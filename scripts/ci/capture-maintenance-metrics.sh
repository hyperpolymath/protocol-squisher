#!/usr/bin/env bash
# SPDX-License-Identifier: PMPL-1.0-or-later

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
jq_dir="${repo_root}/scripts/ci/jq"
with_podman=false
with_realworld=false
output_path=""
logs_dir=""
panic_attack_bin="${PANIC_ATTACK_BIN:-}"
baseline_file="${repo_root}/scripts/ci/panic-assail-baseline.json"
timestamp_utc="$(date -u +%Y%m%dT%H%M%SZ)"
realworld_min_success=100
realworld_max_files=220

usage() {
    cat <<USAGE
usage: $0 [--with-podman] [--with-realworld] [--output <path>] [--logs-dir <path>] [--panic-bin <path>]

Capture maintenance metrics as JSON.

Options:
  --with-podman       Include timed podman maintenance steps
  --with-realworld    Include real-world schema gate (>=100 success, 0 invariant violations)
  --output <path>     Output JSON path (default: /tmp/protocol-squisher-maint-<timestamp>.json)
  --logs-dir <path>   Directory for step logs (default: /tmp/protocol-squisher-maint-logs-<timestamp>)
  --panic-bin <path>  panic-attack binary path
  --realworld-min-success <n>   Override minimum successful analyses for real-world gate
  --realworld-max-files <n>     Override max attempted files for real-world gate
USAGE
}

while [[ $# -gt 0 ]]; do
    case "$1" in
        --with-podman)
            with_podman=true
            shift
            ;;
        --with-realworld)
            with_realworld=true
            shift
            ;;
        --output)
            output_path="${2:-}"
            shift 2
            ;;
        --logs-dir)
            logs_dir="${2:-}"
            shift 2
            ;;
        --panic-bin)
            panic_attack_bin="${2:-}"
            shift 2
            ;;
        --realworld-min-success)
            realworld_min_success="${2:-}"
            shift 2
            ;;
        --realworld-max-files)
            realworld_max_files="${2:-}"
            shift 2
            ;;
        -h|--help)
            usage
            exit 0
            ;;
        *)
            echo "error: unknown argument: $1" >&2
            usage >&2
            exit 2
            ;;
    esac
done

if [[ -z "${panic_attack_bin}" && -x /var/mnt/eclipse/repos/panic-attacker/target/release/panic-attack ]]; then
    panic_attack_bin=/var/mnt/eclipse/repos/panic-attacker/target/release/panic-attack
fi
if [[ -z "${panic_attack_bin}" ]]; then
    panic_attack_bin=panic-attack
fi

if ! command -v "${panic_attack_bin}" >/dev/null 2>&1; then
    echo "error: panic-attack binary not found (set PANIC_ATTACK_BIN or use --panic-bin)." >&2
    exit 127
fi
if ! command -v jq >/dev/null 2>&1; then
    echo "error: jq is required." >&2
    exit 127
fi
if [[ ! -f "${jq_dir}/append-podman-step.jq" || ! -f "${jq_dir}/capture-maintenance-report.jq" ]]; then
    echo "error: jq filters missing in ${jq_dir}" >&2
    exit 127
fi
if ! command -v git >/dev/null 2>&1; then
    echo "error: git is required." >&2
    exit 127
fi
if ! [[ "${realworld_min_success}" =~ ^[0-9]+$ ]]; then
    echo "error: --realworld-min-success must be an integer." >&2
    exit 2
fi
if ! [[ "${realworld_max_files}" =~ ^[0-9]+$ ]] || [[ "${realworld_max_files}" -le 0 ]]; then
    echo "error: --realworld-max-files must be a positive integer." >&2
    exit 2
fi

if [[ -z "${output_path}" ]]; then
    output_path="/tmp/protocol-squisher-maint-${timestamp_utc}.json"
fi
if [[ -z "${logs_dir}" ]]; then
    logs_dir="/tmp/protocol-squisher-maint-logs-${timestamp_utc}"
fi

tmp_dir="$(mktemp -d)"
cleanup() {
    rm -rf "${tmp_dir}"
}
trap cleanup EXIT

mkdir -p "${logs_dir}"

abi_status="pass"
abi_log="${logs_dir}/abi-policy.log"
if ! "${repo_root}/scripts/ci/check-abi-policy.sh" >"${abi_log}" 2>&1; then
    abi_status="fail"
fi

source_tree="${tmp_dir}/source"
assail_report="${tmp_dir}/assail.json"
panic_stderr="${tmp_dir}/panic-assail.stderr"

"${repo_root}/scripts/ci/build-panic-assail-source.sh" "${source_tree}" >/dev/null
if ! "${panic_attack_bin}" assail "${source_tree}" --output "${assail_report}" >/dev/null 2>"${panic_stderr}"; then
    cat "${panic_stderr}" >&2
    exit 1
fi

current_weak_points="$(jq -r '.weak_points | length' "${assail_report}")"
current_unwrap_calls="$(jq -r '.statistics.unwrap_calls' "${assail_report}")"
current_panic_sites="$(jq -r '.statistics.panic_sites' "${assail_report}")"

baseline_weak_points=0
baseline_unwrap_calls=0
baseline_panic_sites=0
if [[ -f "${baseline_file}" ]]; then
    baseline_weak_points="$(jq -r '.metrics.weak_points // 0' "${baseline_file}")"
    baseline_unwrap_calls="$(jq -r '.metrics.unwrap_calls // 0' "${baseline_file}")"
    baseline_panic_sites="$(jq -r '.metrics.panic_sites // 0' "${baseline_file}")"
fi

podman_status="skipped"
podman_failure_reason=""
podman_steps='[]'
realworld_status="skipped"
realworld_failure_reason=""
realworld_report=""
realworld_totals='{}'

append_podman_step() {
    local name="$1"
    local status="$2"
    local seconds="$3"
    local log_path="$4"
    podman_steps="$(jq -c \
        --arg name "${name}" \
        --arg status "${status}" \
        --argjson seconds "${seconds}" \
        --arg log "${log_path}" \
        -f "${jq_dir}/append-podman-step.jq" \
        <<<"${podman_steps}")"
}

run_timed_step() {
    local name="$1"
    shift
    local start end seconds log_path status

    log_path="${logs_dir}/${name}.log"
    start="$(date +%s)"
    if "$@" >"${log_path}" 2>&1; then
        status="pass"
    else
        status="fail"
    fi
    end="$(date +%s)"
    seconds="$((end - start))"

    append_podman_step "${name}" "${status}" "${seconds}" "${log_path}"
    [[ "${status}" == "pass" ]]
}

if [[ "${with_podman}" == true ]]; then
    podman_status="pass"

    if ! command -v podman >/dev/null 2>&1; then
        podman_status="fail"
        podman_failure_reason="podman binary not found in PATH"
        preflight_log="${logs_dir}/podman_prereq.log"
        printf '%s\n' "${podman_failure_reason}" >"${preflight_log}"
        append_podman_step "podman_prereq" "fail" 0 "${preflight_log}"
    fi
    if [[ "${podman_status}" == "pass" ]] && ! podman compose version >/dev/null 2>&1 && ! command -v podman-compose >/dev/null 2>&1; then
        podman_status="fail"
        podman_failure_reason="neither podman compose plugin nor podman-compose binary is available"
        preflight_log="${logs_dir}/podman_prereq.log"
        printf '%s\n' "${podman_failure_reason}" >"${preflight_log}"
        append_podman_step "podman_prereq" "fail" 0 "${preflight_log}"
    fi
    if [[ "${podman_status}" == "pass" ]] && ! run_timed_step "install_ephapax_cli" "${repo_root}/scripts/podman-dev.sh" install-ephapax-cli; then
        podman_status="fail"
        podman_failure_reason="install_ephapax_cli failed (see install_ephapax_cli.log)"
    fi
    if [[ "${podman_status}" == "pass" ]] && ! run_timed_step "podman_test_verified_real" "${repo_root}/scripts/podman-dev.sh" test-verified-real; then
        podman_status="fail"
        podman_failure_reason="podman_test_verified_real failed (see podman_test_verified_real.log)"
    fi
    if [[ "${podman_status}" == "pass" ]] && ! run_timed_step "podman_bench_verified_real" "${repo_root}/scripts/podman-dev.sh" bench-verified-real; then
        podman_status="fail"
        podman_failure_reason="podman_bench_verified_real failed (see podman_bench_verified_real.log)"
    fi
    if [[ "${podman_status}" == "pass" ]] && ! run_timed_step "backend_verified_real" "${repo_root}/scripts/podman-dev.sh" backend-verified-real; then
        podman_status="fail"
        podman_failure_reason="backend_verified_real failed (see backend_verified_real.log)"
    fi
    if [[ "${podman_status}" == "pass" ]] && ! run_timed_step "compile_smoke_verified_real" "${repo_root}/scripts/podman-dev.sh" compile-smoke-verified-real; then
        podman_status="fail"
        podman_failure_reason="compile_smoke_verified_real failed (see compile_smoke_verified_real.log)"
    fi
fi

if [[ "${with_realworld}" == true ]]; then
    realworld_report="${logs_dir}/realworld-report.json"
    realworld_log="${logs_dir}/realworld-gate.log"

    if "${repo_root}/scripts/ci/validate-realworld-corpus.sh" \
        --min-success "${realworld_min_success}" \
        --max-files "${realworld_max_files}" \
        --output "${realworld_report}" >"${realworld_log}" 2>&1; then
        realworld_status="pass"
    else
        realworld_status="fail"
        realworld_failure_reason="validate-realworld-corpus.sh failed (see realworld-gate.log)"
    fi

    if [[ -f "${realworld_report}" ]] && jq -e '.totals' "${realworld_report}" >/dev/null 2>&1; then
        realworld_totals="$(jq -c '.totals' "${realworld_report}")"
    fi
fi

git_commit="$(git -C "${repo_root}" rev-parse HEAD)"
generated_at="$(date -u +%Y-%m-%dT%H:%M:%SZ)"

mkdir -p "$(dirname "${output_path}")"

jq -n \
    --arg generated_at "${generated_at}" \
    --arg git_commit "${git_commit}" \
    --arg panic_bin "${panic_attack_bin}" \
    --arg logs_dir "${logs_dir}" \
    --arg abi_status "${abi_status}" \
    --arg podman_status "${podman_status}" \
    --arg podman_failure_reason "${podman_failure_reason}" \
    --arg realworld_status "${realworld_status}" \
    --arg realworld_failure_reason "${realworld_failure_reason}" \
    --arg realworld_report "${realworld_report}" \
    --argjson baseline_weak_points "${baseline_weak_points}" \
    --argjson baseline_unwrap_calls "${baseline_unwrap_calls}" \
    --argjson baseline_panic_sites "${baseline_panic_sites}" \
    --argjson current_weak_points "${current_weak_points}" \
    --argjson current_unwrap_calls "${current_unwrap_calls}" \
    --argjson current_panic_sites "${current_panic_sites}" \
    --argjson podman_steps "${podman_steps}" \
    --argjson realworld_totals "${realworld_totals}" \
    -f "${jq_dir}/capture-maintenance-report.jq" >"${output_path}"

echo "wrote metrics: ${output_path}"
echo "logs dir: ${logs_dir}"

# Non-zero if any gate failed.
if [[ "${abi_status}" != "pass" || "${podman_status}" == "fail" || "${realworld_status}" == "fail" ]]; then
    exit 1
fi
