{
  generated_at_utc: $generated_at,
  git_commit: $git_commit,
  logs_dir: $logs_dir,
  abi_policy: {
    status: $abi_status
  },
  panic_assail: {
    tool: $panic_bin,
    baseline: {
      weak_points: $baseline_weak_points,
      unwrap_calls: $baseline_unwrap_calls,
      panic_sites: $baseline_panic_sites
    },
    current: {
      weak_points: $current_weak_points,
      unwrap_calls: $current_unwrap_calls,
      panic_sites: $current_panic_sites
    }
  },
  podman: {
    status: $podman_status,
    failure_reason: $podman_failure_reason,
    steps: $podman_steps
  },
  realworld_corpus: {
    status: $realworld_status,
    failure_reason: $realworld_failure_reason,
    report_path: $realworld_report,
    totals: $realworld_totals
  }
}
