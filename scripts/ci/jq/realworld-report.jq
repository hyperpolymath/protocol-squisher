{
  generated_at_utc: $generated_at,
  protocol_squisher_bin: $bin,
  roots: $roots,
  strict_json_schema: $strict_json_schema,
  thresholds: {
    min_success: $min_success,
    max_files: $max_files
  },
  totals: {
    candidates_discovered: $total_candidates,
    attempted: $attempted,
    successful_analyses: $successful,
    parse_failures: $parse_failures,
    invariant_violations: $invariant_violations
  },
  per_format: $per_format,
  gates: {
    real_world_target_met: ($successful >= $min_success),
    invariant_target_met: ($invariant_violations == 0)
  }
}
