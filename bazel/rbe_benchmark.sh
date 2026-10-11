#!/usr/bin/env bash
# Bounded Bazel/BuildBuddy diagnostics. Run from the repository root.
set -euo pipefail

mode="${1:-}"
case "$mode" in
  analysis|smoke|repeat|cache-only|parallel) ;;
  *) echo "Usage: bash bazel/rbe_benchmark.sh {analysis|smoke|repeat|cache-only|parallel} [target]" >&2; exit 2 ;;
esac

if [[ ! -f MODULE.bazel || ! -f .bazelrc ]]; then
  echo "Run this script from the RiemannResearch repository root." >&2
  exit 2
fi

bazel_bin="${BAZEL_BIN:-bazel}"
command -v "$bazel_bin" >/dev/null || { echo "Bazel is unavailable: $bazel_bin" >&2; exit 2; }
command -v timeout >/dev/null || { echo "GNU timeout is required." >&2; exit 2; }
time_bin="${RBE_TIME_BIN:-/usr/bin/time}"
[[ -x "$time_bin" ]] || { echo "GNU time is required; set RBE_TIME_BIN if it is installed elsewhere." >&2; exit 2; }

diag_root="${RBE_DIAGNOSTICS_DIR:-${XDG_CACHE_HOME:-$HOME/.cache}/riemann-rbe-diagnostics}"
mkdir -p "$diag_root"
diag_root="$(cd "$diag_root" && pwd)"
run_id="$(date -u +%Y%m%dT%H%M%SZ)-$$"
report_dir="$diag_root/$mode-$run_id"
mkdir -p "$report_dir"
output_base="$diag_root/client"
target="${2:-//:smoke}"
jobs="${RBE_BENCH_JOBS:-2}"
time_limit="${RBE_BENCH_TIMEOUT:-10m}"
case "$jobs" in
  ''|*[!0-9]*) echo "RBE_BENCH_JOBS must be an integer from 1 to 80." >&2; exit 2 ;;
esac
if (( 10#$jobs < 1 || 10#$jobs > 80 )); then
  echo "RBE_BENCH_JOBS must be an integer from 1 to 80." >&2
  exit 2
fi

flags=(--config=buildbuddy --jobs="$jobs")
case "$mode" in
  analysis)
    target="${2:-//:RiemannResearch}"
    flags+=(--nobuild)
    ;;
  cache-only)
    # Fresh local action state; native repository caches still remain shared.
    output_base="$diag_root/cache-check-$run_id"
    flags+=(--experimental_remote_require_cached --noremote_upload_local_results)
    ;;
  parallel)
    flags=(--config=buildbuddy-benchmark --jobs="${RBE_BENCH_JOBS:-8}")
    ;;
esac
flags+=(--profile="$report_dir/profile.gz")
if [[ "$mode" != analysis ]]; then
  flags+=(--execution_log_compact_file="$report_dir/execution.log")
fi

# The Bazel client delegates work to a persistent JVM. GNU time alone does
# not measure that JVM's memory. Sample its PID separately when available.
sampler_pid=""
cleanup_sampler() {
  if [[ -n "$sampler_pid" ]]; then
    kill "$sampler_pid" 2>/dev/null || true
    wait "$sampler_pid" 2>/dev/null || true
    sampler_pid=""
  fi
}
trap cleanup_sampler EXIT
if command -v ps >/dev/null && server_pid="$(timeout --signal=INT --kill-after=10s 30s \
    "$bazel_bin" --output_base="$output_base" info server_pid 2> "$report_dir/server-info.log")"; then
  if [[ "$server_pid" =~ ^[0-9]+$ ]]; then
    printf '%s\n' "$server_pid" > "$report_dir/server-pid.txt"
    printf '%s\n' 'timestamp_utc pid cpu_lifetime_pct rss_kib vsz_kib elapsed' > "$report_dir/server-resources.txt"
    (
      while kill -0 "$server_pid" 2>/dev/null; do
        printf '%s ' "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
        ps -p "$server_pid" -o pid=,pcpu=,rss=,vsz=,etime= || break
        sleep 2
      done
    ) >> "$report_dir/server-resources.txt" &
    sampler_pid="$!"
  fi
fi

git rev-parse HEAD > "$report_dir/commit.txt"
git status --porcelain > "$report_dir/git-status.txt"
printf '%s\n' "mode=$mode" "target=$target" "output_base=$output_base" "timeout=$time_limit" > "$report_dir/run.txt"
printf 'Reports: %s\n' "$report_dir"
printf 'Running:'
printf ' %q' "$bazel_bin" --output_base="$output_base" build "${flags[@]}" "$target"
printf '\n'

set +e
"$time_bin" -v -o "$report_dir/resources.txt" \
  timeout --signal=INT --kill-after=30s "$time_limit" \
  "$bazel_bin" --output_base="$output_base" build "${flags[@]}" "$target" \
  2>&1 | tee "$report_dir/build.log"
build_status="${PIPESTATUS[0]}"
set -e
cleanup_sampler
printf '%s\n' "$build_status" > "$report_dir/exit-code.txt"

if [[ -f "$report_dir/profile.gz" ]]; then
  timeout --signal=INT --kill-after=30s 2m \
    "$bazel_bin" --output_base="$output_base" analyze-profile "$report_dir/profile.gz" \
    > "$report_dir/profile-summary.txt" 2>&1 || true
fi

if [[ "$mode" == cache-only && "$build_status" != 0 ]]; then
  echo "Cache-only check did not pass. A cache miss fails instead of dispatching remote compilation."
fi
printf 'Exit code: %s\nReports: %s\n' "$build_status" "$report_dir"
exit "$build_status"
