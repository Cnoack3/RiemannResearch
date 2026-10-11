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
command -v flock >/dev/null || { echo "util-linux flock is required." >&2; exit 2; }
time_bin="${RBE_TIME_BIN:-/usr/bin/time}"
[[ -x "$time_bin" ]] || { echo "GNU time is required; set RBE_TIME_BIN if it is installed elsewhere." >&2; exit 2; }

diag_root="${RBE_DIAGNOSTICS_DIR:-${XDG_CACHE_HOME:-$HOME/.cache}/riemann-rbe-diagnostics}"
mkdir -p "$diag_root"
diag_root="$(cd "$diag_root" && pwd -P)"
# Serialize this private benchmark root. Close this descriptor in child
# processes so an idle Bazel JVM cannot keep the harness lock alive.
exec {benchmark_lock_fd}> "$diag_root/benchmark.lock"
if ! flock -n "$benchmark_lock_fd"; then
  echo "Another benchmark is using $diag_root; wait for it to finish." >&2
  exit 2
fi
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
    jobs="${RBE_BENCH_JOBS:-8}"
    flags=(--config=buildbuddy-benchmark --jobs="$jobs")
    ;;
esac
# Keep timing/cache summaries in the captured log even when normal builds are
# quiet. These UI options do not change action cache keys.
flags+=(--ui_event_filters=+info --color=no --curses=no --noshow_progress)
flags+=(--profile="$report_dir/profile.gz")
if [[ "$mode" != analysis ]]; then
  flags+=(--execution_log_compact_file="$report_dir/execution.log")
fi

# The Bazel client delegates work to a persistent JVM. GNU time alone does
# not measure that JVM's memory. Sample its PID separately when available.
sampler_pid=""
owned_cache_base=""
server_pid=""
cleanup_sampler() {
  if [[ -n "$sampler_pid" ]]; then
    kill "$sampler_pid" 2>/dev/null || true
    wait "$sampler_pid" 2>/dev/null || true
    sampler_pid=""
  fi
}
# shutdown is a server control command, never a cache clean. Refuse to wait
# behind another active command, including commands outside this harness.
bazel_control() (
  exec {benchmark_lock_fd}>&-
  timeout --signal=INT --kill-after=5s 30s "$bazel_bin" "$@"
)
valid_benchmark_base() {
  local base="$1" name
  [[ ! -L "$base" && ! -L "$base/server" && ! -L "$base/server/server.pid.txt" ]] || return 1
  [[ "$base" != "$diag_root/client" ]] || return 0
  [[ "$base" == "$diag_root/"* ]] || return 1
  name="${base#"$diag_root/"}"
  [[ "$name" =~ ^cache-check-[0-9]{8}T[0-9]{6}Z-[0-9]+$ ]]
}
recorded_benchmark_base() {
  awk '/^output_base=/ {count++; base=substr($0, 13)} END {
    if (count == 1) print base
  }' "$1/run.txt"
}
shutdown_benchmark_base() {
  local base="$1" expected_pid="${2:-}" status
  valid_benchmark_base "$base" || { echo "Unsafe benchmark server path: $base" >&2; return 1; }
  if [[ ! "$expected_pid" =~ ^[1-9][0-9]*$ && -f "$base/server/server.pid.txt" ]]; then
    expected_pid="$(cat "$base/server/server.pid.txt")"
  fi
  printf 'Stopping benchmark server: %s (recorded PID %s)\n' "$base" "${expected_pid:-unavailable}"
  if bazel_control --noblock_for_lock --output_base="$base" shutdown; then
    if [[ "$expected_pid" =~ ^[1-9][0-9]*$ ]] && kill -0 "$expected_pid" 2>/dev/null; then
      echo "Recorded server PID $expected_pid is still alive after shutdown." >&2
      return 1
    fi
  else
    status="$?"
    echo "Benchmark server shutdown failed with exit $status." >&2
    return 1
  fi
}
cleanup_on_exit() {
  local original_status="$?"
  set +e
  cleanup_sampler
  # Signal exits also mark this harness run complete; an active Bazel command
  # is still protected by --noblock_for_lock on the subsequent shutdown.
  if [[ -f "$report_dir/run.txt" && ! -f "$report_dir/exit-code.txt" ]]; then
    printf '%s\n' "$original_status" > "$report_dir/exit-code.txt"
  fi
  if [[ -n "$owned_cache_base" ]]; then
    if shutdown_benchmark_base "$owned_cache_base" "$server_pid" \
        > "$report_dir/server-shutdown.log" 2>&1; then
      printf '%s\n' stopped > "$report_dir/server-cleanup.txt"
    else
      printf '%s\n' failed > "$report_dir/server-cleanup.txt"
      echo "Warning: cache-only JVM cleanup failed; build exit $original_status is preserved. See $report_dir/server-shutdown.log." >&2
    fi
  fi
  exit "$original_status"
}
trap cleanup_on_exit EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

git rev-parse HEAD > "$report_dir/commit.txt"
git status --porcelain > "$report_dir/git-status.txt"
printf '%s\n' "mode=$mode" "target=$target" "jobs=$jobs" "output_base=$output_base" "timeout=$time_limit" > "$report_dir/run.txt"
if [[ "$mode" == cache-only ]]; then
  declare -A live_current_bases=()
  declare -A completed_bases=()
  # Only completed harness reports can authorize stopping an old server.
  # An incomplete live report protects its base even if an older completed
  # report names the same shared client.
  for previous_report in "$diag_root"/*; do
    [[ -d "$previous_report" && ! -L "$previous_report" ]] || continue
    previous_name="${previous_report##*/}"
    [[ "$previous_name" =~ ^(analysis|smoke|repeat|cache-only|parallel)-[0-9]{8}T[0-9]{6}Z-[0-9]+$ ]] || continue
    [[ -f "$previous_report/run.txt" && -f "$previous_report/server-pid.txt" ]] || continue
    previous_base="$(recorded_benchmark_base "$previous_report")"
    valid_benchmark_base "$previous_base" || continue
    previous_pid="$(cat "$previous_report/server-pid.txt")"
    current_pid=""
    [[ ! -f "$previous_base/server/server.pid.txt" ]] || current_pid="$(cat "$previous_base/server/server.pid.txt")"
    recorded_live=false
    current_live=false
    if [[ "$previous_pid" =~ ^[1-9][0-9]*$ ]] && kill -0 "$previous_pid" 2>/dev/null; then recorded_live=true; fi
    if [[ "$current_pid" =~ ^[1-9][0-9]*$ ]] && kill -0 "$current_pid" 2>/dev/null; then current_live=true; fi
    [[ "$recorded_live" == true || "$current_live" == true ]] || continue
    if [[ "$recorded_live" == true && "$current_live" != true ]]; then
      echo "Cannot verify the recorded benchmark server at $previous_base against its current server PID file. Refusing to stop it or start another cache-only JVM." >&2
      exit 2
    fi
    live_current_bases["$previous_base"]="$current_pid"
    # A stale completed report for a dead earlier JVM is not proof for the
    # current JVM; a later report may supply the matching completed record.
    [[ "$current_pid" == "$previous_pid" ]] || continue
    previous_exit=""
    [[ ! -f "$previous_report/exit-code.txt" ]] || previous_exit="$(cat "$previous_report/exit-code.txt")"
    if [[ ! "$previous_exit" =~ ^[0-9]+$ ]]; then
      echo "A live benchmark server has an incomplete report: $previous_report. Refusing to start another cache-only JVM." >&2
      exit 2
    fi
    completed_bases["$previous_base"]="$previous_pid"
  done
  for previous_base in "${!live_current_bases[@]}"; do
    if [[ "${completed_bases["$previous_base"]:-}" != "${live_current_bases["$previous_base"]}" ]]; then
      echo "No completed benchmark report matches the current server PID at $previous_base. Refusing to stop it or start another cache-only JVM." >&2
      exit 2
    fi
  done
  for previous_base in "${!completed_bases[@]}"; do
    if ! shutdown_benchmark_base "$previous_base" "${completed_bases["$previous_base"]}" \
        >> "$report_dir/preflight-shutdown.log" 2>&1; then
      echo "Could not stop a completed benchmark server at $previous_base. No new cache-only build was started. See $report_dir/preflight-shutdown.log." >&2
      exit 2
    fi
  done
  # This base is unique to this run; the trap may stop only this newly owned
  # server after the build, preserving all output-base and repository caches.
  owned_cache_base="$output_base"
fi
if command -v ps >/dev/null && server_pid="$(bazel_control \
    --output_base="$output_base" info server_pid 2> "$report_dir/server-info.log")"; then
  if [[ "$server_pid" =~ ^[0-9]+$ ]]; then
    printf '%s\n' "$server_pid" > "$report_dir/server-pid.txt"
    printf '%s\n' 'timestamp_utc pid cpu_lifetime_pct rss_kib vsz_kib elapsed' > "$report_dir/server-resources.txt"
    (
      exec {benchmark_lock_fd}>&-
      while kill -0 "$server_pid" 2>/dev/null; do
        printf '%s ' "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
        ps -p "$server_pid" -o pid=,pcpu=,rss=,vsz=,etime= || break
        sleep 2
      done
    ) >> "$report_dir/server-resources.txt" &
    sampler_pid="$!"
  fi
fi

printf 'Running %s on %s (timeout %s). Collecting results; logs stay local.\n' "$mode" "$target" "$time_limit"
printf 'Command:' > "$report_dir/command.txt"
printf ' %q' "$bazel_bin" --output_base="$output_base" build "${flags[@]}" "$target" >> "$report_dir/command.txt"
printf '\n' >> "$report_dir/command.txt"

set +e
(
exec {benchmark_lock_fd}>&-
LC_ALL=C "$time_bin" -v -o "$report_dir/resources.txt" \
  timeout --signal=INT --kill-after=30s "$time_limit" \
  "$bazel_bin" --output_base="$output_base" build "${flags[@]}" "$target" \
) > "$report_dir/build.log" 2>&1
build_status="$?"
set -e
cleanup_sampler
printf '%s\n' "$build_status" > "$report_dir/exit-code.txt"

if [[ -s "$report_dir/profile.gz" ]]; then
  # Bazel 9.2 has no analyze-profile. Keep the raw trace without starting
  # another Bazel command or loading a potentially large profile into memory.
  cat > "$report_dir/profile-viewing.txt" <<EOF
Profile: $report_dir/profile.gz
Open chrome://tracing in Chrome, click Load, and select profile.gz.
Inspect runAnalysisPhase, remote setup/cache events, and Garbage Collector.
Build result: exit-code.txt; build output: build.log.
A profile from an interrupted build or OOM may be incomplete.
Reference: https://bazel.build/versions/9.2.0/advanced/performance/json-trace-profile
EOF
fi

if [[ "$build_status" != 0 ]]; then
  printf '\nLast build diagnostics:\n' >&2
  tail -n 40 "$report_dir/build.log" >&2
fi
if [[ "$mode" == cache-only && "$build_status" != 0 ]]; then
  echo "Cache-only check did not pass. A cache miss fails instead of dispatching remote compilation."
fi

# The console summary is the normal handoff: no profile/log attachments needed.
wall_time="unavailable"
if [[ -f "$report_dir/resources.txt" ]]; then
  wall_time="$(awk '/Elapsed \(wall clock\) time/ {sub(/^.*: /, ""); print; exit}' "$report_dir/resources.txt")"
  wall_time="${wall_time:-unavailable}"
fi
server_rss="unavailable (server PID/samples missing)"
if [[ -f "$report_dir/server-resources.txt" ]]; then
  server_rss="$(LC_ALL=C awk 'NR > 1 && NF >= 6 && $4 ~ /^[0-9]+$/ {
    count++; if ($4 > peak) peak = $4
  } END {
    if (count) printf "%.2f GiB (%d samples, every 2s)", peak / 1048576, count;
    else printf "unavailable (no samples)"
  }' "$report_dir/server-resources.txt")"
fi
invocation="$(awk 'match($0, /https:\/\/app\.buildbuddy\.io\/invocation\/[[:alnum:]-]+/) {
  url = substr($0, RSTART, RLENGTH)
} END {print url}' "$report_dir/build.log")"
invocation="${invocation:-unavailable}"
revision="$(cat "$report_dir/commit.txt")"
tree_state="clean"
[[ ! -s "$report_dir/git-status.txt" ]] || tree_state="dirty"
result="PASS"
[[ "$build_status" == 0 ]] || result="FAIL"
[[ "$build_status" != 124 ]] || result="TIMEOUT"
profile_state="missing"
if [[ -s "$report_dir/profile.gz" ]]; then
  profile_state="saved locally"
  [[ "$build_status" == 0 ]] || profile_state+=" (may be incomplete)"
fi
{
  printf '\n--- RBE summary: paste this block ---\n'
  printf 'Mode: %s\nTarget: %s\nRevision: %.12s (%s)\n' "$mode" "$target" "$revision" "$tree_state"
  printf 'Jobs: %s\n' "$jobs"
  printf 'Result: %s (exit %s)\nBuild wall time: %s\n' "$result" "$build_status" "$wall_time"
  printf 'JVM peak sampled RSS: %s\n' "$server_rss"
  awk '/^INFO: (Analyzed |Elapsed time: |[0-9]+ processes:)/ {
    sub(/^INFO: /, ""); print
  }' "$report_dir/build.log"
  if [[ "$build_status" != 0 ]]; then
    awk '/(^ERROR:|FATAL:|[[:space:]]error:|OutOfMemoryError|UndeliverableException)/ {
      print "Diagnostic: " substr($0, 1, 400); if (++count == 3) exit
    }' "$report_dir/build.log"
  fi
  printf 'BuildBuddy: %s\nProfile: %s\n' "$invocation" "$profile_state"
  printf '%s\n' '--- End summary ---'
} | tee "$report_dir/summary.txt"
printf '\nDetails kept locally: %s\n' "$report_dir"
exit "$build_status"
