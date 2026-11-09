# Bazel-backed Lean verification

The experimental default is `bazel build --config=buildbuddy`. The existing
repository BuildBuddy settings, resource limits, and credentials are reused.
No automatic fallback to Lake is performed.

## Selection and coverage

`agent_workspace_run_code`, `agent_workspace_check_file`, `lean_build`, and
`agent_workspace_checkpoint` accept an optional `backend` argument:

- Omitted or `"bazel"`: use Bazel (unless the operator changed the default).
- `"lake"`: explicitly use the previous Lake implementation for this job.
- `LEAN_VERIFICATION_BACKEND=lake` in the service environment: restore the
  legacy default after a service restart. Use `bazel` to switch back.

Each submitted job records its backend as part of its request identity. Jobs
created by the old server retain their Lake semantics. Editor/LSP diagnostics,
tactic attempts, and axiom inspection remain exploratory; queued compilation
and checkpoint results are acceptance evidence.

The full target is `//:RiemannResearch`. A file in a source directory has target
`//RiemannResearch/<directory>:<basename>`; the root module itself has target
`//:RiemannResearch_module`. Ephemeral snippets receive unique temporary source
packages in `RiemannResearch/`, use the same Bazel rules and sorry audit, and are
removed after the job finishes. Bazel handles its own artifacts; native Lake
cache snapshots are not restored or published for Bazel verification.

After patches and before verification, the server generates missing
`BUILD.bazel` files for Lean source directories and all intermediate parents.
Existing package files are preserved and must call `lean_modules()`; empty
package files are rejected. Generated files are part of the checkpoint source
tree. Direct edits can use:

```bash
python3 tools/bazel_verification.py --fix
python3 tools/bazel_verification.py --check
```

Build-file changes trigger full checkpoint validation. A failed build, a changed
source tree during validation, or failed integration blocks publication. The
per-workspace operation lease and serialized publication are retained. Independent
Bazel workspaces bypass the legacy global queue and run concurrently by default.

## Verification concurrency

- `LEAN_BAZEL_JOB_WORKERS=0` (the default): no global Bazel job cap.
- A positive `LEAN_BAZEL_JOB_WORKERS` sets an optional cap shared by cooperating
  MCP processes using the same state directory; configure them consistently.
- `LEAN_JOB_WORKERS` applies only to the legacy Lake queue (default 1, range 1–4).
- Each workspace allows one active job. Duplicate pending requests reuse that
  job; competing requests or mutations are rejected until it finishes. Give
  each parallel agent a separate workspace. Publication remains serialized.

Job responses report `worker_count: null` for uncapped Bazel execution and
`same_workspace_limit: 1`. A configured cap reports its numeric value.
This controls concurrent verification jobs, not Bazel action parallelism.
BuildBuddy flags, credentials, and remote resource settings are unchanged.
RBE runs compiler actions remotely; local Bazel servers still perform analysis
and consume memory, so set an optional cap if measurements warrant one.

Admission uses a separate lock and pending-job index for each workspace.
Submitting a job or checking whether a workspace is busy does not scan completed
job history. A process-start recovery scan indexes legacy pending records and
marks jobs whose owner exited as interrupted; it never replays them. Keep
cooperating MCP processes on the same server version when upgrading.
Malformed job records block recovery/admission instead of being treated as idle;
the original records remain available for diagnosis.

Submission responses include `admission` timings for workspace-lock waiting,
pending-record lookup, persistence, dispatch, and total admission time, plus
`records_examined`. Job records retain `admission_started_at` and lookup/lock
measurements. These measurements start inside the manager's admission method;
they exclude earlier request validation and connector/network time. The existing
`submitted_at` timestamp still marks job creation, not initial request arrival.

## Host resource policy

Remote execution still leaves analysis, input preparation, dependency bootstrap,
and editor processes on the MCP host. Each workspace has its own JVM; the 8 GiB
Java heap setting is per JVM, not a total memory budget.

The approximately 14 GiB WSL host experienced global OOM kills of a local Lean
process with about 10.1 GiB resident memory and a Java process with about 5.3 GiB.
The process logs do not identify whether that Lean process was an editor worker
or a dependency-bootstrap compiler. A later service start does not turn those
interrupted jobs into successful verifications.

A guarded full-project trial with an 8 GiB `MemoryHigh` reached about 8.11 GiB
of cgroup usage and about 99% full memory pressure, with repeated `high` events
and no OOM kills. That soft limit forced sustained reclaim during analysis.
A later three-workspace invalidation trial also reached about 97% full memory
pressure with a 9 GiB soft limit and a 1 GiB service swap cap. The operator then
raised the live limits to 11 GiB high and 12 GiB max. The profile now matches
those RAM limits and removes the separate service swap cap. These settings
still need workload measurement and do not guarantee arbitrary concurrency.

Install `bazel/lean-tunnel.resources.conf` to apply an aggregate service budget:

| Setting | Value | Purpose |
| --- | --- | --- |
| `MemoryHigh` | 11 GiB | Reclaim/throttle memory above the preferred budget |
| `MemoryMax` | 12 GiB | Hard limit for the whole service and its descendants |
| `MemorySwapMax` | infinity | Allow available host swap; WSL still bounds total capacity |
| `OOMPolicy` | stop | Stop the unit if one of its processes is OOM-killed |
| `LEAN_WORKSPACE_THREADS`, `LEAN_LAKE_BUILD_THREADS` | 2 | Bound local Lean thread pools |
| `LEAN_MAX_SHARED_CLIENTS` | 2 | Bound retained editor clients |
| `LEAN_BAZEL_JOB_WORKERS` | 0 | Preserve concurrent independent workspaces |

A BuildBuddy build retains its 80-action limit. One job per workspace and
serialized publication still apply. A large local task can fail at the memory
limit; this policy does not prove that arbitrary concurrent builds fit in RAM.
It does not cover manually launched builds outside the service's control group.
Do not run heavy manual jobs alongside the recovery test.

Once jobs are idle, run from the server checkout:

```bash
git pull --ff-only
sudo install -Dm644 bazel/lean-tunnel.resources.conf /etc/systemd/system/lean-tunnel.service.d/90-bazel-resources.conf
sudo systemctl daemon-reload
sudo systemctl restart lean-tunnel.service
systemctl show lean-tunnel.service -p MemoryHigh -p MemoryMax -p MemorySwapMax -p OOMPolicy
```

Use `start` instead of `restart` if the service was deliberately stopped after
an OOM. Verify the kernel cgroup limits before resuming stress tests:

```bash
lean_cgroup=$(systemctl show lean-tunnel.service -p ControlGroup --value)
cat "/sys/fs/cgroup${lean_cgroup}/memory.high" "/sys/fs/cgroup${lean_cgroup}/memory.max" "/sys/fs/cgroup${lean_cgroup}/memory.swap.max"
```

Expected values are `11811160064`, `12884901888`, and `max`, respectively.
The RAM limits must be finite; `max` is intentional only for the service swap
limit. Missing controller files do not establish that the guard is active. The drop-in preserves service commands and credentials. Other drop-ins
may override it, so verify effective settings rather than only reading the file.

To apply the current policy during an active build without restarting the
service:

```bash
sudo systemctl set-property --runtime lean-tunnel.service \
  MemoryHigh=11G MemoryMax=12G MemorySwapMax=infinity
```

The runtime override lasts until reboot; install the updated drop-in for
persistence. `MemorySwapMax=infinity` removes only the unit-specific swap limit;
it does not allocate additional swap and does not remove the RAM limits.

### WSL swap capacity

For this host, 16 GiB of WSL swap is a reasonable initial capacity for the
multi-workspace experiments. In Windows PowerShell, open the existing global
configuration:

```powershell
notepad "$env:USERPROFILE\.wslconfig"
```

Set `swap=16GB` inside its existing `[wsl2]` section, preserving other settings.
If the file does not exist, create it with:

```ini
[wsl2]
swap=16GB
```

After all verifier jobs have finished, apply the WSL configuration from
PowerShell with `wsl --shutdown`, then reopen Ubuntu. This stops all WSL
distributions, so do not use it during a build. Verify inside Ubuntu:

```bash
free -h
swapon --show
```

The service swap allowance and WSL swap capacity are separate: both must permit
swapping. More swap helps absorb peaks and move cold pages out of RAM; it does
not make disk-backed pages as fast as RAM or eliminate active-working-set
thrashing.

Warm one fresh workspace's dependency setup first. Once that succeeds, run
parallel warm-workspace checks and measure memory and latency. Do not start
several cold Mathlib bootstraps at once during recovery. Never automatically
replay interrupted jobs, particularly publication jobs. Keep the original job
records and source changes.

Bazel's existing two-processor hint, loading threads, batch scheduling, and idle
exit remain in place. They are not a hard aggregate RSS limit. The 8 GiB Java
heap ceiling is unchanged because previous full-project runs used most of it.
New job responses should report `worker_count: null` and `same_workspace_limit: 1`.

Sources: [systemd memory controls](https://www.freedesktop.org/software/systemd/man/latest/systemd.resource-control.html),
[systemd OOM policy](https://www.freedesktop.org/software/systemd/man/latest/systemd.service.html#OOMPolicy=),
[Bazel options](https://bazel.build/versions/9.2.0/reference/command-line-reference),
and [Microsoft WSL configuration](https://learn.microsoft.com/en-us/windows/wsl/wsl-config).

## Idle Bazel servers

The default server idle timeout is 30 minutes (`--max_idle_secs=1800`).
Each command restarts the idle interval. Retaining the server preserves its
in-memory analysis graph for subsequent work in that workspace. Disk and
BuildBuddy compilation caches survive a server shutdown.

The timeout is read when the Bazel server starts. Existing JVMs retain their
previous timeout until they exit. Existing checkouts must pull or sync this
configuration before starting a replacement server.

This is an explicit retention tradeoff. A full-project server has been observed
retaining about 8.5 GiB. The aggregate RAM limits and available host swap still
constrain simultaneous workspaces. Additional swap provides capacity for cold
pages, while repeatedly paging active graphs can slow builds. Pressure-aware
eviction of idle servers is still pending. The existing
`--shutdown_on_low_sys_mem` checks VM-wide memory and is not a substitute for
service-cgroup-aware eviction.

Revert the startup option to 300 for the previous five-minute policy.
The 30-minute setting has been checked as a configuration-only change, but a
live 30-minute retention test has not yet been performed.

## Shared storage

The cache policy lives entirely in the repository's `.bazelrc`. Updated
checkouts use the following per-user locations; older checkouts retain their
own settings until updated.

| Directory under `~/.cache/riemann-bazel` | Purpose |
| --- | --- |
| `repository/` | Shared external-repository downloads |
| `repo-contents/` | Shared completed, reproducible external repositories |
| `disk/` | Local action cache and CAS, including downloaded BuildBuddy blobs |
| `outputs/<workspace-path-hash>/` | Separate mutable build state for each checkout |

Bazel keeps each output base outside the source tree and removes convenience
`bazel-*` symlinks from the checkout. Use `bazel info output_path` or
`bazel info bazel-bin` to locate generated files.

Remote output downloads remain `minimal`. Files downloaded when needed enter
the shared disk cache; absent remote blobs are not fetched eagerly. A disk
action-cache entry can still miss when its referenced blobs are absent, and
Bazel then consults BuildBuddy. This is not a mirror of the entire hosted CAS
and does not eliminate analysis in a fresh workspace.

The disk cache has a **32 GiB soft limit** and **14-day age limit**, with
garbage collection after one idle minute. Completed repository contents use
14-day idle retention. These limits do not cover repository archives,
per-workspace output bases, or native Lake caches.

There are no additional Python storage overrides or workspace-lifecycle cleanup
hooks. Per-workspace output bases have no size limit and are retained until
explicitly cleaned; their actual disk usage has not yet been measured. After a
representative build, inspect one without following links to shared repositories:

```bash
du -h --max-depth=1 "$(bazel info --config=buildbuddy output_base)"
```

Override local paths through the existing `.bazelrc.local` import when needed.
Pulling the configuration applies it to subsequent Bazel invocations; no MCP
service restart is needed for this cache policy. Existing caches at older
locations are not moved or deleted, and the first use of the new root may
repopulate dependencies and analysis state.

Sources: [Bazel 9.2 cache options](https://bazel.build/versions/9.2.0/reference/command-line-reference),
[output layout](https://bazel.build/versions/9.2.0/remote/output-directories),
and [local-first downloads and remote-cache fill](https://github.com/bazelbuild/bazel/blob/9.2.0/src/main/java/com/google/devtools/build/lib/remote/CombinedCache.java).

## Viewing a running build

Bazel 9 defaults `--write_command_log` to false. The repository enables it so
each output base retains `command.log`, containing the current/latest command's
console output. The setting applies to the next invocation; it cannot enable
logging retroactively for a running command and requires no MCP restart.

For the default output-root policy, calculate the log path without starting
another Bazel command:

```bash
lean_workspace=/absolute/project_root/from/agent_workspace_open
lean_output_base="$HOME/.cache/riemann-bazel/outputs/$(printf %s "$(realpath "$lean_workspace")" | md5sum | cut -d' ' -f1)"
tail -n 80 -F "$lean_output_base/command.log"
```

In the same shell (stop `tail` with Ctrl+C first), extract the BuildBuddy link:

```bash
rg -o 'https://app\.buildbuddy\.io/invocation/[A-Za-z0-9-]+' "$lean_output_base/command.log" | head -n 1
```

A custom `--output_base` or `--output_user_root` changes this path.
Do not run `bazel info` to discover it while a build is active: commands share
the output-base lock, and the later info command can replace the command log.
`server/jvm.out` in the same output base is a separate JVM diagnostic log; it
is not a substitute for the build console. MCP full-build status currently
does not stream console output, so an unchanged progress field alone does not
establish an analysis stall.

## Time budgets and cold workspaces

Snippet and file checks default to 1,800 seconds (30 minutes); callers may set
`timeout_seconds` from 1 through 10,800 seconds. Full builds and checkpoint
validation allow 10,800 seconds (three hours). These are cancellation ceilings,
not target runtimes or polling intervals.

A cold workspace can prepare dependency repositories, fetch Mathlib's published
compiled artifacts, and perform Bazel analysis before any remote Lean action
starts. This setup consumes the same wall-clock budget. Measure cold setup,
warm verification, and cache invalidation separately. Do not treat expiry of a
short diagnostic budget as evidence of a bad theorem or an execution deadlock.

## Operator rollout

1. Wait for all existing queued/running jobs to finish. Preserve retained
   workspaces and job records. Do not restart an active verifier.
2. In the server checkout, run `git pull --ff-only`. Preserve local changes;
   resolve a failed fast-forward before restarting.
3. Run the regression suite and the real Bazel checks:

   ```bash
   python3 -m unittest discover -s tools -p 'test_*.py' -q
   python3 tools/bazel_verification.py --fix
   python3 tools/bazel_verification.py --check
   bazel build --config=buildbuddy //:smoke
   bazel build --config=buildbuddy //:RiemannResearch
   ```

4. Leave `LEAN_VERIFICATION_BACKEND` unset for Bazel. On this host, install
   the resource-policy drop-in above to bound aggregate memory while keeping
   `LEAN_BAZEL_JOB_WORKERS=0`.
   Restart the existing `lean-tunnel.service` only when its jobs are idle.
   After changing a systemd drop-in, run `sudo systemctl daemon-reload`
   before restarting. Preserve other service settings.
5. Refresh the connected plugin's tool schema. Confirm `backend` is advertised
   on the four queued tools and that workspace/job results report Bazel.
6. Through the plugin, run a valid snippet, an invalid snippet, a file check,
   and one explicit `backend="lake"` check. Confirm successful jobs report
   their selected backend and failures do not switch backends. Run the existing
   checkpoint gate before publishing project changes.

The offline tests substitute fake compilers. Passing those tests checks routing,
package generation, queue identity, cleanup, and publication gates; it does not
establish that the actual Bazel toolchain compiled the project or that the live
service loaded the change.

Rollback changes only the backend selection; it does not delete new packages,
workspaces, cache entries, source changes, or job records. A historical clone
without the Bazel setup must use the explicit legacy backend until updated.

## Observed verification tests: 2026-11-08 to 2026-11-09

For the larger 4/42/100-module invalidations, failed cold-start trials, and
full-build overlap under the revised memory policy, see the
[November 9 stress-test report](STRESS_TEST_20261109.md) and its linked job data.

These are actual MCP jobs on the NucBoxK6 WSL host. Times below are server-side
verification wall times; clone, RPC, and polling delays are excluded. Fixtures
remained in isolated workspaces and were not published.

| Test | Observed result |
| --- | --- |
| Fresh workspace, new real-number identity | Passed in 17.389 s; one remote compilation |
| Identical source in a second workspace | Passed in 13.642 s; one remote-cache hit |
| Earlier partial invalidation of a mid-graph proof | Passed in 44.581 s; four remote compilations and 196 remote-cache hits |
| Warm serial changed-source checks, three workspaces | 8.035 / 7.108 / 8.189 s; one remote compilation each |
| Warm concurrent changed-source checks, same three workspaces | 6.576 / 6.432 / 6.666 s; one remote compilation each |
| Deliberately false equality proved with rfl | Rejected in 6.004 s with the expected Lean equality error |
| False equality using sorry with warnings suppressed | Rejected in 10.118 s: declaration uses sorry while forbid_sorry is enabled |
| Deliberate one-second deadline | Controlled wall_timeout in 1.822 s; next valid check passed in 3.027 s |
| Restore after both invalid-proof tests | Exact original source hash restored; passed in 3.071 s |
| Full aggregate | Passed in 856.977 s; 3,777 action-cache hits and 165 remote-cache hits |

The concurrent changed-source batch spanned 8.438 s from first worker start to
last finish, with all three workers overlapping for 4.783 s. Admission took
0.899 / 0.981 / 1.334 ms, with no completed-history records examined. Each job
reported an uncapped global worker count, one job per workspace, and distinct,
matching submitted/checked source hashes. No slowdown was observed in this
small sample; warmup and ordering effects prevent treating the faster parallel
times as a general speedup claim.

The full aggregate configured 46,184 targets in 150 packages. It reused cached
results rather than recompiling the whole project, and its elapsed time includes
the memory-reclaim episode described above. During that run, the operator raised
MemoryHigh to 9 GiB and stopped the two completed test JVMs. After the full build,
the operator stopped its idle JVM; measured service memory fell to about 516 MiB
and ten-second full memory pressure fell to 0.05%. This is not a clean cold-build
benchmark, a peak-memory measurement for the concurrent batch, or evidence that
several simultaneous full-project analyses fit in the host budget.

Evidence:
- [Full aggregate](https://app.buildbuddy.io/invocation/40eedd76-01dd-45df-b32c-8ff5c8820b7d)
- Concurrent checks: [A](https://app.buildbuddy.io/invocation/7d3744af-3bb9-4b91-87e3-1ac01799042d), [B](https://app.buildbuddy.io/invocation/47eb2b02-5490-44bc-9ce2-55b22272ff9c), [C](https://app.buildbuddy.io/invocation/2d5bfc3a-1a5c-426a-ad79-9a8c60f3f99b)
- [Partial invalidation](https://app.buildbuddy.io/invocation/2a3eee75-78b3-43ef-89e0-38fa6e5ebb97)
- [False equality](https://app.buildbuddy.io/invocation/7e63805d-a5d9-4256-8ff2-b6ebff7c2b26)
- [Suppressed-sorry rejection](https://app.buildbuddy.io/invocation/b512dacb-784a-4b41-82e1-c15b00fe61cd)
- [Timeout](https://app.buildbuddy.io/invocation/eb1ac1bb-2b33-4ee4-99c8-5926c667ac4c) and [successful recovery](https://app.buildbuddy.io/invocation/a2a82da3-c0c6-4def-90a9-b60b2981417b)
- [Restored proof](https://app.buildbuddy.io/invocation/51a5ff2c-bf7d-4beb-bbbf-9b7f4cf83cb1)
