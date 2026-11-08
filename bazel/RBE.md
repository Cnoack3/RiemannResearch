# RBE smoke setup

## BuildBuddy Personal trial

`bazel build --config=buildbuddy` selects BuildBuddy's hosted executors and
artifact cache. It also sends build events to the authenticated BuildBuddy
organization so its invocation page can show execution and transfer statistics.
Ordinary builds keep the GCS cache. MCP verification defaults to Bazel with
BuildBuddy; Lake is available as an explicit legacy backend.
Use either `--config=buildbuddy` or `--config=rbe`, not both.

The BuildBuddy profile uses the existing pinned Ubuntu 24.04 Linux x86-64
platform, 80 jobs, minimal output downloads, and remote execution only.
An executor failure fails the build rather than compiling on the MCP server.
BuildBuddy's hosted workers use its CAS; this profile does not attach our GCS
bucket to those workers.

All updated checkouts use shared local caches under `~/.cache/riemann-bazel`:
repository archives in `repository/`, completed repositories in `repo-contents/`,
and action results/downloaded blobs in `disk/`. Mutable output state remains
separate for each workspace under `outputs/`, outside the checkout. The disk
cache uses a 32 GiB soft limit and 14-day retention. Builds remove convenience
`bazel-*` symlinks, so inspect outputs via `bazel info bazel-bin` instead.
These settings come entirely from each checkout's `.bazelrc`; existing
checkouts adopt them when updated. Per-workspace output bases have no automatic
size limit or additional MCP cleanup. See
[shared storage details](VERIFICATION.md#shared-storage).

Minimal output downloads remain enabled. Only bytes actually fetched from
BuildBuddy enter the local CAS; the configuration does not mirror every remote
artifact. This local reuse reduces repeated client downloads, not the SDK input
bytes downloaded by BuildBuddy's executors.

The API key is scoped to `common:buildbuddy` in this private repository's
`.bazelrc`, as authorized by the repository owner. No additional authentication
setup is needed in each checkout. The key supports unattended builds across
reboots until it is revoked or disabled; no Google login is needed for this
profile. A replacement key can be set under the same config in the git-ignored
`.bazelrc.local`, which is imported last.

From the repository root on the Ubuntu MCP server, start with the tiny probe:

```sh
bazel --output_base="$HOME/.cache/bazel-buildbuddy-smoke" build \
  --config=buildbuddy --remote_accept_cached=false \
  --action_env=LEAN_RBE_PROBE_NONCE="$(date +%s%N)" \
  --remote_download_outputs=toplevel //bazel:rbe_probe
cat "$(bazel --output_base="$HOME/.cache/bazel-buildbuddy-smoke" info bazel-bin)/bazel/rbe-probe.txt"
```

Expect `Linux x86_64` and an actual `remote` process in the build summary.
This checks authentication, image pulling, and execution without fetching
Mathlib or uploading the Lean SDK. A cache hit alone does not prove execution.
`--remote_accept_cached=false` bypasses remote action cache reads, but does not
force locally up-to-date actions to rerun. It also bypasses remote repository
contents reads if that experiment is enabled; our configuration keeps that
experiment disabled after hangs on the Ubuntu server.
Use it only for this tiny executor probe. The nonce changes the probe action's
key so repeated probes exercise execution without cleaning the workspace.

Then build the Lean smoke target and its compiled-sorry audit, keeping caches
enabled:

```sh
bazel --output_base="$HOME/.cache/bazel-buildbuddy-smoke" build \
  --config=buildbuddy //:smoke
```

The smoke target imports `Mathlib.Tactic.NormNum`, but `MODULE.bazel` prepares
the entire Mathlib repository (`modules = ["Mathlib"]`) for all project targets.
If the shared local repository contents cache has no matching entry, its first
population runs `lake exe cache get Mathlib` locally before remote Lean actions
can start. Experimental remote repository contents caching is disabled, so
this stage has no remote repository cache fallback. This can take several minutes. It may also need
to upload the Lean SDK and imported artifacts to BuildBuddy. It does not compile
the full RiemannResearch target.

Fresh workspaces on the same Ubuntu server should reuse the completed repository
through the shared local contents cache under the same `output_user_root`.
A local hit links the completed directory; it does not repeat the Mathlib
bootstrap or copy its compiled bundles into every workspace. RBE itself does
not execute repository rules. Changed dependency inputs, cache eviction, or a
different cache location can still cause a cold fetch. Confirm reuse with the
fresh output base below before relying on this for agent workspaces.

Test shared local repository reuse and remote action cache reuse from a second
output base, allowing cached results:

```sh
bazel --output_base="$HOME/.cache/bazel-buildbuddy-warm" build \
  --config=buildbuddy //:smoke
```

Compare the linked invocation pages: remote actions when compilation is needed,
cache hits on the fresh repeat, and uploaded/downloaded bytes. Stored artifact size is
not the same as transfer per invocation. Keep the account on the free Personal
plan; its public pricing does not specify exactly how internal executor traffic
counts toward the advertised transfer allowance.

Validation: The forced remote probe passed on the Ubuntu server. Bazel 9.2.0
accepted the profile and selected the pinned Linux platform for the Lean smoke
action, including its compiled-sorry audit. The compatibility patch permits
absent macOS `.dylib` files in the Linux SDK while keeping its required globs
strict. The generated SDK BUILD file reproduced the original empty-glob error
before that fix and passed smoke-target analysis afterward, using the real
Linux SDK. Hosted Lean compilation remains unverified in these diagnostics.
Smoke and full-project action-cache reuse have since passed the user-run
checks below.

Sources: [RBE setup](https://www.buildbuddy.io/docs/rbe-setup/),
[authentication](https://www.buildbuddy.io/docs/guide-auth/),
[execution platforms](https://www.buildbuddy.io/docs/rbe-platforms/), and
[Personal pricing](https://www.buildbuddy.io/pricing/).

## Google RBE profile

Instance creation for this project returned `FAILED_PRECONDITION`: the project
is not allowlisted for Google Remote Build Execution. The profile below remains
available if managed-service access is granted; enabling the API alone is not
sufficient.

`bazel build --config=rbe` selects Google Remote Build Execution at
`remotebuildexecution.googleapis.com`, instance
`projects/project-c5cfd87b-fbe8-47ea-9d0/instances/lean-test`.
The profile uses two jobs, an Ubuntu 24.04 Linux x86-64 execution platform,
and remote execution only. It fails if the executor fails; it cannot silently
compile on the MCP server. Ordinary builds keep the existing GCS cache profile.

The execution image is pinned to the digest used by
[Gerrit's RBE setup](https://gerrit-review.googlesource.com/Documentation/dev-bazel.html#_google_remote_build_support).
Lean comes from the declared Bazel toolchain inputs. No Lean installation or
project checkout is needed in the worker image.

## Check project access first

Run these commands on the Ubuntu MCP server. They do not create billable workers.

```sh
gcloud config set project project-c5cfd87b-fbe8-47ea-9d0
gcloud auth list --filter=status:ACTIVE --format='value(account)'
gcloud services list --enabled \
  --filter='config.name:remotebuildexecution.googleapis.com' \
  --format='value(config.name)'

curl --silent --show-error --fail-with-body \
  -H "Authorization: Bearer $(gcloud auth print-access-token)" \
  'https://admin-remotebuildexecution.googleapis.com/v1alpha/projects/project-c5cfd87b-fbe8-47ea-9d0/instances'
```

The list endpoint comes from Google's
[RBE admin API specification](https://code.googlesource.com/google-api-go-client/+/refs/heads/master/remotebuildexecution/v1alpha/remotebuildexecution-api.json).
Enabling the API does not prove instance creation or execution access. Inspect
the response before creating a worker pool. The proposed smoke pool has one
`e2-standard-8` worker in `us-central1`; provisioning has not been run.

## Authenticate and test after provisioning

Google RBE uses OAuth. The GCS HMAC key cannot authenticate to this service.
Bazel reads private Application Default Credentials (ADC), independently of
the `gcloud` CLI login. If ADC is absent, use
`gcloud auth application-default login` on the Ubuntu server and follow its
browser instructions. Do not copy credentials into the checkout.

User ADC can refresh access tokens, but organization session policies can require
another login. It does not meet a guaranteed unattended "never reauthenticate"
requirement. Resolve a supported machine identity or federation before making
RBE the server's default build path.

Once the instance and worker pool are running, from the project root:

```sh
bazel --output_base="$HOME/.cache/bazel-rbe-smoke" build --config=rbe \
  --remote_accept_cached=false --remote_download_outputs=toplevel \
  //bazel:rbe_probe
cat "$(bazel --output_base="$HOME/.cache/bazel-rbe-smoke" info bazel-bin)/bazel/rbe-probe.txt"

bazel --output_base="$HOME/.cache/bazel-rbe-smoke" build --config=rbe \
  //:smoke
```

The first command tests the executor without fetching Mathlib or uploading the
Lean toolchain. Look for an actual `remote` process in the build summary.
`remote cache hit` alone does not prove execution. The second command tests Lean
and its compiled-sorry audit with repository and action cache reads enabled. Repository fetching and analysis still run locally;
Lean compilation and its audit run remotely. The first Lean test must upload its
SDK and imported artifacts to the execution service's CAS. Later actions reuse
those blobs.

The RBE profile uses its execution service's CAS and action cache, rather than
the separate `bazel-remote` GCS backend. A cached repeat should then be tested
from a fresh Bazel output base, without `--remote_accept_cached=false`.

Validation so far covers Bazel flag parsing, action analysis, and selection of
the Linux execution platform. Live Google RBE execution, instance access, and
persistent machine authentication remain untested.

## RBE performance diagnostics

### Build progress and quiet logs

Normal builds show Bazel progress, status messages, warnings, and successful
completion. `--output_filter='^$'` suppresses stdout/stderr from successful
build actions, including Lean's informational messages and compiler warnings.
Failed-action diagnostics and failed-test logs remain visible. Long output-file
lists remain hidden. The filter applies at the action-output boundary, so it
does not hide Bazel's progress or completion messages.

The earlier default suppressed both INFO and progress, making successful
cached builds silent and long-running builds appear idle. That global
suppression is now restricted to the explicit quiet configuration.

For fully silent successful builds, select quiet mode explicitly:

```sh
bazel build --config=buildbuddy --config=quiet //:smoke
```

Restore successful action output and output-file details when diagnosing a problem:

```sh
bazel build --config=buildbuddy --config=verbose //:smoke
```

To expose startup, lock, or analysis problems without running Lean compilation:

```sh
timeout --signal=INT --kill-after=5s 45s bazel --noblock_for_lock build \
  --config=buildbuddy --config=verbose --nobuild //:smoke
printf 'Bazel diagnostic exit: %s\n' "$?"
```

Exit 9 indicates another command holds this Bazel server's lock; exit 124
indicates the 45-second diagnostic timed out. Dependency repository setup can
still run during analysis. The diagnostic explicitly selects BuildBuddy;
ordinary builds without that config use the local GCS cache proxy at
`http://127.0.0.1:9090`, which must be running.

These display options do not alter Lean action commands, the compiled-sorry
audit, or action cache keys. They do not reduce worker input downloads. Action
stdout/stderr can still exist in the remote execution logs even when it is
hidden from the build console.

Structured build events and profiles remain available; execution logs can be
enabled separately for an input audit. Raw
worker action output can still be recorded and transferred; quieter console logs
are not evidence of a measured performance or transfer reduction.

Sources: [Bazel 9.2 action output filter](https://github.com/bazelbuild/bazel/blob/9.2.0/src/main/java/com/google/devtools/build/lib/buildtool/BuildRequestOptions.java),
[UI filters](https://github.com/bazelbuild/bazel/blob/9.2.0/src/main/java/com/google/devtools/build/lib/runtime/UiOptions.java),
[UI output handling](https://github.com/bazelbuild/bazel/blob/9.2.0/src/main/java/com/google/devtools/build/lib/runtime/UiEventHandler.java),
and [successful versus failed action output](https://github.com/bazelbuild/bazel/blob/9.2.0/src/main/java/com/google/devtools/build/lib/skyframe/SkyframeActionExecutor.java).

### Local client limits and artifact uploads

The repository sets an 8 GiB maximum Java heap, two loading/analysis threads,
and a two-CPU budget for locally scheduled actions. `ActiveProcessorCount=2`
also reduces automatically sized JVM pools, including garbage collection.
The heap ceiling excludes native memory, thread stacks, and child processes.
The CPU settings are scheduling and pool-size controls, not an operating-system
CPU quota; explicitly sized remote callback pools can still run more threads.
The normal BuildBuddy profile continues to allow 80 remote jobs.

Bazel uses Linux batch CPU scheduling to favor interactive work. An idle JVM
exits after five minutes, and idle low-memory shutdown is enabled. The shared
disk and repository-content collectors start after one idle minute so they can
run before that timeout. These settings are per JVM; each workspace has its own
Bazel server. They are not a combined RAM limit across workspaces.

For this memory-sensitive MCP host, install
[`lean-tunnel.resources.conf`](lean-tunnel.resources.conf) as described in
[the verification guide](VERIFICATION.md#host-resource-policy). It sets the
aggregate memory controls (`MemoryHigh=9G`, `MemoryMax=10G`, and
`MemorySwapMax=1G`) for the service and its descendants. Independent workspaces
remain concurrent with `LEAN_BAZEL_JOB_WORKERS=0`, and each BuildBuddy build
retains its 80-action limit. Local Lean pools and retained editor clients are
bounded separately. Manually launched builds outside the service are not covered.
Warm dependency setup in one fresh workspace before parallel recovery tests.
No Python changes are required.

The JVM also exits immediately on heap exhaustion via
`-XX:+ExitOnOutOfMemoryError`, including when a background callback encounters
it. This prevents an exhausted server from continuing to run; it does not
prevent OOM. Immediate exit can leave the final event/profile diagnostics
incomplete and outstanding remote actions may finish independently.

Allow memory headroom beyond the 8 GiB heap; full-project runs previously
reported about 8.5 GiB process RSS. Reducing the heap without a measured trial
risks recreating the earlier OOM failures. The host policy bounds aggregate
service memory; an oversized job may fail at that boundary. The heap limit remains
configurable in `.bazelrc.local`;
a smaller value is not established as sufficient for the full analysis graph.

Startup settings only apply when a Bazel server starts. Updating the rc file
does not retroactively change already-running or retained older workspaces.
Restart the MCP service only when its jobs are idle. Manually launched idle
Bazel servers can be stopped from their own workspace with
`bazel --noblock_for_lock shutdown`. Avoid killing all Java processes.

BuildBuddy now uses
`--experimental_build_event_upload_strategy=local`.
This bypasses the remote BEP artifact uploader's file-metadata digest pass,
which appeared in the reported Java heap exhaustion. Build events still go to
BuildBuddy, and remote execution and action-cache transfers continue normally.
Artifact, test-log, and profile references in those events become local file
URLs, so BuildBuddy cannot retrieve those files from the dashboard. With minimal
output downloads, a referenced artifact may also be absent from the local disk.
The diagnostic script retains its profiles and logs locally.

Restore hosted artifact uploads explicitly when needed:

```sh
bazel build --config=buildbuddy-artifacts //:smoke
```

That profile still uses 80 jobs and may reproduce the uploader memory pressure.
Do not add `--build_event_upload_max_threads`: Bazel removed it in version 8.
Changing `--bes_upload_mode` does not limit metadata concurrency.

After stopping any currently running build and pulling these changes, the next
Bazel invocation restarts that output base's server because its startup
arguments changed. Start with the bounded analysis and smoke commands below;
there is no need to clean the cache. Local overrides or command-line options
can change these limits.

The option names and uploader behavior were checked against Bazel 9.2.0 source.
The memory/CPU effect and a successful full build remain unverified on the
Ubuntu server.

Sources: [JVM OOM exit implementation](https://github.com/openjdk/jdk/blob/jdk-21%2B35/src/hotspot/share/utilities/debug.cpp),
[JVM heap and processor options](https://docs.oracle.com/en/java/javase/21/docs/specs/man/java.html),
[Bazel 9.2 loading threads](https://github.com/bazelbuild/bazel/blob/9.2.0/src/main/java/com/google/devtools/build/lib/runtime/LoadingPhaseThreadsOption.java),
[local action resources](https://github.com/bazelbuild/bazel/blob/9.2.0/src/main/java/com/google/devtools/build/lib/exec/ExecutionOptions.java),
[BEP upload strategies](https://github.com/bazelbuild/bazel/blob/9.2.0/src/main/java/com/google/devtools/build/lib/buildeventstream/BuildEventProtocolOptions.java),
and [local artifact uploader](https://github.com/bazelbuild/bazel/blob/9.2.0/src/main/java/com/google/devtools/build/lib/buildeventstream/LocalFilesArtifactUploader.java).

### Imported module lookup errors

A missing object path beneath a project package, such as
`FromPNTPlus/Mathlib/MeasureTheory/Function/Floor.olean`, can result from
namespace shadowing. Lean chooses the first search root containing a
`Mathlib` directory and does not continue to later roots when the requested
file is absent. Bazel's output tree for vendored project modules can create
that directory even though their actual namespace begins with
`RiemannResearch`.

The compatibility patch detects these physical namespace directories and
supplies explicit artifact paths for affected import closures. The pinned
Mathlib revision includes `Mathlib.MeasureTheory.Function.Floor`; this fix
does not change its import, project proofs, dependency versions, or action
inputs. Unaffected namespaces continue to use ordinary search paths.

After pulling the fix, retry the affected target with the bounded script:

```sh
bash bazel/rbe_benchmark.sh smoke \
  //RiemannResearch/RH/WeilExplicitFormula/FromPNTPlus:ZetaBounds
```

There is no need to clean the cache. Patch application and a filesystem model
of the reported lookup failure have been checked locally. Live Bazel
compilation of this target remains to be verified on the Ubuntu server.

Source: [Lean 4.33 module lookup](https://github.com/leanprover/lean4/blob/v4.33.0-rc2/src/Lean/Util/Path.lean).

### Bounded measurements

The BuildBuddy profile enables Bazel 9.2's `--remote_cache_compression`.
This compresses client-to-cache transfers. It does not remove required inputs
or guarantee a decrease in the internal-download usage counter.

Lean library default outputs contain only that library's compiled files.
The Lean provider still supplies its full transitive import artifacts, and
compilation inputs and the compiled-declaration audit remain unchanged.
This reduces the exposed default-output set; with minimal downloads already
enabled, it is not evidence of a measured internal-transfer reduction.

The ordinary BuildBuddy profile retains the checkout's 80-job setting.
A bounded diagnostic profile permits eight:

```sh
bazel build --config=buildbuddy-benchmark //:smoke
```

The job limit affects cached builds too: Bazel 9.2 uses it for execution-side
work and remote callback handling. Increasing it may improve cache-check
throughput, but can also increase client memory use. Compilation concurrency
can additionally increase input staging and executor queuing.

Start with one bounded measurement from the repository root:

```sh
bash bazel/rbe_benchmark.sh analysis
```

Paste the final **RBE summary** block into chat. It includes the job count, exit code, build
wall time, sampled JVM memory, available Bazel analysis/action statistics, and
the BuildBuddy invocation link. No files need to be copied out of WSL for this
first pass. The script captures its detailed output locally instead of streaming
successful-action log spam. On failure it also prints the last 40 log lines and
up to three diagnostic lines in the summary.

If analysis succeeds, run `bash bazel/rbe_benchmark.sh cache-only` next. Only if
that fails specifically because of a cache miss, run `smoke`, then `repeat`, then
`cache-only` again. Stop and report an analysis OOM or timeout before attempting
compilation. Leave `parallel` and full-project compilation for later.

The analysis mode defaults to the full aggregate with `--nobuild`; it does not
compile project modules. Other modes default to `//:smoke`, and accept a target
as the second argument. The build phase has a ten-minute limit; override it with
`RBE_BENCH_TIMEOUT`. Profiles, command output, revision and
dirty-tree metadata, client resource reports, and JVM samples are retained beneath
`$HOME/.cache/riemann-rbe-diagnostics` (or `RBE_DIAGNOSTICS_DIR`).
The script does not clean existing workspaces or force cache misses.
Execution logging is disabled by default, including any inherited compact,
JSON, or binary execution-log setting. It walks action inputs and uses a shared
serialization lock, so enabling it can distort cache-hit timing. The separate
JSON trace profile remains enabled. For a deliberate input-manifest audit,
use `RBE_BENCH_EXECUTION_LOG=1`; non-analysis modes then retain `execution.log`
locally. That audit run adds logging overhead and should not be compared with
logging-disabled timing runs. Analysis mode always disables execution logging.
The console summary and `run.txt` record the effective execution-log setting.
After the timed build, the script also inventories the selected SDK's runtime
files using file metadata, and includes the total plus namespace/artifact size
breakdowns in the same paste-ready summary. It needs only Python's standard
library and does not invoke Bazel again or download inputs. The existing rules
include this full SDK runtime filegroup in every `LeanOlean` action. Native
static libraries, headers, and `.ilean` files are excluded from this inventory,
matching that filegroup. The Lean executable, Mathlib/project inputs, and
plugins are separate and are not included in the reported SDK runtime total.
Logical file sizes are not BuildBuddy download or billing measurements; shared
digests, compression, and worker reuse can change transferred bytes. The size
scan runs after timing and resource sampling finish, with a 15-second timeout
and up to two seconds of termination grace. A missing, ambiguous, incomplete,
or timed-out SDK inventory does not change the build's exit code.
It captures INFO in `build.log` for its summary while keeping warnings filtered.
Those INFO events also reach the BuildBuddy console during benchmarks. Use
`--config=verbose` on an ordinary build to inspect the full console diagnostics.
Server startup/PID discovery is capped at 30 seconds before the timed build.
Termination grace periods can extend the timeout bounds. `resources.txt`
measures the client and wrapper. `server-resources.txt` samples the persistent
JVM every two seconds;
its CPU percentage is a lifetime average, and sampling can miss brief RSS peaks.

Bazel 9.2 has no `analyze-profile` subcommand. The script retains
`profile.gz` and writes `profile-viewing.txt` with viewing instructions instead
of invoking that command. In Chrome, open
`chrome://tracing`, click **Load**, and select the compressed profile.
Look for `runAnalysisPhase`, remote setup/cache events, and garbage collection.
See [Bazel's JSON trace profile guide](https://bazel.build/versions/9.2.0/advanced/performance/json-trace-profile).
Use `exit-code.txt` and `build.log` to determine whether the build passed;
an error from the old post-processing command did not change the recorded
Bazel build exit code. Profiles from an interrupted build or OOM may be
incomplete. Existing profiles can be inspected without rerunning the build.

The repeat mode reuses the same client output base as smoke. Cache-only
uses a fresh output base and `--experimental_remote_require_cached`: an
action-cache miss fails instead of dispatching remote compilation.
The harness uses `flock` to serialize benchmarks sharing a diagnostics root.
Before a cache-only run, it shuts down idle servers recorded by completed
benchmark runs, including the shared diagnostic client. It validates the
recorded base and PID and uses nonblocking Bazel shutdown; a selected live base
without matching completed PID metadata, or a busy server, stops the new check.
Unrecognized paths are not selected for cleanup. The new
cache-only server is also shut down on exit. These bounded shutdowns are outside
the reported build wall time and preserve output directories, caches, and
reports. Other ordinary Bazel output bases are not selected for cleanup.
Repository bootstrap can still run locally on a native repository-cache miss.
Hold source revision, platform, instance name, and action environment fixed.
A timeout or bootstrap error is not proof of a remote-cache miss.

### Recorded cache-check baseline

The user reported these successful runs on the NucBoxK6 WSL checkout at
`785e2a8273ccd2c403d3f4f1c54950faa3d7d43c`, using the two-job default:

| Measurement | Bazel elapsed time | Peak sampled JVM RSS | Remote action-cache hits |
| --- | ---: | ---: | ---: |
| Full project, analysis only | 42.512 s | 5.73 GiB | Execution skipped |
| Smoke, cache only | 10.894 s | 0.57 GiB | 1 |
| Full project, cache only | 506.001 s | 8.52 GiB | 2,512 |

Full cache-only analysis configured 43,222 targets; its critical path was
15.97 seconds. All 2,512 external actions were cache hits. The additional
`1 internal` process counts a Bazel action, not BuildBuddy download bytes.
This verifies remote cache reuse at full-project scale, but it does not measure
worker input downloads or establish the cause of the cache-check delay.

The 8 GiB limit applies to Java heap, so 8.52 GiB of process RSS does not
indicate that the heap limit was ignored. Earlier benchmark versions left their
servers running after cache-only checks; those servers could add memory
pressure between trials. That possibility is not evidence of observed swapping.

Further user-run full-project cache-only checks at
`0c67f6bd595d0cb43492e00e7fb58b5e0dfe0d58` used the corrected JVM cleanup:

| Jobs | Bazel elapsed time | Peak sampled JVM RSS | Critical path |
| ---: | ---: | ---: | ---: |
| 4 | 300.676 s | 8.53 GiB | 18.76 s |
| 8 | 198.227 s | 8.50 GiB | 24.24 s |
| 80 | 180.656 s | 8.53 GiB | 94.26 s |

Each run passed with the same 2,512 remote action-cache hits and 43,222
configured targets. Eight to 80 jobs improved elapsed time by only about 9%,
with essentially unchanged RSS. That shows diminishing returns at this point;
the summary alone cannot identify input preparation, RPC waits, or GC as the
remaining cause. Cleanup also changed between the two-job and four-job trials,
so their entire speed difference cannot be attributed to job count. These
fresh-output-base checks measure cache-check throughput, not worker compilation
or an unchanged repeat in a persistent client workspace.

All of the cache-only timings above used a benchmark version that enabled
`--execution_log_compact_file` unconditionally. The later 80-job trace reported
2,458 `logSpawn` records totaling 5,289.015 inclusive seconds, with a 6.927-second
maximum. It also recorded long nested `logEntry` scopes. These overlapping
durations are not wall time or CPU time, and their sums cannot be added together
or subtracted from the build duration. They identify execution logging as a
significant candidate for the measured delay; they do not establish the speedup
from disabling it. The compact logger traverses action input sets and emits
entries through synchronized methods. Normal repository builds do not enable
an execution-log file in `.bazelrc`; this overhead was introduced by the
diagnostic script. The script now defaults to logging disabled. Measure that
default before attributing the old three-minute result to ordinary cache lookup.
This change does not shrink remote worker inputs or their download size.

The follow-up user run on the same clean `0c67f6bd595d` source snapshot, with
80 jobs and execution logging disabled, passed with all 2,512 remote cache
hits and the same 43,222 configured targets:

| Execution logging | Bazel elapsed | Build wall time | Peak sampled JVM RSS | Critical path |
| --- | ---: | ---: | ---: | ---: |
| Enabled, previous run | 180.656 s | 182.04 s | 8.53 GiB | 94.26 s |
| Disabled, follow-up | 100.114 s | 101.55 s | 8.51 GiB | 19.58 s |

The follow-up elapsed time is 80.542 seconds (44.58%) lower. This is one
user-run comparison; machine load and filesystem cache state were not fully
controlled. Removing execution logging was a material improvement, while the
roughly 100-second cache check and essentially unchanged RSS still need work.
Invocation: [logging-disabled run](https://app.buildbuddy.io/invocation/e5d3d207-8fbc-4b44-af5a-c6317483e6b5).

The same run inventoried 12,444 SDK runtime files totaling 2.526 GiB (about
2.712 GB decimal). By namespace: Lean 1.190 GiB, runtime libraries 0.566 GiB,
Init 0.362 GiB, Std 0.306 GiB, Lake 0.099 GiB, and other modules 0.002 GiB.
By artifact kind, `.olean.private` accounts for 1.254 GiB, shared libraries
0.566 GiB, `.ir` 0.346 GiB, `.olean` 0.330 GiB, `.olean.server` 0.030 GiB,
and `.ir.sig` rounds to 0.000 GiB. These are declared file sizes, not actual
worker downloads. They cannot simply be subtracted from a BuildBuddy download
counter to infer the remaining input composition.

Lean 4.33's default module loader reads the `.olean`, `.olean.server`, and
`.olean.private` parts for module-system imports, and can also load `.ir.sig`
and `.ir` together. Dropping a whole artifact suffix is not a safe SDK pruning
strategy. A smaller SDK input set must preserve all required parts of each
selected module and the compiled-sorry audit's dependency closure.
Source: [Lean 4.33 module loader](https://github.com/leanprover/lean4/blob/v4.33.0-rc2/src/Lean/Environment.lean).

The large worker payload still needs a separate reduction. The current rules
select all SDK `.olean*`, `.ir`, and `.ir.sig` files plus runtime shared
libraries for every compilation, rather than the SDK import closure of that
module. The compiled-sorry audit also runs an interpreted helper with
`import Lean`, which needs its own SDK dependency closure. Measure the SDK's
share of the input payload before pruning it, and preserve the audit's imports,
Lean's implicit imports, all required module artifacts, and runtime libraries.
No SDK inputs have been removed by these diagnostic changes.

For one full-project timing at 80 jobs with the source revision from the previous
80-job run, use the current harness against a detached source snapshot:

```sh
RBE_BENCH_REVISION=0c67f6bd595d RBE_BENCH_JOBS=80 \
  bash bazel/rbe_benchmark.sh cache-only //:RiemannResearch
```

`RBE_BENCH_REVISION` accepts a locally available 7-40 character commit SHA and
only applies to cache-only mode. It prepares a detached Git worktree under the
new report's `source` directory, uses that revision's sources and Bazel config,
and retains the snapshot for review. The original checkout stays on its existing
revision and retains any edits. Snapshot preparation is capped at 30 seconds
plus up to two seconds of termination grace, before build timing starts; checkout
hooks are disabled for that operation. The current script and SDK inventory
helper still run, even if the old revision lacks them. The summary records the
source revision, and the build remains cache-only. Keep the platform, instance,
action environment, and other cache-key settings fixed for the comparison.
Omit `RBE_BENCH_REVISION` to benchmark the current checkout.

Sources: [compact spawn logger](https://github.com/bazelbuild/bazel/blob/9.2.0/src/main/java/com/google/devtools/build/lib/exec/CompactSpawnLogContext.java),
[execution-log options](https://github.com/bazelbuild/bazel/blob/9.2.0/src/main/java/com/google/devtools/build/lib/exec/ExecutionOptions.java),
and [empty paths disable logging](https://github.com/bazelbuild/bazel/blob/9.2.0/src/main/java/com/google/devtools/build/lib/util/OptionsUtils.java).

To inventory an existing benchmark's SDK without any build:

```sh
python3 bazel/rbe_sdk_summary.py \
  "$HOME/.cache/riemann-rbe-diagnostics/cache-only-20261011T221733Z-93354"
```

The SDK inventory mirrors the pinned [SDK runtime globs](https://github.com/atvrager/rules_lean/blob/2cf9d007003ff73374e0082a82342e3f4723fc65/lean/private/repositories.bzl)
and this repository's [runtime-library patch](rules_lean_compat.patch). It accepts
an output base directly or reads `output_base` from the saved report's `run.txt`.
It uses bounded scans and fixed-size categories; unsupported directory symlinks,
missing selected files, multiple SDK roots, and limit failures report an
unavailable inventory instead of printing a partial total.

### Inspect an existing profile without another build

For the latest logging-disabled profile, also retrieve input-byte/file-count
metrics from the existing earlier logged run with the same clean source
revision, mode, target, and jobs:

```sh
python3 bazel/rbe_profile_summary.py --operations --input-metrics \
  "$HOME/.cache/riemann-rbe-diagnostics/cache-only-20261011T232359Z-244708"
```

This performs no build and does not enable execution logging. The operation
timings describe the specified new profile; the input metrics explicitly name
the older execution-log file they describe. Automatic matching rejects dirty
or incomplete source identities, and does not assert that all environment or
platform settings were identical. Input sizes are not worker transfer or
billing measurements. The compact-log reader uses the system `libzstd` shared
library and Python's standard library; no Python packages are needed. It streams
bounded protobuf records, decodes only recorded `LeanOlean` spawn metrics, and
reports counts, min/median/max sizes and file counts, and up to five largest
targets. Zero byte/file metrics mean unavailable in Bazel's schema, and are
excluded from these distributions. Corrupt, truncated, empty, or oversized logs
produce an unavailable result without publishing partial metrics. The reader
caps compressed/decoded bytes at 256 MiB, individual records at 16 MiB, total
records at one million, and Lean spawns at 100,000.

To read a known saved execution log independently:

```sh
python3 bazel/rbe_input_metrics.py \
  "$HOME/.cache/riemann-rbe-diagnostics/cache-only-20261011T221733Z-93354"
```

Sources: [compact log schema and input metric meanings](https://github.com/bazelbuild/bazel/blob/9.2.0/src/main/protobuf/spawn.proto)
and [input metrics set before remote cache lookup](https://github.com/bazelbuild/bazel/blob/9.2.0/src/main/java/com/google/devtools/build/lib/remote/RemoteSpawnRunner.java).

For the recorded 80-job run, after pulling the reader:

```sh
python3 bazel/rbe_profile_summary.py \
  "$HOME/.cache/riemann-rbe-diagnostics/cache-only-20261011T221733Z-93354"
```

Paste its final summary block. The reader also accepts a `profile.gz` path.
It uses Python's standard library and streams the compressed trace with bounded
record reads; it does not start Bazel or load the entire profile into memory.
Incomplete, unsupported, and malformed input is reported explicitly.
It reads the one-line task and counter subset emitted by Bazel 9.2; multiline
metadata is skipped. It is not a validator for every record in the JSON trace.

The 80-job profile's initial summary reported 4.642 cores on average and a
13.159-core peak, with 7,942 MiB maximum used Java heap plus nonheap memory.
The JVM's four-processor hint sizes automatic pools; it does not impose an OS
CPU quota. The merged analysis/execution phase spans most of this build, so its
large outer scopes cannot isolate the remaining cost. Only 94 named Merkle
records and 90 remote-cache-check records survive as distinct records in this
slim trace, versus 2,512 cached actions; those duration sums are incomplete.

To inspect finer recorded operation names in the same saved file:

```sh
python3 bazel/rbe_profile_summary.py --operations \
  "$HOME/.cache/riemann-rbe-diagnostics/cache-only-20261011T221733Z-93354"
```

This ranks recorded intervals by operation and category, excluding the outer
whole-build scopes. It retains at most 4,096 bounded name groups and explicitly
reports overflow. Names are capped at 140 characters and categories at 80, so
long names sharing a prefix can be grouped together. The intervals still include
nested work and waits; this is not a sampled CPU stack profile or exclusive
execution time. Slim-profile merging can hide short operations altogether.

Its output summarizes recorded trace intervals. Durations can overlap between
threads and nested tasks, so their sums are not build wall time or CPU time.
CPU counter values use cores (1 means one core); displayed averages are recorded
sample means. Memory counters measure used Java heap plus nonheap memory, not
process RSS. Neither counter should be silently inferred when absent.
Profiler thresholds and slim-profile merging mean record counts are not counts
of all calls. `Unknown event` merged spans may include gaps. Remote setup events
named `acquiring semaphore` measure waiting for the preparation throttle.
GC notification durations come from JVM GC reports with approximate timestamps;
they are not exact measurements of stop-the-world pause time or proof that GC
caused the delay. The full Chrome trace remains available when the compact
summary cannot resolve these distinctions.

Sources: [trace records and counters](https://github.com/bazelbuild/bazel/blob/9.2.0/src/main/java/com/google/devtools/build/lib/profiler/CounterSeriesTraceData.java),
[CPU and memory units](https://github.com/bazelbuild/bazel/blob/9.2.0/src/main/java/com/google/devtools/build/lib/profiler/CollectLocalResourceUsage.java),
[GC duration recording](https://github.com/bazelbuild/bazel/blob/9.2.0/src/main/java/com/google/devtools/build/lib/metrics/PostGCMemoryUseRecorder.java),
and [profile merging](https://github.com/bazelbuild/bazel/blob/9.2.0/src/main/java/com/google/devtools/build/lib/profiler/JsonTraceFileWriter.java).

Bazel 9.2 constructs each action's input-root and action digest before its
remote cache lookup. Ordinary input files are flattened and sorted for that
construction; their file digests can come from metadata, so this does not imply
that all input bytes are reread for every action. Its automatic Merkle subtree
caches cover aggregate artifacts, not arbitrary SDK depsets. The obsolete
`experimental_remote_merkle_tree_cache` and size flags are unavailable in this
version; keep the default Merkle-tree discard/throttle behavior while measuring.

Sources: [Merkle input preparation](https://github.com/bazelbuild/bazel/blob/9.2.0/src/main/java/com/google/devtools/build/lib/remote/merkletree/MerkleTreeComputer.java),
[action preparation before cache lookup](https://github.com/bazelbuild/bazel/blob/9.2.0/src/main/java/com/google/devtools/build/lib/remote/RemoteSpawnRunner.java),
[remote options](https://github.com/bazelbuild/bazel/blob/9.2.0/src/main/java/com/google/devtools/build/lib/remote/options/RemoteOptions.java),
and [remote callback executor](https://github.com/bazelbuild/bazel/blob/9.2.0/src/main/java/com/google/devtools/build/lib/remote/RemoteModule.java).

The diagnostic script uses two jobs by default to bound the baseline; it does
not lower the ordinary profile's 80-job setting. For a deliberate concurrency experiment on a bounded target that still
needs compilation:

```sh
bash bazel/rbe_benchmark.sh parallel //RiemannResearch/Analysis:AbelCoboundary
```

An already cached target does not benchmark execution concurrency.
Use `RBE_BENCH_JOBS=4` to try four jobs first. Do not use cache-bypass flags,
nonces, or a full-project forced rebuild for this experiment.

The console summary is sufficient for the initial review. When investigating
worker transfers, use the linked dashboard to compare external and internal
transfer deltas separately, worker input fetching, queue time, and execution
time. Cache-only profiles isolate warm-cache lookup work without paying for
another remote compilation. Detailed local files are only needed if the summary
and dashboard cannot explain the result.

Follow-up work is provider-level dependency metadata sharing and a reusable
compiled audit tool. Bazel's performance guidance warns that repeatedly
flattening overlapping depsets can produce quadratic analysis work:
https://bazel.build/rules/performance.
Do not narrow SDK inputs solely from explicit source imports: the audit imports
`Lean`, ordinary modules implicitly import `Init`, and imported prebuilt
modules can require additional SDK artifacts.

These changes have been checked for patch application and script behavior.
The user-run measurements above verify full-project analysis and remote
action-cache reuse. Hosted Lean compilation, worker input-transfer reductions,
and performance effects of changes beyond these measured concurrency trials
remain unverified.

## SDK inputs for BuildBuddy

`--config=buildbuddy` enables per-action SDK import closures by default. This is
the same flag sequence used by the successful full-repository build below:

```sh
bazel build --config=buildbuddy //:RiemannResearch
```

To select the previous full-SDK input set, put the rollback profile last:

```sh
bazel build --config=buildbuddy --config=lean-sdk-full //:RiemannResearch
```

The rollback disables SDK indexing and selects the original checker and action
inputs. It does not delete caches. `--config=lean-sdk-slim` remains available
when using another build profile. Do not add it separately to `buildbuddy`;
that profile already includes it.

At SDK repository setup, a helper uses the pinned Lean decoder to read imports
from the compiled SDK modules, including private olean parts. The toolchain
constructs a shared transitive depset for each SDK module once. A compile action
includes the SDK closures required by its own imports and its indexed external
dependencies, implicit `Init`, and any required compiled-sorry checker imports.
All existing shared runtime libraries remain inputs. This selects whole module
bundles; it does not drop `.olean.private`, `.olean.server`, `.ir` or `.ir.sig`
from selected modules. See the pinned
[module loader](https://github.com/leanprover/lean4/blob/v4.33.0-rc2/src/Lean/Environment.lean).

The smaller checker imports `Lean.Environment` and `Lean.Util.Sorry` instead
of the `Lean` umbrella. Its compiled-declaration audit body is identical to the
original checker, including private proof inspection and rejection of
suppressed sorry warnings.

Unknown prebuilt dependency graphs, custom plugins, custom `LEAN_PATH`, and
custom toolchains without an index retain the full SDK. SDK indexing currently
requires a native Linux x86-64 host and SDK. On other hosts use
`--config=lean-sdk-full`. Decoder failures and malformed/incomplete indexes
fail rather than silently disabling indexing. Errors include bounded stdout
and stderr. Builds that do not enable either `buildbuddy` or `lean-sdk-slim`
keep their previous SDK selection.

### Validation on 2026-11-08

The full aggregate
[build](https://app.buildbuddy.io/invocation/6c96992e-a5a6-43e5-a9f4-d4e3be794597)
succeeded in 672.845 seconds: 3,934 remote actions, one remote cache hit and one
internal action. Its cache panel recorded 5.846 GB downloaded, 2.64 GB compressed,
and 19.37 MB uploaded. Executor file caches were already populated, so this is
not a measurement of a completely cold executor fleet.

The same output digest was retained for the two inspected targets:

| Target and measurement | Full SDK | Selected SDK |
| --- | ---: | ---: |
| Basic: SDK inputs | 2.713 GB | 1.892 GB |
| Basic: external input files | 3.321 GB | 2.501 GB |
| Basic: recorded worker peak RAM | 1.377 GB | 263.7 MB |
| ZetaBounds: SDK inputs | 2.713 GB | 1.985 GB |
| ZetaBounds: external input files | 5.427 GB | 4.699 GB |
| ZetaBounds: recorded worker peak RAM | 1.704 GB | 775.9 MB |

Sources: [baseline action cache](https://app.buildbuddy.io/invocation/5fb1b633-1d08-461b-bd95-d89e9a6b6ac6#cache),
[Basic run](https://app.buildbuddy.io/invocation/5dc0ff52-8824-493b-84ff-b0955015ba4a),
and [ZetaBounds run](https://app.buildbuddy.io/invocation/4942914e-b3b5-4553-9539-3a3841cf122b).
Worker RAM figures are individual recorded executions, not a whole-repository
memory bound. The ZetaBounds trial rebuilt seven remote actions successfully.

The existing benchmark's SDK inventory reports the entire installed SDK, not
the subset selected for an action. Declared inputs, compressed transfer bytes,
executor-local file reuse, and account billing are different measurements.
These runs do not establish BuildBuddy free-tier eligibility or guarantee a
particular reduction for a completely cold fleet.

Nineteen local tests also exercise the actual Starlark functions, including
SDK closures, default-action equivalence, disabled-indexer behavior, error
reporting and rollback selection. The user-run Bazel builds above provide the
runtime evidence; the local action model alone does not compile Lean.
