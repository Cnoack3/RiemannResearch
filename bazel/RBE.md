# RBE smoke setup

## BuildBuddy Personal trial

`bazel build --config=buildbuddy` selects BuildBuddy's hosted executors and
artifact cache. It also sends build events to the authenticated BuildBuddy
organization so its invocation page can show execution and transfer statistics.
Ordinary builds keep the GCS cache. MCP verification continues using Lake.
Use either `--config=buildbuddy` or `--config=rbe`, not both.

The BuildBuddy profile uses the existing pinned Ubuntu 24.04 Linux x86-64
platform, 80 jobs, minimal output downloads, and remote execution only.
An executor failure fails the build rather than compiling on the MCP server.
BuildBuddy's hosted workers use its CAS; this profile does not attach our GCS
bucket to those workers.

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
cat bazel-bin/bazel/rbe-probe.txt
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
Linux SDK. Hosted Lean compilation and remote-cache reuse remain unverified.

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
cat bazel-bin/bazel/rbe-probe.txt

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

Additional execution concurrency only helps when compilation actions actually need to run.
It can increase input staging, memory use, and executor queuing.

Run the bounded diagnostic script from the repository root:

```sh
bash bazel/rbe_benchmark.sh analysis
bash bazel/rbe_benchmark.sh smoke
bash bazel/rbe_benchmark.sh repeat
bash bazel/rbe_benchmark.sh cache-only
```

The analysis mode defaults to the full aggregate with `--nobuild`; it does not
compile project modules. Other modes default to `//:smoke`, and accept a target
as the second argument. The build phase has a ten-minute limit; override it with
`RBE_BENCH_TIMEOUT`. Profiles, execution logs, command output, revision and
dirty-tree metadata, client resource reports, and JVM samples are retained beneath
`$HOME/.cache/riemann-rbe-diagnostics` (or `RBE_DIAGNOSTICS_DIR`).
The script does not clean existing workspaces or force cache misses.
Server startup/PID discovery is capped at 30 seconds before the timed build;
profile-summary generation is capped at two minutes after it. Termination
grace periods can extend those bounds. `resources.txt` measures the client and
wrapper. `server-resources.txt` samples the persistent JVM every two seconds;
its CPU percentage is a lifetime average, and sampling can miss brief RSS peaks.

The repeat mode reuses the same client output base as smoke. Cache-only
uses a fresh output base and `--experimental_remote_require_cached`: an
action-cache miss fails instead of dispatching remote compilation.
Repository bootstrap can still run locally on a native repository-cache miss.
Hold source revision, platform, instance name, and action environment fixed.
A timeout or bootstrap error is not proof of a remote-cache miss.

The diagnostic script uses two jobs by default to bound the baseline; it does
not lower the ordinary profile's 80-job setting. For a deliberate concurrency experiment on a bounded target that still
needs compilation:

```sh
bash bazel/rbe_benchmark.sh parallel //RiemannResearch/Analysis:AbelCoboundary
```

An already cached target does not benchmark execution concurrency.
Use `RBE_BENCH_JOBS=4` to try four jobs first. Do not use cache-bypass flags,
nonces, or a full-project forced rebuild for this experiment.

Record dashboard external and internal transfer deltas separately around
each run. Compare client analysis time, RSS, remote hits/misses, worker input
fetching, queue time, and actual execution time. Cache-only profiles isolate
warm-cache lookup work without paying for another remote compilation.

Follow-up work is provider-level dependency metadata sharing and a reusable
compiled audit tool. Bazel's performance guidance warns that repeatedly
flattening overlapping depsets can produce quadratic analysis work:
https://bazel.build/rules/performance.
Do not narrow SDK inputs solely from explicit source imports: the audit imports
`Lean`, ordinary modules implicitly import `Init`, and imported prebuilt
modules can require additional SDK artifacts.

These changes have been checked for patch application and script behavior.
Live Bazel analysis, hosted Lean compilation, and measured performance changes
remain to be verified on the Ubuntu server.
