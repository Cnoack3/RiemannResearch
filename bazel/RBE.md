# RBE smoke setup

## BuildBuddy Personal trial

`bazel build --config=buildbuddy` selects BuildBuddy's hosted executors and
artifact cache. It also sends build events to the authenticated BuildBuddy
organization so its invocation page can show execution and transfer statistics.
Ordinary builds keep the GCS cache. MCP verification continues using Lake.
Use either `--config=buildbuddy` or `--config=rbe`, not both.

The BuildBuddy profile uses the existing pinned Ubuntu 24.04 Linux x86-64
platform, two jobs, minimal output downloads, and remote execution only.
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
`--remote_accept_cached=false` bypasses remote cache hits but does not force
locally up-to-date actions to rerun. The nonce changes the probe action's key
so repeated probes exercise execution without cleaning the workspace.

Then test actual Lean compilation and the compiled-sorry audit:

```sh
bazel --output_base="$HOME/.cache/bazel-buildbuddy-smoke" build \
  --config=buildbuddy --remote_accept_cached=false //:smoke
```

The smoke target imports `Mathlib.Tactic.NormNum`. Its first run may fetch
dependency repositories locally and upload the Lean SDK and imported artifacts
to BuildBuddy. It does not build the full RiemannResearch target.

Test remote cache reuse from a second output base, allowing cached results:

```sh
bazel --output_base="$HOME/.cache/bazel-buildbuddy-warm" build \
  --config=buildbuddy //:smoke
```

Compare the linked invocation pages: remote actions on the forced run, cache
hits on the fresh repeat, and uploaded/downloaded bytes. Stored artifact size is
not the same as transfer per invocation. Keep the account on the free Personal
plan; its public pricing does not specify exactly how internal executor traffic
counts toward the advertised transfer allowance.

Validation: Bazel 9.2.0 accepted the profile, and action analysis selected the
pinned Linux platform for the probe and Lean smoke action, including its
compiled-sorry audit. Live hosted execution remains unverified: the authoring
environment could not resolve `remote.buildbuddy.io`. Run the probe above on
the Ubuntu server before treating the executor as working.

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
  --remote_accept_cached=false //:smoke
```

The first command tests the executor without fetching Mathlib or uploading the
Lean toolchain. Look for an actual `remote` process in the build summary.
`remote cache hit` alone does not prove execution. The second command tests Lean
and its compiled-sorry audit. Repository fetching and analysis still run locally;
Lean compilation and its audit run remotely. The first Lean test must upload its
SDK and imported artifacts to the execution service's CAS. Later actions reuse
those blobs.

The RBE profile uses its execution service's CAS and action cache, rather than
the separate `bazel-remote` GCS backend. A cached repeat should then be tested
from a fresh Bazel output base, without `--remote_accept_cached=false`.

Validation so far covers Bazel flag parsing, action analysis, and selection of
the Linux execution platform. Live Google RBE execution, instance access, and
persistent machine authentication remain untested.
