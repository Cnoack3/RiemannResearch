# Google RBE smoke setup

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
