# Bazel baseline

Bazelisk reads `.bazelversion`, which pins Bazel 9.2.0. Atvrager's `rules_lean`
is pinned to commit `2cf9d007003ff73374e0082a82342e3f4723fc65`.

From the repository root:

```sh
bazel build //:smoke
bazel build //RiemannResearch:Basic
bazel build //RiemannResearch/Analysis:AbelCoboundary
bazel build --nobuild //:RiemannResearch
bazel build //:RiemannResearch
```

`smoke` compiles the existing `RiemannResearch/Basic.lean` arithmetic check.
`--nobuild` resolves dependencies and analyzes targets without compiling project
sources. Each Lean source has a named target and its own compilation action.
Each source directory has a short `BUILD.bazel` that calls `lean_modules()`.
The shared macro derives exact dependencies from the watched import index.
Parsed imports determine the exact transitive artifact inputs, including
Lean module sidecars. A source edit invalidates its action and affected importers.

Recursive globs stop at nested Bazel packages. A new directory without a BUILD
file is covered by its nearest ancestor package, including the root fallback.
For example, `RiemannResearch/NewArea/Foo.lean` initially has the target
`//RiemannResearch:NewArea.Foo`. Adding `NewArea/BUILD.bazel` changes its target
to `//RiemannResearch/NewArea:Foo`; the import index updates dependencies.
Copy any existing three-line module BUILD file to give a new directory its own
package. `//:RiemannResearch` includes every project source, even if it is not
exported by `RiemannResearch.lean`.

Every project target sets `forbid_sorry = True`. The patched rule checks warnings
and compiled declaration types and bodies, including private module declarations.
It rejects `sorry` and `admit` even with `set_option warn.sorry false`.
Lean compilation checks proof terms; no executable `lean_test` is needed for this.
This is not a general axiom allowlist audit. MCP's source-policy audit and
publication gate continue unchanged.

The extensions read the root `lean-toolchain` and `lake-manifest.json`.
`MODULE.bazel` selects external source packages and module roots; their local
import closures become normal Bazel compilation actions. Mathlib and its
published dependency artifacts are prebuilt targets with complete import graphs.

When dependency pins change, update the archive SHA-256 values in
`MODULE.bazel`. Extend its package/module root lists when adding external
imports. Keep namespace mappings, module overrides, source directories, and
package compiler flags aligned with those dependencies. Keep `lean_modules.bzl`'s
compiler flags aligned with the root Lake file. A new Lean version may also
need its archive checksums added to the ruleset patch.

The upstream patch fixes consumer repository labels and version selection,
complete import closures, Lean 4.33 module outputs, and portable repository
contents. It also exposes selected source dependencies as per-module targets.
The checkout import index stays local. Only portable external repositories use
the shared repository contents cache.

MCP verification continues using Lake unchanged. An opt-in Google RBE smoke
profile is described in [RBE.md](RBE.md). Cloud provisioning and authentication
must succeed before that profile can run.

Validation covers `Basic.lean`, the 12 selected external source modules,
full-project analysis without compilation, incremental import fixtures, large
import closures and cycle rejection, concurrent source repository reuse, and a
70-module Mathlib cold fetch followed by fresh offline reuse. A fresh Bazel output
directory restored the smoke action from a stock HTTP cache without compiling.
Package-split validation covers the project smoke build, full-project analysis,
cross-package legacy/module imports, unpackaged fallback sources, addition of a
package, and rejection of normal, suppressed, private sorries and `admit`.
The full project compilation, private GCS reuse, and RBE have not been tested.

## Shared local repository caches

Bazel 9.2 provides two native repository caches. Workspaces using the same
`output_user_root` share these persistent locations:

- Downloaded archives: `{output_user_root}/cache/repos/v1`.
- Completed reproducible repositories: `{repository_cache}/contents`.

Run `bazel info output_user_root` on the Ubuntu server to locate them. No
additional service or authentication is required; the directories survive
reboots. Eligible completed repositories are shared through directory symlinks,
with native filesystem locks for concurrent readers and garbage collection.
The patched rules normalize fetched repositories into portable trees and mark
them reproducible. Keep any custom cache location outside the checkout.

`.bazelrc` explicitly retains completed repositories for 14 days after last use
and runs their garbage collection after 5 minutes idle. This is age-based
retention, not a 100 GiB size limit; it does not prune the downloaded-archive
cache or change Lake's separate cache budget.

The first Mathlib population downloads its public cache locally. Bootstrap uses
isolated temporary Home, Lake, and Mathlib cache directories. It retains only
compiled import bundles and deterministic metadata, then removes the temporary
state. Later workspaces can reuse the completed repository without repeating
bootstrap.

`.bazelrc` also enables experimental remote repository contents caching:

```bazelrc
startup --experimental_remote_repo_contents_cache
build --remote_download_outputs=minimal
```

Eligible completed repositories can use the configured remote cache as well.
Cached action outputs download when needed by local actions; outputs compiled
locally still occupy disk. Repository contents caching is experimental in
Bazel 9.2. The downloaded-archive cache remains separate.

## Private GCS cache on the Ubuntu server

`.bazelrc` uses `http://127.0.0.1:9090`. Stock
[bazel-remote](https://github.com/buchgr/bazel-remote) uses the existing HMAC key
to sign requests to GCS's S3-compatible XML API. Its objects live under
`gs://riemann_lean_cache/bazel/`, separate from Lake's artifacts. Bazel's native
Google credential flags use OAuth, so they cannot consume the HMAC JSON.

Run the following on the Ubuntu MCP server, from this checkout. This installs
the upstream Linux amd64 binary, verifies its published checksum, and prepares
the user service:

```sh
install -d "$HOME/.local/bin" "$HOME/.config/systemd/user"
install -d -m 700 "$HOME/.config/bazel-remote"
curl --fail --location \
  https://github.com/buchgr/bazel-remote/releases/download/v2.6.2/bazel-remote-2.6.2-linux-amd64 \
  --output "$HOME/.local/bin/bazel-remote"
printf '62e236bf8396e69396928e0d0c32062fbd5575f20fe55dc10a82eb791297e1a0  %s\n' \
  "$HOME/.local/bin/bazel-remote" | sha256sum --check
chmod 755 "$HOME/.local/bin/bazel-remote"
install -m 600 bazel/bazel-remote.config.example.yaml \
  "$HOME/.config/bazel-remote/config.yaml"
install -m 644 bazel/bazel-remote.service \
  "$HOME/.config/systemd/user/bazel-remote.service"
```

Edit `$HOME/.config/bazel-remote/config.yaml`: set the two HMAC fields from
`$HOME/.config/lean-gcs-cache/hmac.json`, and use your absolute home directory
for `dir`. Keep the edited file outside the checkout. The example bounds the
service's local buffer to 5 GiB; this is separate from Lake's existing budget.

Then enable startup without an interactive login and start the service:

```sh
sudo loginctl enable-linger "$USER"
systemctl --user daemon-reload
systemctl --user enable --now bazel-remote.service
curl --fail http://127.0.0.1:9090/status
bazel build //:smoke
```

The enabled user unit starts when Ubuntu boots; lingering keeps its user
manager active across logout. `Restart=always` restarts the cache after a crash.
No interactive Google login or MCP service changes are needed.

Backend uploads run asynchronously. Inspect
`journalctl --user -u bazel-remote.service` for successful S3 uploads and confirm
objects under the bucket's `bazel/` prefix before treating it as warmed. A local
cache hit alone does not prove GCS reuse.

For temporary offline builds, pass `--remote_cache=`. A git-ignored
`.bazelrc.local` can override the endpoint for another machine.
