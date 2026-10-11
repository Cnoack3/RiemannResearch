# Bazel baseline

Bazelisk reads `.bazelversion`, which pins Bazel 9.2.0. Tomato's `rules_lean`
is pinned to commit `e3b343ff799554a1e1a1d158d4a96eac5cdaa3ea`.

From the repository root:

```sh
bazel build //:smoke
bazel build --nobuild //:RiemannResearch
bazel build //:RiemannResearch
```

`smoke` compiles the existing `RiemannResearch/Basic.lean` arithmetic check.
`--nobuild` resolves dependencies and analyzes targets without compiling project
sources. The full project target currently uses a glob and one compilation
action; changing a source invalidates that action. Smaller libraries with
explicit import dependencies are the next step for fine-grained caching.
That split must also preserve Lean module sidecar artifacts between targets.

The Lake extension reads the existing `lean-toolchain` and `lake-manifest.json`.
`bazel/lakefile.toml` lists only the project dependencies so bootstrap cannot
accidentally build the project. Keep its direct requirements synchronized with
the root Lake file. Transitive package labels come from the extension.

The first bootstrap downloads the Lean distribution and Mathlib's public cache,
then builds only the external modules listed in `source_build_targets` and their
import closures. These repository setup steps run locally, outside Bazel's
action cache. Update the target list when adding other external module imports.

The small upstream compatibility patch adds the pinned Lean 4.33.0-rc2 archive
checksums, passes through the same compiler options as the root Lake file, and
allows dependency bootstrap to select module targets instead of whole libraries.
Keep `BUILD.bazel`'s flags synchronized with those options.

MCP verification continues using Lake unchanged. Remote execution is not
configured.

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
