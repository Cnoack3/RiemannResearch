# Private GCS artifact cache

Native Lake caching for the verification service, pinned to
`leanprover/lean4:v4.33.0-rc2`. Public configuration uses project
`project-c5cfd87b-fbe8-47ea-9d0` and private bucket `riemann_lean_cache`.
Source installation alone leaves the integration inactive.

## Activate on the existing WSL server

Run as the verifier Unix user, `cri_2025`. The already working HMAC file is
`/home/cri_2025/.config/lean-gcs-cache/hmac.json`, outside Git:

```json
{"type":"gcs_hmac","access_id":"YOUR_ACCESS_ID","secret":"YOUR_SECRET"}
```

No credential value belongs in a tracked file or shell command. The bridge
requires this file to belong to its service user and have mode `0600`.
It uses Python's standard library; there is no installer or pip dependency.

First pull the infrastructure commit and start only the cache service:

```bash
cd /home/cri_2025/lean-projects/RiemannResearch
git pull --ff-only
mkdir -p -m 700 /home/cri_2025/.cache/lean-native-artifacts /home/cri_2025/.local/share/lean-gcs-cache/tmp
sudo install -m 644 tools/lean-gcs-cache/lean-gcs-cache.service /etc/systemd/system/lean-gcs-cache.service
sudo systemctl daemon-reload
sudo systemctl enable --now lean-gcs-cache.service
curl --fail --silent --show-error http://127.0.0.1:8765/readyz
```

Then run the isolated acceptance test, before enabling remote caching in the
verifier. It builds three tiny modules, never the research project. It requires
actual cold compilation, zero compilation on a warm build, zero compilation
in a fresh workspace with an empty local cache, and rebuilding only the changed
import and its consumer. It writes small objects under a unique smoke namespace.

```bash
python3 tools/lean_gcs_smoke_test.py \
  --repo "$PWD" \
  --config "$PWD/tools/lean-gcs-cache/lake.toml" \
  --output /home/cri_2025/.local/share/lean-gcs-cache/acceptance.json
```

After it passes, when queued/running verifier jobs have finished:

```bash
sudo mkdir -p /etc/systemd/system/lean-tunnel.service.d
sudo install -m 644 tools/lean-gcs-cache/60-lean-gcs-cache.conf /etc/systemd/system/lean-tunnel.service.d/60-lean-gcs-cache.conf
sudo systemctl daemon-reload
sudo systemctl restart lean-tunnel.service
```

The queued workers run inside that service. Subsequent plugin builds return
`dependency_cache.remote_artifacts` with restored, missing, uploaded and
already-uploaded package lists. A full project build is unnecessary for setup.
The real acceptance result must pass before claiming remote reuse works.

## Build behavior

The managed full, affected-module, checkpoint and integration build paths,
plus the legacy checkpoint path, call `lean_remote_cache.run_cached_build`.
It preserves dependency preflight, fallback locks, target selection and
verification/publication audits. The existing mathlib cache preparation remains.
Direct `lake env lean` proof snippets and LSP checks retain their checking path.

Before a build, the helper fetches merged mapping indexes and runs native
`lake cache add` to register remote artifacts lazily. The requested build runs
with `-o` to collect native input/output hashes. After success, `lake cache put`
uploads root artifacts and outputs from dependencies used by those targets.
Collecting dependency mappings replays the same already successful target
request with `--package`. Daily local receipts skip unchanged uploads and replay.
Failed builds never upload mappings. Cache transport, authentication or integrity
failures stop the enabled verification path by default.

`lean_gcs_bridge.py` listens only at `127.0.0.1:8765`. Lake's S3 uploads use the
dummy `LAKE_CACHE_KEY=loopback:unused`. Only the bridge reads the private HMAC
file and signs Cloud Storage XML requests over verified TLS. Lean receives no
GCP credentials. The bridge implements the `a0` artifact and `r0` mapping paths,
SHA256 validation, immutable artifact deduplication and generation-conditioned
merges of successful partial mappings. It does not change bucket IAM.

Remote objects live under `lean-cache/v1`, isolated by project namespace,
toolchain/platform and exact dependency configuration. Source/import/options
hashes remain Lake's responsibility. A mapping index retains previous successful
inputs and is limited to 128 MiB. Artifact objects are limited to 2 GiB. Do not
expire artifacts still referenced by an index; rotate namespaces for retention.

## Persistence and maintenance

The systemd service starts at boot. Bucket objects, the home-directory local
artifact cache, service settings and the private HMAC file survive restarts.
HMAC requests do not use an expiring OAuth login or require browser
reauthentication. Revoking the key or removing its permissions still stops
access. Rotate credentials by replacing the private JSON and restarting
`lean-gcs-cache.service`; no source or cache-layout change is needed.

To disable when verification is idle, remove only the installed
`60-lean-gcs-cache.conf`, reload systemd and restart `lean-tunnel.service`.
With `LEAN_REMOTE_CACHE_URL` unset, both original build paths are unchanged.
No local or remote artifacts are deleted.

## Offline checks

```bash
python3 -m unittest discover -s tools/tests -v
python3 tools/test_agent_workspaces.py
python3 tools/test_verification_jobs.py
```

These exercise fake Lake commands, in-memory storage, XML HTTP fixtures,
concurrent mapping updates, checksums, signing against a curl reference, failure
handling and verifier regressions. They are not real Lean/GCS acceptance.

Protocol references:

- [Pinned Lake cache configuration](https://github.com/leanprover/lean4/blob/v4.33.0-rc2/src/lake/Lake/Config/Cache.lean)
- [Pinned Lake CLI](https://github.com/leanprover/lean4/blob/v4.33.0-rc2/src/lake/Lake/CLI/Main.lean)
- [Cloud Storage HMAC keys](https://cloud.google.com/storage/docs/authentication/hmackeys)
