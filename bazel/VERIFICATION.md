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
garbage collection after five idle minutes. Completed repository contents use
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

4. Leave `LEAN_VERIFICATION_BACKEND` and `LEAN_BAZEL_JOB_WORKERS` unset for
   Bazel with no global job cap. Remove an old backend or positive cap override
   if present, and restart the existing `lean-tunnel.service` when idle. If a
   systemd environment drop-in was edited, run `sudo systemctl daemon-reload`
   before the restart. Do not replace other service settings.
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
