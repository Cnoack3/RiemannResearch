# RiemannResearch agent instructions

## Branch scope

- `main` is the RH-focused development branch. Add Lean modules here only when they
  are part of the RH program or have a concrete identified RH consumer.
- The complete Serre II development at commit
  `0d8199086f808671b3f61460fab7864b46915bce` is preserved on
  `serre-ii-archive-20260904`. Do not reconstruct or publish Serre II modules on
  `main`; future Serre II work requires an explicitly branch-aware workspace.

## Mandatory server verification before publication

- The private repository uses GitHub for source hosting. GitHub-hosted CI is
  unavailable because its runner quota is exhausted; it has been broken since
  setup. Do not rely on it, wait for it, rerun it, or propose paid runners as
  the verification path. This is the user's explicit requirement, reaffirmed
  2026-10-09.
- Verify every Lean source or dependency change on the user's Lean server
  through the Lean plugin before pushing. Publish only through
  `agent_workspace_checkpoint` with push enabled, after its server source
  audit and required Lean validation succeed. If publication integrates newer
  `main` changes, the integrated source must pass server validation before
  that source is pushed.
- A queued job, an accepted request, an isolated successful proof snippet,
  a source scan, or a GitHub commit is not evidence that the final project
  changes passed verification. Wait for the checkpoint's terminal successful
  result and inspect its validation scope and publication result.
- If server verification fails, times out, is interrupted, or is unavailable,
  retain the work and block publication. Do not bypass the gate with direct
  `git push`, GitHub file/commit APIs, an unverified integration, or a fallback
  to hosted CI. Report the blocker and the exact verification status.
- Report the server verification job, validation scope, and published commit
  for Lean changes. Documentation-only checkpoints may skip Lean compilation;
  explicitly describe them as documentation changes, never as freshly checked
  mathematical results. A server check of a snippet does not certify unchanged
  repository modules or an entire repository build.

## Mathematical and verification policy

- For RH research, keep complete exact identities as the primary results.
  Preserve all signed summands, boundary terms, and norm-square remainders.
  When an estimate is useful, give the full equality first and identify the
  terms being estimated. Do not treat a lossy bound as closing an RH argument.
  This is the user's explicit research preference, reaffirmed 2026-09-29.
- Treat this repository as the persistent source of truth. A successful Lean
  check verifies a declaration's exact type, not the truth of hypotheses in
  that type or an informal interpretation of it.
- Search declarations with `lean_local_search` before proving anything new.
  Follow with focused declaration lookup, Loogle, or LeanSearch as needed.
  Batch `#check` for a short list of candidates instead of opening source files
  merely to learn their signatures. Use bounded `agent_workspace_search_files`
  only when declaration search and filename filtering are insufficient.
  Never read all of `RiemannResearch/THEOREM_CATALOG.md` for discovery; it is a
  human-readable publication and research-obligation ledger.
- Do not mistake a failed tactic, timeout, or unsolved goal for a refutation.
  When Lean decisively exposes faulty or mismatched user logic, lead with
  `## Lean found a problem`, the exact evidence, and the conclusion affected.
- Never persist `sorry`, `admit`, project-local `axiom`, or `unsafe`
  declarations.
- For important assumptions, distinguish ordinary Mathlib foundations from
  unresolved domain-specific hypotheses. `#print axioms` does not report local
  hypotheses in a theorem's type.

## Bazel verification default

- Default all acceptance checks to Bazel with `--config=buildbuddy`. The queued
  snippet, file-check, full-build, and checkpoint tools select this backend.
  Do not silently retry a failed Bazel check through Lake.
- This is an experimental migration. Select `backend="lake"` on a queued tool
  for an explicitly requested legacy check. The server environment flag
  `LEAN_VERIFICATION_BACKEND=lake` restores the old default. Record which backend
  verified the result. Jobs record their backend at submission; old jobs retain
  their original Lake path.
- Every new directory containing Lean sources, including its intermediate
  parents, must have `BUILD.bazel` with `lean_modules()`. The server generates
  absent package files after patches and before verification. Keep these files
  in the same checkpoint as the source. Use
  `python3 tools/bazel_verification.py --check` to audit coverage, or `--fix` to
  create missing package files. Preserve existing custom package definitions.
- LSP diagnostics, goals, tactic attempts, and axiom exploration remain editor
  tools. They do not replace queued Bazel acceptance or the publication gate.
  If the installed server lacks the backend fields/default, report that the
  migration is not deployed; do not label an old Lake result as Bazel-verified.

## Efficient isolated workflow

- Retain the active workspace token and absolute project root across turns of
  an ongoing task. Pass the token directly to subsequent workspace tools; do
  not call `agent_workspace_open` again merely to confirm connectivity or reuse
  an already active workspace. Create a new isolated workspace only when a new
  task actually needs one. Reopen a retained token to resume an archived clone
  or when the server explicitly reports that restoration is needed. Old tokens
  remain resumable after server updates.
- Pass absolute paths beneath its `project_root` to Lean tools. Use
  `agent_workspace_run_code` for a coherent ephemeral proof candidate. Inspect
  goals or diagnostics after failure rather than checking every tactic
  separately. When several local tactic repairs are plausible in an existing
  file, send 2--5 alternatives together with `lean_multi_attempt`.
- Batch related declaration checks and proof candidates into coherent
  submissions, and batch independent read-only searches and file reads.
  Independent Bazel workspaces may verify concurrently. Each parallel agent
  must own its workspace; allow at most one queued or running job per workspace.
  A timeout does not free that workspace: recover the job status before
  submitting more work there. Do not repeat a
  connectivity smoke test when a successful task-relevant operation already
  establishes access.
- Read only relevant source ranges. Use targeted diagnostics or verification
  during development. Diagnostics are compact by default; request full details
  only when the bounded result omits evidence needed to repair the proof.
- Bazel jobs bypass the legacy global worker queue. By default
  `LEAN_BAZEL_JOB_WORKERS=0` imposes no global Bazel job cap; a positive value
  enables an optional cross-process cap. Lake retains `LEAN_JOB_WORKERS`
  (default 1, maximum 4). Same-workspace operations and publication stay locked.
  RBE offloads build actions, but Bazel analysis still consumes local resources.
  Submit once
  and poll `agent_workspace_job_status` no sooner than `retry_after_seconds`;
  never resubmit a pending job. Running status reports the current phase, Lake
  task percentage when available, and a rough task-count ETA.
- Report workspace-opening request time, queue/polling delay, and the server's
  reported verification duration separately. A request round trip is not a
  measurement of kernel proof-checking time. Do not attribute a delay to disk,
  cache, networking, or Lean startup without supporting timing evidence.
- `agent_workspace_checkpoint` audits and validates the entire unpublished
  delta from the workspace base before commit and serialized publication.
  It skips Lean only when that delta contains no Lean source or dependency
  changes. Otherwise Bazel incrementally builds `//:RiemannResearch` with
  `--config=buildbuddy`, including every project package and unexported source;
  unchanged artifacts are reused. Source
  changes during validation block publication. Integrated source is audited
  and validated again before pushing its exact commit. `lean_build` is the
  explicit incremental full-project validation; do not run it immediately
  before checkpoint. After
  an intentional `lakefile.toml` change, queue `agent_workspace_update_deps`
  once and wait for it before validation.
- The following native dependency/cache details apply to the explicit Lake
  legacy backend and editor exploration. Bazel uses the existing repository
  configuration and BuildBuddy cache without changing resource/quota settings.
  Dependency artifacts are shared read-mostly. Native project artifacts use a
  shared content-addressed cache backed by private GCS storage. Each clone has
  its own writable project build directory, restored through native Lake
  artifacts and cleaned after successful verification when no editor uses it.
  Native cache writes and pruning share an exclusive reentrant lease; its
  retention budget is 100 GiB, excluding dependency artifacts and active
  workspace links. One managed Lake worker runs by default, with at most eight Lean
  threads; publication remains serialized. Before each build, a protected
  `lake exe cache get` preflight fills available binary artifacts. If that
  preflight is incomplete, builds for the same dependency key serialize while
  Lake fills missing artifacts, preventing shared-cache corruption. The exact
  environment is keyed by `lean-toolchain`, `lakefile.toml`, and
  `lake-manifest.json`.
- Automatic cleanup archives only old clean published or unchanged clones.
  Dirty trees and unpublished commits are retained. Reopening a token restores
  an archived clone; Lean processes restart on demand.

## Persistence and publication

- Save reusable material results in an appropriate `RiemannResearch/` module.
  Update `RiemannResearch.lean` when exporting a new module.
- Track provenance best-effort when formalizing material from an external
  source. Add a nearby module docstring or declaration comment with a stable
  bibliographic reference or URL and, when known, the theorem, section, or page
  being adapted. One module-level reference may cover a coherent sourced
  development; cite declarations separately when their sources differ.
- Say what the reference supports (for example, the statement, proof strategy,
  or terminology). Use `Source: user-provided argument` when that is all that
  is known. Do not describe uncited or independently developed formalization as
  mathematically novel merely because no prior source was found.
- Update the theorem catalog when a reusable declaration is added, moved, or
  changes status. Read and edit only the relevant catalog section.
- Classify a named research result with unresolved substantive hypotheses as a
  **conditional research reduction**. List each domain-specific obligation as
  `Open` until a checked provider declaration discharges it. Move the result to
  the established section only when all obligations are discharged and the
  specialized theorem passes checkpoint.
- Publish only through `agent_workspace_checkpoint` with push enabled. Report
  the published commit after the queued job succeeds.
- Never force-push, rebase, stash, create merge commits, or discard local work.
  Reset is a destructive fail-safe: preview the exact plan, obtain explicit
  permission, then submit its confirmation token.

## Module architecture

- Before editing, inspect filenames and outlines in the matching subject
  directory. Extend a module only when the declaration belongs to its existing
  concept; otherwise create a descriptively named sibling module. Never use a
  catch-all scratch or program-checks file for unrelated results.
- New modules must live in a named subject directory and be exported from
  `RiemannResearch.lean`.
- Put reusable declarations in the lowest general-purpose namespace appearing
  in their statements; keep application modules focused on assembly.
- Use focused Mathlib or project-module imports; exact `import Mathlib` is
  forbidden in every new or modified module. Keep the import graph acyclic.
- Follow import-what-you-use (IWYU): import the narrow owning modules for
  directly used declarations, including required tactics, notation, instances,
  and attributes. Avoid relying on an unrelated application module to bring
  these into scope transitively. An import with no visibly named declaration
  can still be required for elaboration.
- Keep reusable definitions and general lemmas below their application and
  theorem-assembly modules. Split a mixed module when identified consumers can
  import only the reusable part.
- Judge dependency cleanups by transitive import paths and the modules affected
  by an edit, accounting for alternate paths. Removing an already-implied import
  does not itself improve cache isolation. Distinguish graph reductions from
  measured build-time/cache-hit gains, and use the existing server validation
  gate to check consumers after import changes.
- Split by mathematical responsibility, not an arbitrary line count. File size
  is a review signal; a long file is appropriate when it contains one cohesive
  complex theorem and its tightly coupled support.
- This repository has no external compatibility contract. During refactors,
  update every in-repository import, reference, reverse dependency, catalog
  entry, and document that is affected, then remove the obsolete module,
  declaration, or name. Do not add import-only relocation modules, aliases,
  deprecated forwarding declarations, duplicate theorem spellings, or other
  compatibility wrappers unless the user explicitly requests compatibility
  for a concrete external consumer. Prefer separate checkpoints for structural
  refactors and new results.

## Useful commands

- Ephemeral candidate: `agent_workspace_run_code`
- Declaration discovery: `lean_local_search`, then focused Lean search tools
- Targeted file verification: `lean_verify` or diagnostics on an absolute path
- Intentional dependency refresh: `agent_workspace_update_deps`
- Standalone incremental validation: `lean_build` when no checkpoint follows
- Final acceptance and publication: `agent_workspace_checkpoint`

Local cost telemetry is written as bounded JSON Lines to
`~/.local/state/lean-agent-workspaces/metrics.jsonl`; it records durations,
response sizes, queue polling, and cache/build events without proof text or
workspace tokens.


