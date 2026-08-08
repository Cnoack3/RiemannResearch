# RiemannResearch agent instructions

## Mathematical and verification policy

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

## Efficient isolated workflow

- Open one isolated workspace per task and retain its token. Reopen that token
  to resume an archived clone. Old tokens remain resumable after server updates.
- Pass absolute paths beneath its `project_root` to Lean tools. Use
  `agent_workspace_run_code` for a coherent ephemeral proof candidate. Inspect
  goals or diagnostics after failure rather than checking every tactic
  separately. When several local tactic repairs are plausible in an existing
  file, send 2--5 alternatives together with `lean_multi_attempt`.
- Read only relevant source ranges. Use targeted diagnostics or verification
  during development. Diagnostics are compact by default; request full details
  only when the bounded result omits evidence needed to repair the proof.
- Long builds, updates, and checkpoints use one FIFO worker. Submit once and
  poll `agent_workspace_job_status` no sooner than `retry_after_seconds`; never
  resubmit a pending job.
- `agent_workspace_checkpoint` performs the source audit, incremental project
  validation, commit, and serialized publication. `lean_build` performs the
  same incremental validation without publication; do not run it immediately
  before checkpoint. Dependency updates are not exposed to ordinary agents.
- Dependency artifacts are shared read-mostly. Each clone has its own writable
  project build directory, seeded by exact commit and dependency environment.
  Lake builds use at most four threads. If the shared Mathlib binary cache is
  incomplete, the queued build first runs `lake exe cache get`; if binaries are
  unavailable, one serialized source build fills the shared cache for all later
  agents using the same dependency key.
- Automatic cleanup archives only old clean published or unchanged clones.
  Dirty trees and unpublished commits are retained. Reopening a token restores
  an archived clone; Lean processes restart on demand.

## Persistence and publication

- Save reusable material results in an appropriate `RiemannResearch/` module.
  Update `RiemannResearch.lean` when exporting a new module.
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
- Split by concept before a file reaches 500 lines. Checkpoint rejects new
  modules over 500 lines and further growth of existing over-500-line modules.
- Preserve declaration names during refactors when practical. Prefer separate
  checkpoints for structural refactors and new results.

## Useful commands

- Ephemeral candidate: `agent_workspace_run_code`
- Declaration discovery: `lean_local_search`, then focused Lean search tools
- Targeted file verification: `lean_verify` or diagnostics on an absolute path
- Standalone incremental validation: `lean_build` when no checkpoint follows
- Final acceptance and publication: `agent_workspace_checkpoint`

Local cost telemetry is written as bounded JSON Lines to
`~/.local/state/lean-agent-workspaces/metrics.jsonl`; it records durations,
response sizes, queue polling, and cache/build events without proof text or
workspace tokens.
