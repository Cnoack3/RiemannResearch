# RiemannResearch agent instructions

## Branch scope

- `main` is the RH-focused development branch. Add Lean modules here only when they
  are part of the RH program or have a concrete identified RH consumer.
- The complete Serre II development at commit
  `0d8199086f808671b3f61460fab7864b46915bce` is preserved on
  `serre-ii-archive-20260904`. Do not reconstruct or publish Serre II modules on
  `main`; future Serre II work requires an explicitly branch-aware workspace.

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
- Long builds, updates, and checkpoints use a bounded worker queue. Submit once
  and poll `agent_workspace_job_status` no sooner than `retry_after_seconds`;
  never resubmit a pending job. Running status reports the current phase, Lake
  task percentage when available, and a rough task-count ETA.
- `agent_workspace_checkpoint` performs the source audit and change-aware
  validation before commit and serialized publication. It skips Lean for
  documentation-only changes and otherwise builds changed modules plus local
  reverse dependents; dependency configuration changes and structural module
  removals trigger full validation. `lean_build` is the explicit incremental
  full-project validation; do not run it immediately before checkpoint. After
  an intentional `lakefile.toml` change, queue `agent_workspace_update_deps`
  once and wait for it before validation.
- Dependency artifacts are shared read-mostly. Each clone has its own writable
  project build directory, seeded by exact commit and dependency environment.
  Up to two isolated jobs may build concurrently, each with at most eight Lean
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
