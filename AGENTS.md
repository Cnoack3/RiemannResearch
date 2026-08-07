# RiemannResearch agent instructions

## Required workflow

- Treat this repository as the persistent source of truth for Lean research.
- Synchronize the clean `main` branch from `origin/main` before reading or editing.
- Search the project and Mathlib for existing declarations before proving a new result.
- Distinguish informal arguments from Lean kernel-verified proofs, and distinguish
  kernel-checked implications from unconditional solutions of the motivating
  research problem. A successful build proves the declaration's exact type; it
  does not prove any hypotheses appearing as inputs to that declaration.
- When Lean establishes that a user-supplied claim, inference, assumption, or
  definition is faulty or materially mismatched, lead the user-facing response
  with `## Lean found a problem`. State the exact faulty step, decisive Lean
  evidence or smallest counterexample, and the downstream conclusion that no
  longer follows. Never bury an established logical error in a summary or
  side-note.
- Do not mistake proof-search failure for refutation. A failed tactic, timeout,
  or unsolved goal is inconclusive unless Lean provides decisive evidence such
  as a contradiction, counterexample, type mismatch, or failed required
  condition. Clearly label any corrected theorem as different from the user's
  original claim.
- Save successful material proofs in the appropriate `RiemannResearch/` module
  and update `RiemannResearch/THEOREM_CATALOG.md` when adding a reusable
  theorem.
- Classify any theorem that represents a named research result but assumes
  unresolved domain-specific ingredients as a **conditional research
  reduction** in the theorem catalog. Do not hide that status behind the phrase
  “kernel checked.”
- For every conditional research reduction, maintain an explicit catalog
  ledger of its substantive propositional hypotheses. Mark each hypothesis
  `Open` until a project declaration supplies it; when it is discharged,
  replace `Open` with the fully qualified provider declaration and update the
  reduction to use that provider when practical.
- Ordinary variables, structures, typeclass instances, and hypotheses in
  general-purpose lemmas need not be treated as open research obligations.
  Track the domain-specific inputs standing between a conditional assembly
  theorem and its intended unconditional mathematical statement.
- Do not use `#print axioms` as evidence that a theorem is unconditional:
  it reports global axioms, not local hypotheses in the theorem's type.
- Move a result from the conditional section to the established section only
  after all cataloged research obligations are supplied by checked
  declarations and the resulting specialized theorem passes the full build.
- Verify edited files with the Lean tools and run `lake build` before checkpointing.
- Do not introduce `sorry`, `admit`, project-local `axiom` declarations, or `unsafe` declarations.
- After a successful material change, checkpoint and push it to `origin/main`; report the commit SHA.
- Never force-push, rebase, stash, create merge commits, discard local work, or pull into a dirty or diverged tree. Stop and report the condition instead.
- Treat `workspace_reset` as a destructive fail-safe only. First preview it without a token, show exactly what would be discarded, obtain explicit user permission in the current chat, and only then invoke it with the returned confirmation token. Never run it automatically.

## Module architecture

- Organize modules by mathematical concept or theorem family; do not create one file per theorem.
- Put reusable declarations in the lowest general-purpose namespace whose concepts occur in their statements. Do not leave generic infrastructure trapped in an application-specific namespace.
- Keep application modules focused on application-specific definitions, hypotheses, and theorem assembly.
- Split a module when it contains independently reusable concepts. Treat roughly 300--500 lines as a review signal, not a rigid limit.
- Preserve declaration names during refactors when practical; otherwise provide compatibility aliases or re-export modules.
- Prefer focused Mathlib imports over `import Mathlib` in persistent library modules.
- Keep the import graph acyclic and directed from general infrastructure toward specialized applications.
- Keep `RiemannResearch.lean` as the project export surface and update it whenever adding or moving an exported module.
- Update `RiemannResearch/THEOREM_CATALOG.md` whenever reusable declarations
  are added or moved, and whenever a conditional theorem gains, changes, or
  discharges an open research obligation.
- Prefer a separate checkpoint for structural refactors and new mathematical results when practical.

## Project commands

- Full build: `lake build`
- Verify one file: `lake env lean path/to/File.lean`
- Search text: `rg "pattern" RiemannResearch`
