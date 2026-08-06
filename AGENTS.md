# RiemannResearch agent instructions

## Required workflow

- Treat this repository as the persistent source of truth for Lean research.
- Synchronize the clean `main` branch from `origin/main` before reading or editing.
- Search the project and Mathlib for existing declarations before proving a new result.
- Distinguish informal arguments from Lean kernel-verified proofs.
- Save successful material proofs in the appropriate `RiemannResearch/` module and update `RiemannResearch/THEOREM_CATALOG.md` when adding a reusable theorem.
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
- Update `RiemannResearch/THEOREM_CATALOG.md` whenever reusable declarations are added or moved.
- Prefer a separate checkpoint for structural refactors and new mathematical results when practical.

## Project commands

- Full build: `lake build`
- Verify one file: `lake env lean path/to/File.lean`
- Search text: `rg "pattern" RiemannResearch`
