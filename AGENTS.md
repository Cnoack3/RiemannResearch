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

## Project commands

- Full build: `lake build`
- Verify one file: `lake env lean path/to/File.lean`
- Search text: `rg "pattern" RiemannResearch`
