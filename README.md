# RiemannResearch

Persistent, kernel-checked Lean research library focused on the Riemann
hypothesis and related analytic, spectral, operator-algebraic, and geometric
approaches.

## Source of truth

The `.lean` files in this repository are the mathematical record. Chat
conversations may propose work, but a result belongs to the library only after
it has been:

- saved in a project module;
- accepted by Lean;
- checked for placeholders and project-local axioms;
- built with the pinned toolchain and dependencies;
- committed to Git; and
- automatically pushed to the configured private remote.

## Layout

- `RiemannResearch/RH/`: zeta-function and RH-equivalent formulations
- `RiemannResearch/OperatorTheory/`: spectral and operator-theoretic foundations
- `RiemannResearch/NoncommutativeGeometry/`: C*-algebras and spectral triples
- `RiemannResearch/F1/`: field-with-one-element constructions
- `RiemannResearch/AlgebraicGeometry/`: scheme-theoretic foundations
- `RiemannResearch/THEOREM_CATALOG.md`: human-readable declaration index

## Reproducibility

`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` pin the
environment. Run `lake build RiemannResearch --quiet` from the repository
root to verify the project library and its transitive imports. Lake stores
compiled artifacts under `.lake`; subsequent builds traverse the dependency
graph but rebuild only stale modules and their affected dependents.

## Automatic synchronization

On the first edit of a clean working tree, the restricted workspace connector
fetches `origin/main` and permits only a fast-forward update. A verified
checkpoint incrementally builds the project library, commits approved files,
and pushes the resulting commit to the private `main` branch by default. It refuses dirty-tree
pulls, merge commits, rebases, force-pushes, unexpected remotes, and unexpected
branches.
