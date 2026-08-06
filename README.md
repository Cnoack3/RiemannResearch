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
- built with the pinned toolchain and dependencies; and
- committed to Git and, when requested, pushed to the private remote.

## Layout

- `RiemannResearch/RH/`: zeta-function and RH-equivalent formulations
- `RiemannResearch/OperatorTheory/`: spectral and operator-theoretic foundations
- `RiemannResearch/NoncommutativeGeometry/`: C*-algebras and spectral triples
- `RiemannResearch/F1/`: field-with-one-element constructions
- `RiemannResearch/AlgebraicGeometry/`: scheme-theoretic foundations
- `RiemannResearch/THEOREM_CATALOG.md`: human-readable declaration index

## Reproducibility

`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` pin the
environment. Run `lake build` from the repository root to verify the complete
library.
