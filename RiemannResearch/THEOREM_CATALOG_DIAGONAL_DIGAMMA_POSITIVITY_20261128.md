# Diagonal digamma positivity reduction (2026-11-28)

Source: `RiemannResearch/RH/CenteredMeanDigammaNegativeMass.lean`.

## Kernel-checked declarations

- `diagonalHeadNonnegative n` means
  `0 <= sectionCoordinate (n + 1) k` for every `1 <= k <= n`.
- `digammaDiagonalNegativeMass_eq_zero_iff n` proves that this finite sign
  condition is equivalent to exact vanishing of `digammaNegativeMassHead n n`.
- `riemannHypothesis_of_diagonalHeadNonnegative` proves that the condition for
  every `n` implies the repository's standard `RiemannHypothesis` predicate.

The declarations contain no `sorry`, `admit`, new axiom, or unsafe escape.
Their foundational audit reports only the inherited standard dependencies.

## Open arithmetic input

The repository does **not** prove

```lean
∀ n : ℕ, diagonalHeadNonnegative n
```

This universal finite sign theorem would settle RH through the original mean
ladder and its digamma recurrence. High-precision external computation found
the condition through `n = 50`, but that evidence is not imported as a Lean
proof. Global section positivity is false: at stage 11 the complete period
has a negative coordinate at `k = 9856`, outside the diagonal head.
