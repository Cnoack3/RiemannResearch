# Complete Pareto approximation-to-RH Lean bridge
Date: 16 September 2026

## Conclusion

The implication from approximation of the constant by finite legal Pareto packets to Mathlib's actual `RiemannHypothesis` is fully proved. The current repository already contained the core Mellin separation and reflection proof. This continuation adds explicit small-error, sequential, mean-one variance, and density entry points.

The earlier chat statement that the forward bridge was absent from Lean was outdated relative to the repository inspected in this turn.

This is a proof of an implication. It does not construct the approximating sequence or prove RH unconditionally.

## Exact endpoint

Mathlib defines:

```lean
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ), riemannZeta s = 0 →
    (¬ ∃ n, s = -2 * (↑n + 1)) → s ≠ 1 → s.re = 1 / 2
```

All declarations below use namespace `RiemannResearch.RH.Pareto`.

The sequential entry point is:

```lean
theorem riemannHypothesis_of_legal_paretoError_tendsto
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (g : ℕ → ℕ → ℝ) (hg : ∀ j, g j ∈ legalSeedSpan A)
    (hlim : Filter.Tendsto (fun j => paretoError (g j))
      Filter.atTop (nhds 0)) : RiemannHypothesis
```

For the requested two-seed family take `A = {2, 3}`. Each packet is a finite real linear combination of the generators `dilation m (residue a)`, with positive integer m and a in A. Every positive integer dilation is allowed.

The error is the complete infinite Pareto sum:
`paretoError g = ∑ n≥1, (1 - g(n))² / (n(n+1))`.
Index zero has weight zero. Finite legality supplies boundedness and summability internally.

## Proved chain

1. `hilbertOne_mem_legalClosure_iff_paretoError`: arbitrarily small full Pareto error is equivalent to membership of the target in the actual legal Hilbert closure.
2. `paretoMellinContinuous`: the actual integral defines a continuous real-linear, complex-valued functional for Re(s)>1/2, with the proved Cauchy bound.
3. `paretoMellin_generator_zeta`: its value on every generator is
   ζ(s)/s · m^(1-s) · (1-a^(1-s)), for s≠1.
4. `paretoMellin_zero_on_legalClosure_of_zeta`: a hypothetical zeta zero annihilates the entire closed legal space.
5. `paretoMellin_one`: the target has transform 1/s, which is nonzero in that half-plane.
6. `zeta_ne_zero_of_hilbertOne_mem_legalClosure`: target membership therefore excludes every zeta zero with Re(s)>1/2 and s≠1.
7. Zeta reflection and `RiemannResearch.RH.riemannHypothesis_iff_strip_zeros_on_line` discharge the remaining strip, boundary, and trivial-zero details.
8. `riemannHypothesis_of_hilbertOne_mem_legalClosure` concludes Mathlib's actual RH.

No Nyman–Beurling theorem is inserted as an assumption: this is the direct Mellin proof of the needed implication.

## Added entry points

In `RiemannResearch/RH/ParetoLegalApproximationClosure.lean`:
- `riemannHypothesis_of_legal_paretoError`
- `riemannHypothesis_of_legal_paretoError_tendsto`
- `riemannHypothesis_of_legal_meanOne_variance_tendsto`

In `RiemannResearch/RH/ThresholdRiemannHypothesis.lean`:
- `riemannHypothesis_of_legalClosure_eq_top`

The mean-one version assumes finite legality, mean exactly one for each packet, and full Pareto variance tending to zero. It proves the error identity using the actual summability supplied by finite legality.

## Verification and remaining mathematical input

Lean checked the core bridge, its exact RH endpoint, and the added approximation proofs. The inspected axiom dependencies are only `propext`, `Classical.choice`, and `Quot.sound`; no project axiom or unfinished proof is used.

The approximation property itself remains an input. Neither existence of successful packets nor the converse RH-to-two-seed approximation is established by this continuation.
