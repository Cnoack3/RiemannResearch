# Minimal seeds and balanced arithmetic coordinates: verification scope

Source: the conversation and
`RH_Minimal_Seeds_Canonical_Basis_and_Arithmetic_Charge_20260914.md`.
The statements below use the actual Pareto Hilbert space with weights
`1 / (n * (n + 1))`, positive integer dilations, and finite signed legal packets.

## Established structural results

- `twoSeedAnnihilatorDefects_injective`: the pair of adjoint defects embeds
  the two-seed annihilator into two copies of the full-remainder annihilator.
  No density or RH hypothesis is used.
- `balancedSelected_span_eq_twoSeedSpan`: selecting seed 2 when
  `m.factorization 2 ≤ m.factorization 3`, and seed 3 otherwise, preserves
  the original **finite** legal span exactly.
- The arithmetic decomposition, its uniqueness, finite balancing paths,
  explicit cuts, and continuous Möbius coordinate functionals are proved.
  `balancedCoefficientCLM_biorthogonal` supplies the actual biorthogonal
  provider, and the scalar-index family is linearly independent.
- `balancedCut_signal_ne_zero_iff` computes the target support exactly:
  for `m = 2^a * 3^b * u` with `u` positive and indivisible by 2 and 3,
  its coefficient is nonzero precisely when `μ(u) ≠ 0` and
  `a = b`, `a = b + 1`, or `(a,b) = (0,1)`.
- `balanced_finite_deletion_iff` proves the finite deletion criterion.
  `balanced_exists_minimal_iff_support_approximates` proves that an
  inclusion-minimal target family exists exactly when that nonzero support
  approximates the target. It does not assert that it does.
- `hilbertOne_mem_balancedWithoutFourth_iff` removes the concrete generator
  `R_12 - R_4` while preserving approximation of 1. The resulting closed
  span is nevertheless not the whole Hilbert space.

## Established obstructions and limiting statements

- `fullResidueSpan_not_cyclic` and its positive-distance theorem exclude
  **every** fixed finite full-remainder template, even with all positive
  integer dilations. Fixed mixtures of the two seeds are included.
- `integerSeed_explicit_distance_gap` proves the exact one-seed lower bound
  `1 / (1 + (2π / log a)^2)` for every integer `a > 1`.
- `two_finite_templates_optimal_of_full_density` states the precise
  conditional optimality of two fixed finite templates: full remainder
  density implies the two explicit seeds suffice, whereas every singleton
  finite template fails unconditionally.
- The actual local coefficients approach their Möbius values. Every rough
  squarefree dilation index is necessary. Restriction to squarefree
  dilations, or to squarefree allowed Ramanujan conductors, is impossible.
- Actual signed component charge escapes every fixed smooth cutoff.
  `twoSeed_roughComponent_energy_tendsto_atTop` proves that every nonzero
  Möbius rough component of any pointwise-successful legal sequence has
  full Pareto energy tending to infinity. The Hilbert-norm specialization
  and the obstruction to a continuous component projection are included.
- `balancedDictionary_no_series_representation_one` rules out every
  ordinary series representation of 1 using this dictionary, with any
  fixed coefficients and any enumeration. Approximating finite arrays
  need not be the partial sums of one fixed series.
- `finiteDilationFamily_distance_gap` gives the common-multiple atom
  obstruction for any fixed finite family of individual generators.

## Explicit remaining boundaries

1. `BalancedSupportThinning` is an **open proposition**, not an axiom or a
   proved theorem. It says that two-seed density implies approximation of 1
   using only the nonzero target support. Finite deletion does not prove it.
2. The classical RH-to-full-remainder-density implication still has no
   checked provider in this project (`PositiveResidueDensityFromRH`).
   Consequently, results phrased here under full density must not be
   reported as an unconditional Lean proof of the complete RH equivalence.
   This is an outstanding formalization obligation for a known classical
   theorem, distinct from the thinning conjecture.
3. The ancillary natural-density value `3/π²` in the source note is not
   formalized here. The index-by-index necessity statement is formalized.

No numerical experiments or uniform variance bounds are treated as proofs.
The development proves structural and conditional statements, not RH.

## Lean validation

All 26 modules pass with their own focused imports. An axiom audit of 28 main
results reports only `propext`, `Classical.choice`, and `Quot.sound`.
No `sorry`, `admit`, or project-local axiom was introduced. Substantive
hypotheses were inspected separately from the axiom lists; the open
propositions above are not supplied as proved providers.
