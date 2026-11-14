# Theorem 12.2: conditional-mean endpoint equivalences

Source: user-selected Theorem 12.2 in
`RH_Random_Prime_Powers_CRT_Multi_Range_2026-09-19.tex`, equations (1.4)--(1.8).

## Exact quantities

The objective is
`conditionalMeanSquare F = ∑' k, [2 / ((k+2)(k+3))] * cesaro F (k+1)^2`.
It is the energy of the mean, not the error relative to one.
The legal class is the algebraic finite residue span, with an exact head
`F n = 1` for `1 ≤ n ≤ Y`. Its infimum is the existing
`conditionalHeadMinimum Y`; the forced head mass is `Y/(Y+2)`.

The existing `legal_exists_normalized_synthesis` in
`RH/MultiRangeCompleteness.lean` shows that every member of the legal
span has a finite representation using the manuscript's normalized
fractional residues with conductors at least two. No completion or
index-dependent coefficient choice is substituted for finite legality.

| Paper statement | Lean proposition |
| --- | --- |
| (i) | Mathlib `RiemannHypothesis` |
| (ii) | `Pareto.ExactConditionalEndpoint` |
| (iii) | `Pareto.ZeroMeanExactConditionalEndpoint` |
| (iv) | `Pareto.LogarithmicConditionalHeads` |
| (iv), zero mean | `Pareto.ZeroMeanLogarithmicConditionalHeads` |

Here all displayed declarations lie under `RiemannResearch.RH`.
The logarithmic predicates use the actual `Tendsto` limit of
`log (1 + conditionalMeanSquare (F j)) / log (Y j)` and a single
cofinal sequence of finite legal functions. Positive head lengths are
explicit.

## Proved declarations without a classical RH-to-density premise

- `Pareto.zeroMeanConditionalHeadMinimum_eq`: the two infima coincide
  for every head length, including zero. Nonemptiness and boundedness
  below are proved before using the real infimum.
- `Pareto.exactConditionalEndpoint_iff_zeroMean`: (ii) iff (iii).
- `Pareto.logarithmicConditionalHeads_iff_zeroMean`: the two versions
  of (iv) are equivalent. A different distant repair can be chosen at
  each index with energy increase less than one.
- `Pareto.zeroMeanLogarithmicConditionalHeads_of_exactEndpoint`:
  (ii) implies the zero-mean version of (iv), with head lengths j+2
  and complete energies less than two.
- `Pareto.riemannHypothesis_of_logarithmicConditionalHeads`:
  (iv) implies actual Mathlib RH through the existing signed Mellin
  zero obstruction. No Nyman--Beurling hypothesis is used.
- `Pareto.riemannHypothesis_of_exactConditionalEndpoint`: (ii)
  implies actual RH.
- `Pareto.FiniteHeadRepair.exists_exact_head_approximants`:
  finite physical heads can be preserved exactly in norm-convergent
  finite legal approximants.
- `Pareto.hilbertLegalClosure_eq_top_of_one_mem`: constant-target
  membership gives full Pareto density, using the proved floor
  dilations and dense physical point vectors.
- `Pareto.conditionalHeadMinimum_eq_head_mass_of_dense` and
  `Pareto.exactConditionalEndpoint_of_one_mem`: density (or constant
  membership) gives precisely the forced-head infimum. A finite-support
  mean target, its actual Pareto preimage, exact-head repair, and
  continuity supply the proof.

Files:
`RH/ConditionalMeanExactEndpoint.lean`,
`RH/ParetoFiniteHeadRepair.lean`,
`RH/ConditionalMeanEndpointEquivalences.lean`.

The existing `conditionalMeanSquare_gt_head_mass` shows that no finite
witness attains the infimum when Y is positive. None of the new
statements asserts attainment.

## Conditional research reduction: full Theorem 12.2

`Pareto.exact_endpoint_equivalences` proves all four RH equivalences,
including the zero-mean version of (iv), with one explicit argument:

```lean
(hNB : StrongNymanBeurlingForward)
```

The proposition is defined literally as

```lean
RiemannHypothesis →
  hilbertOne ∈ hilbertLegalClosure (Set.Ici 1)
```

**Open formalization obligation:** supply a checked provider for this
discrete consequence of the published strong Nyman--Beurling theorem,
including the continuous-to-discrete transfer if that route is used.
The published input is Luis Baez-Duarte, "A strengthening of the
Nyman-Beurling criterion for the Riemann hypothesis",
https://arxiv.org/abs/math/0202141. That reference supports the classical
input; a citation does not certify a Lean proof.

The complete RH equivalence is conditional until this argument is
discharged. The new development supplies no unconditional witnesses and
does not prove RH. It introduces no project axiom or proof placeholder.
An axiom audit checks foundations separately from this explicit local
hypothesis. Server checkpoint validation, not this catalog, determines
the exact verified and published revision.
