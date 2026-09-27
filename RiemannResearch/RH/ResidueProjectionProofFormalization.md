# Pareto projection proof: formalization coverage

Source: uploaded `Pasted markdown.md`, equations (1)–(44), 22 September 2026.

The proof is formalized through the existing Pareto Hilbert-space development and
the additions listed below. All norms are the complete infinite Pareto norms.
The formal result establishes the internal convergence equivalences and the
exact limiting defect; it does not prove that the defect is zero.

## Conventions

The manuscript's cutoff `N` corresponds to project stage `n = N - 1`:
`residueAtom i = g_(i+2)`, `finiteSpace n = span(g_2,...,g_(n+1))`, and
`projection n = F_(n+1)`. The manuscript's Schur data for adjoining `g_N`
have project index `N - 2`. `limitEnergy` is the manuscript's `D`.

Namespaces abbreviated below:

- **P**: `RiemannResearch.RH.Pareto`.
- **C**: `P.CoefficientStabilization`.
- **G**: `C.GramMobiusCorrection`.
- **S**: `C.ProjectionSchur`.
- **T**: `C.CorrectionTail`.
- **E**: `RiemannResearch.Analysis.ExhaustiveWalk`.
- **FG**: `RiemannResearch.Analysis.FiniteHilbertGram`.

## Equation coverage

| Manuscript | Coverage and precise declarations | Source status |
|---|---|---|
| Hilbert-space setup | `P.ThresholdHilbert` is real `lp` at exponent 2; `P.hilbert_norm_weighted_sq`, `P.hilbertSequence_range`, `P.hilbertSequence_injective` identify the complete weighted sequence space. `P.positiveWeight_tsum` and `P.hilbertOne_norm_sq` give the normalization. | Existing |
| (1) coordinate continuity and bound | `P.physicalEvaluationCLM` and `P.physicalEvaluationCLM_apply` are continuous coordinate maps. The added `P.hilbertSequence_weighted_sq_le` and `P.hilbertSequence_sq_le_norm_sq` give the literal square bound; `sq_abs` converts to the displayed absolute-value notation. | Existing continuity and added bounds |
| (2) Möbius divisor cancellation | Imported Mathlib Möbius arithmetic; project finite inversion is `P.mobius_inversion`, and the corresponding difference inversion is `P.sum_mobiusDifference`. | Existing arithmetic infrastructure |
| (3) coefficient functional | `C.coefficientCLM := -P.mobiusDifferenceCLM`; `P.mobiusDifferenceCLM_apply` expands the finite divisor sum. | Existing |
| (4) biorthogonality and linear independence | `P.residue_difference`, `P.mobius_normalizedResidue`, `C.coefficientCLM_biorthogonal`, `C.residueAtom_linearIndependent`. | Existing |
| (5) coefficient of the constant | `P.mobius_coordinate_one`, together with the minus sign in `C.coefficientCLM`. | Existing |
| (6) positive definite Gram matrix | `FG.gramMatrix_posDef`; specialized determinant positivity is `P.IntegerDPP.fullGram_det_pos`. | Existing |
| (7) arbitrary-cutoff harmonic identity | New `P.pareto_partial_summation`, `P.residue_partial_sum_harmonic_arbitrary`, `P.normalizedResidue_partial_sum_harmonic` in `ParetoResiduePartialSummation.lean`. The existing `P.residue_partial_sum_harmonic` covers complete residue periods, not this arbitrary-cutoff boundary formula. | Added |
| (8) exact source vector | `P.paretoMean_residue`, `C.residueAtom_inner_one`, `G.source_apply`. These already evaluate the entire infinite Pareto mean as `log d / d`. | Existing |
| (9) periodic progression decomposition | `P.periodic_paretoInner_mixed`, specialized in the proof of `P.normalizedResidueHilbert_inner_digamma`. | Existing |
| (10) exact digamma Gram formula | `P.progressionWeight_eq_digamma`, `P.normalizedResidueHilbert_inner_digamma`. Lean sums positive representatives `1,...,L`; the final representative has zero residue product, so this is exactly the manuscript's `1,...,L-1` formula. | Existing |
| (11) completion of the square and uniqueness | `S.canonical_completion`, `S.canonical_minimizes`, `S.canonical_unique`, backed by `FG.residual_completion` and `FG.residual_minimizer_unique`. The correction quadratic is represented by the equal squared norm of its synthesis. | Existing |
| (12) inverse-Gram Möbius correction | `G.canonical_decomposition`, `G.canonical_mobius_decomposition`, `G.correctionVector_eq`, `G.correctionVector_apply`. | Existing |
| (13) actual orthogonal projection | `C.projection`, `C.projection_expansion`, `G.projection_eq_inverseGram_synthesis`, `G.canonicalVector_apply`. | Existing |
| (14) captured and residual energies | `S.captured_eq_norm_sq`, `S.error_eq_one_sub_captured`; the usual orthogonal projection pairing identifies the middle inner product. | Existing |
| (15) nested Pythagoras | `E.nested_projection_energy` proves the equivalent residual-energy identity; combined with orthogonal projection Pythagoras it yields the manuscript's projected-norm difference. | Existing equivalent form |
| (16) strong convergence for arbitrary vectors | `E.walkProjection_tendsto`, with identity enumeration. This is convergence to the actual closed dictionary span, with no density assumption. | Existing |
| (17) canonical projection limit | `C.projection_tendsto`. | Existing |
| (18) exact remaining-error decomposition | `C.energy_eq_limit_add`, backed by `E.walkError_eq_limitingError_add`. | Existing |
| (19) squared and unsquared error limits | `C.energy_tendsto`, `C.projection_norm_error_tendsto`, and the new `S.projection_norm_tendsto_sqrt_limitEnergy`. | Existing and added |
| (20) Schur complement and strict positivity | `S.sigma_eq_gram_schur`, `S.sigma_pos`. | Existing |
| (21) signed Schur source | `S.eta_eq_gram_schur`. | Existing |
| (22) vector projection recursion | `S.projection_schur_step`. | Existing |
| (23) every updated coefficient | `S.coefficient_schur_new`, `S.coefficient_schur_old`, and their `canonicalVector_schur_new` / `canonicalVector_schur_old` forms. | Existing |
| (24) exact captured-energy increment | `S.captured_schur_step`. | Existing |
| Initial values | `P.residueAtom_zero_norm_sq`, `S.canonicalVector_one`, `S.projection_one`, `S.captured_one`, `S.energy_one`. | Existing |
| (25) finite Schur sum | `S.captured_eq_log_two_add_schur_sum` gives the shifted display exactly, using the existing Schur recursion and `S.captured_one`. | Added |
| (26) exact infinite defect formula | The existing `S.schur_gain_after_two_hasSum` sums the complete shifted series to `1 - log 2 - limitEnergy`. The added `S.limitEnergy_eq_one_sub_log_sub_schur_tsum` states the exact defect formula. | Existing series and added defect formula |
| (27) fixed coefficients always converge | `C.coefficient_tendsto`; `C.limitCoefficient` is the continuous coefficient of `limitProjection`. | Existing |
| (28)–(30) Möbius limits versus zero residual | `C.limitCoefficient_eq_residual`, `C.limitCoefficients_eq_mobius_iff_residual_zero`. | Existing |
| (31) finite Möbius inversion and linear residual exclusion | `P.sequence_linear_of_mobius_zero`, `P.zero_of_linear_hilbertSequence`, `P.eq_zero_of_mobius_coordinates_zero`; the underlying summability result is `P.linear_square_summable_iff`. | Existing |
| (32) correction limits | `G.correction_tendsto`, `G.correction_tendsto_zero_iff`. | Existing |
| (33) internal equivalences | `S.canonical_saturation_equivalences` assembles all six conditions. It uses the existing coefficient, closure, and correction equivalences, plus the existing `S.captured_tendsto_one_iff_norm` and `S.schur_tail_saturation_iff_energy_zero`. | Existing core and added assembly |
| (34) full correction-energy cancellation | `G.mobiusResidual_projection`, `G.mobiusResidual_energy_split`, `G.mobiusResidual_norm_sq`, `G.correctionSynthesis_norm_sq`, and `G.error_eq_mobius_matrix_correction` give the full expanded identity, using actual Möbius and inverse-Gram vectors. | Added |
| (35) divisor/floor identity | Existing `RiemannResearch.NumberTheory.PrimeNumberTheorem.sum_mobius_floor` and its `sum_mobius_mul_floor` companion supply finite Möbius floor identities. The exact-head construction used below already incorporates this arithmetic. | Existing arithmetic; normalization should be matched when citing a literal formula |
| (36)–(37) arithmetic tail and zero head | Existing `P.canonicalMobiusHilbert_exact`; new `T.tailError_eq_finite_combination`, `T.tailError_head`, and `T.tailError_coordinate_zero`. `T.tailError_eq_mobiusResidual_sub` formally identifies this actual arithmetic tail with `R_N - N*m_N*g_N`, so the indexing and terminal cancellation are proved in Lean. | Existing construction and added identification |
| (38)–(39) explicit finite-support Riesz vector | Existing `P.mobiusRieszHilbert_sequence`, `P.dualCoeff_eq_zero_of_lt`, `P.mobiusRieszHilbert_inner`; new signed versions `T.coefficientRiesz_sequence`, `T.coefficientRiesz_sequence_zero`, `T.coefficientRiesz_inner`. The sign is essential: manuscript `h_d = -mobiusRieszHilbert d`. | Existing representer; signed wrappers added |
| (40) projected-tail coefficient | New `T.coefficient_projected_tailError`. | Added |
| (41) exact entire weighted tail pairing | New `T.correction_eq_pairing`, `T.correction_eq_tail_pairing`, `T.correction_eq_weighted_tail`. Physical indices begin at manuscript `N = n+1`; no weighted tail is dropped. | Added |
| (42) moving projected-dual tail tends to zero | New `T.projectedDualTailEnergy_tendsto_zero`. This states convergence of the squared norm and is equivalent to the displayed norm limit. | Added |
| (43) both factors retained in Cauchy–Schwarz | New `T.correction_sq_le_tail_product`, in the equivalent squared form. | Added |
| (44) exact arithmetic-tail energy split | New `T.tailError_projection_residual`, `T.tailError_energy_split`. | Added |

## What the RH endpoint actually proves

The existing theorem

```lean
RiemannResearch.RH.Pareto.CoefficientStabilization.
  riemannHypothesis_of_projection_norm_tendsto_zero
```

has the full Pareto norm convergence as an explicit hypothesis and concludes
Mathlib's actual `RiemannHypothesis`. The same established direction is available
as `C.riemannHypothesis_of_coefficients_tendsto_mobius` and
`G.riemannHypothesis_of_correction_limits`. These are proved implications, not
unconditional proofs of their premises.

The existing `S.riemannHypothesis_of_schur_saturation` already establishes the
full-series conditional RH reduction. The added endpoints
`S.riemannHypothesis_of_schur_tail_saturation`,
`T.riemannHypothesis_of_tail_products`, and
`T.riemannHypothesis_of_bounded_tailError` retain their respective arithmetic
inputs explicitly. They do not infer saturation from summability or product
decay from the vanishing of just one factor.

## Two distinct remaining obligations

1. **Missing formalization of a known classical converse.** The project does
   not currently supply a checked provider of

   ```lean
   RiemannHypothesis →
     RiemannResearch.RH.Pareto.CoefficientStabilization.closedSpace = ⊤
   ```

   This is the classical Nyman–Beurling–Báez–Duarte/Bagchi direction. The existing
   `C.closedSpace_eq_top_iff_one_mem` identifies it with RH implying membership
   of the constant. `RH/FirstCoordinateTailGap.lean` still takes exactly this
   implication as the explicit argument `hDensity`. The source audit
   `RH/RHToDensityDependencyAudit20260921.md` records the absent declaration
   `closedSpace_eq_top_of_riemannHypothesis` and its substantive analytic
   dependencies. The manuscript's final classical equivalence therefore must
   not be reported as an unconditional Lean equivalence unless this provider
   has actually been formalized.

2. **Open mathematical assertion.** Proving `C.limitEnergy = 0` without
   assuming RH remains the RH-strength arithmetic problem. Equivalent internal
   targets are fixed correction decay and saturation of the exact Schur gain
   sum. For the particular tail argument, the remaining sufficient input is
   decay of

   ```lean
   ‖T.tailError n‖ ^ 2 * T.projectedDualTailEnergy n d
   ```

   for every fixed `d > 1`, or a common bound on `‖T.tailError n‖²` at arbitrarily late indices (the strengthened criterion below).
   Convergence of `T.projectedDualTailEnergy n d` to zero alone does not establish
   either input. Equation (44) supplies an exact split, not the missing upper
   bound on the projected arithmetic tail.

## Explicit classical-theorem premise

The application of the external theorem is formalized as
`S.projection_norm_iff_riemannHypothesis_of_baez_duarte`, with the visible argument

```lean
(hBaezDuarte : RiemannHypothesis → hilbertOne ∈ closedSpace)
```

The existing converse implication, norm convergence to RH, is proved without
that extra argument. The new iff introduces neither an axiom nor a provider of
the displayed classical premise.

## Strengthening: cofinal boundedness (26 September 2026)

The sufficient arithmetic bound has been weakened. It is enough that there is
one real constant `C` such that

```lean
∀ M : ℕ, ∃ n : ℕ, M ≤ n ∧ ‖T.tailError n‖^2 ≤ C
```

A bound at every index is unnecessary. The generic theorem
`C.limitEnergy_eq_zero_of_cofinally_bounded_exact_head_errors` in
`RH/ExactHeadCofinalBounds.lean` applies to any sequence in the actual closed
residue span matching the constant on physical coordinates `1,...,n`.

Its proof retains the actual residual. Write `D = C.limitEnergy` and
`r_n = C.residualTailEnergy n`. The existing exact-head argument gives
`D^2 ≤ r_n * ‖T.tailError n‖^2`, while `r_n → 0`. If `D ≠ 0`, eventually
`r_n * C < D^2`. Choosing a bounded-energy index after that point contradicts
the lower bound. Thus `D = 0`.

Specializing to the arithmetic family proves:

- `T.projection_norm_tendsto_zero_of_cofinal_bounded_tailError`: full canonical
  Pareto projection convergence.
- `T.projection_norm_tendsto_zero_of_subsequence_bounded_tailError`: it suffices
  to bound the errors along any index map tending to infinity; strict
  monotonicity is unnecessary.
- `T.riemannHypothesis_of_cofinal_bounded_tailError`: RH follows by the already
  checked norm-convergence implication.

These conclusions do not require the classical RH-to-density premise. They
concern convergence of the optimal projections, not convergence of the
prescribed exact-head Möbius approximants. The cofinal arithmetic bound remains
**Open**. Existing `C.not_RH_exact_head_errors_tendsto_atTop` already implies
divergence of all such exact-head errors under failure of RH; no duplicate
divergence theorem was introduced.

## Source organization and verification

- `ExactHeadCofinalBounds.lean`: vanishing of the actual limiting defect from cofinally bounded exact-head errors.
- `ParetoCoordinateBounds.lean`: coordinate square bounds; evaluation maps remain in `ParetoCoordinateEvaluation.lean`.
- `ParetoResiduePartialSummation.lean`: exact arbitrary-cutoff summation by parts.
- `ResidueGramMobiusCorrection.lean`: Möbius residual, projected correction, and complete matrix energy.
- `ResidueSchurLimits.lean`: exact shifted defect, all six saturation equivalences, and the explicit-premise classical endpoint.
- `ResidueProjectionCorrectionTail.lean`: actual arithmetic tail, signed dual, complete weighted pairing, moving-tail decay, and conditional arithmetic criteria.

Development checks were serialized. Representative axiom audits for the matrix
energy, limiting defect, saturation equivalences, arithmetic tail identification,
moving-tail decay, conditional RH endpoint, partial summation, and coordinate
bound report only `propext`, `Classical.choice`, and `Quot.sound`.
Domain-specific hypotheses remain visible in theorem statements; axiom audits
do not discharge them. The publication checkpoint validates the changed modules
and their affected dependents. No placeholder proofs or project-local axioms
were added.
