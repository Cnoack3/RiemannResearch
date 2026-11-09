# Reciprocal density, compactness and complete-energy catalog — 2026-11-08

**RH is not proved.** The new arithmetic approximation theorems are unconditional;
all routes from reciprocal approximation to RH retain an explicit complete-energy,
complete-tail, or regularized-cost hypothesis.

## Scope and verification

This sidecar catalogs 25 new Lean modules from the user-provided
`Reciprocal_Density_CRT_Nyman_Beurling_2026-11-08.pdf`, §§6–10, and its research agenda.
Base commit: `066a63be91fd0c3edf323415dcfc223322a828c6`.
The existing reciprocal multiplier, Mellin transform, divisor coefficients, full
residue closure, signed-energy certificate and endpoint RH implications were reused.
The new modules are additions, not claims that those prerequisites were absent.

Targeted Bazel/BuildBuddy receipt: **job_DZ3EHd4ZBxkxlF1IeKQqXz5xONXxA0f_`; axiom-output guard `job_cpPUtovIi9jO5zwaJe-RWooAGFW_8GDx**. Its snippet imports all 25 new
modules and audits a representative terminal theorem from each module. The recorded
axioms are `propext`, `Classical.choice`, and `Quot.sound`. Local mathematical hypotheses
are listed in declaration types and are not discharged by the axiom audit.
The publication checkpoint separately validates the complete integrated project;
the snippet alone does not establish that final publication status.

The module-to-declaration index below is generated from the authored sources.
A checked conditional theorem is not an unconditional proof of its conclusion.

## Principal results and remaining providers

| Result | Declaration/module | Arithmetic status |
|---|---|---|
| Bounded reciprocal lifts identify the target by weak compactness and injectivity | `QBoundedReciprocalLift.riemannHypothesis_of_bounded_reciprocal_target` | Uniform complete source norm is Open |
| Reciprocal convergence plus Cauchy preimages or uniform complete tails gives strong convergence | `QReciprocalCompleteTail` | Complete source/tail control is Open |
| Same-Q, same-R, same-target counterexample without boundedness, in the mean-zero hyperplane | `QReciprocalMeanZeroCounterexample.actual_reciprocal_lifting_counterexample` | Unconditional counterexample to the abstract shortcut; this hyperplane is not the arithmetic legal space |
| Failure of RH forces norms of every legal reciprocal approximation to tend to infinity | `QReciprocalLiftDivergence.reciprocal_target_norm_tendsto_atTop_of_not_RH` | Conditional on failure of RH; no assertion that RH fails |
| Any positive power reciprocal rate plus subpower complete energy implies RH | `QReciprocalMellinCriterion.riemannHypothesis_of_reciprocal_power_rate_subpower_norm` | Complete energy is Open |
| Explicit Möbius cutoff has full reciprocal error at most `(C1+1)/(j+2)` | `DampedMobiusExplicitReciprocalCriterion.approximant_reciprocal_error_le` | Unconditional |
| This actual cutoff family implies RH from subpower energy alone | `DampedMobiusExplicitReciprocalCriterion.riemannHypothesis_of_explicit_subpower_energy` | `henergy` is Open |
| Smoothed Chebyshev direction and quadratic full-norm remainder | `DampedMobiusSecondOrderHilbert` | Unconditional; no unsmoothed Chebyshev membership is asserted |
| Finite Richardson cutoff has reciprocal error at most `(6*C2+3)/(j+2)^2` | `DampedMobiusFiniteRichardson.richardsonApproximant_reciprocal_error_le` | Unconditional |
| Accelerated family implies RH from its subpower energy alone | `DampedMobiusFiniteRichardson.riemannHypothesis_of_richardson_subpower_energy` | `henergy` is Open |
| Near-linear regularized cost, allowing every positive exponent loss, implies RH | `QReciprocalRegularizedCriterion.riemannHypothesis_of_near_linear_regularized_cost` | Actual legal-family cost estimate is Open |
| Signed finite-head dual identities and Tikhonov normal-equation remainder | `QReciprocalDualCertificate`; `Analysis.TikhonovQuadratic` | Unconditional identities; no uniform cost estimate inferred |
| Sharper physical Mellin head power `H^(3-2*Re(s))`, with signed head-tail identity | `QReciprocalMellinSharpHead` | Unconditional estimate; legal energy budgets remain Open |
| Complete energy intervals keep the signed head and bound the full omitted tail | `QFiniteEnergyIntervals.sum_residues_norm_sq_interval` | Unconditional generic certificate; external numeric endpoints not kernel-checked |

The subpower premise is with respect to the approximation index `j`, not the
much larger conductor cutoff. It means `(j+1)^(-a)*‖U_j‖² → 0` for every `a>0`.
No arithmetic provider for that premise was obtained.

## External computations

The script `RiemannResearch/RH/MobiusRichardsonEnergyScript20261108.md` reproduces exact-integer
outward rational enclosures with `--certificate-only`, using the Python standard
library. See [the certificate note](RH/RichardsonEnergyCertificate20261108.md) and
[the output](RH/ReciprocalRichardsonEnergy20261108.md). The complete-energy and
reciprocal-error comparisons at `n=2` are external exact-integer calculations.
The `n=3` floating rows have no rounding certificate. Neither is an asymptotic
energy bound, and neither has been relabeled as a Lean-checked computation.

## Declaration index

### [Analysis/BoundedInjectiveLift.lean](Analysis/BoundedInjectiveLift.lean)

Namespace: `Submodule`.

- `exists_mem_of_bounded_image_tendsto` — theorem
- `mem_of_bounded_injective_image_tendsto` — theorem
- `mem_of_bounded_subsequence_injective_image_tendsto` — theorem

### [Analysis/ExponentialQuadraticRemainder.lean](Analysis/ExponentialQuadraticRemainder.lean)

Namespace: `Real`.

- `exp_neg_first_order_remainder` — theorem

### [Analysis/InjectiveLiftDivergence.lean](Analysis/InjectiveLiftDivergence.lean)

Namespace: `Submodule`.

- `norm_tendsto_atTop_of_not_mem_injective_image_tendsto` — theorem

### [Analysis/TikhonovQuadratic.lean](Analysis/TikhonovQuadratic.lean)

Namespace: `RiemannResearch.Analysis.TikhonovQuadratic`.

- `objective` — def
- `normalDefect` — def
- `objective_expansion` — theorem
- `objective_remainder` — theorem
- `objective_gap_of_normal_defect_bound` — theorem
- `objective_remainder_on_submodule` — theorem
- `objective_minimal_on_submodule` — theorem
- `objective_gap_controls_norm` — theorem
- `eq_of_objective_eq` — theorem

### [RH/DampedMobiusDensityBounds.lean](RH/DampedMobiusDensityBounds.lean)

Namespace: `RiemannResearch.RH.Pareto`.

- `riemannZeta_real_eq_nat_rpow_tsum` — theorem
- `one_div_le_zeta_real_series` — theorem
- `dampedMobius_density_bounds` — theorem
- `zeta_real_series_le_one_add_one_div` — theorem
- `dampedMobius_density_sandwich` — theorem
- `dampedMobius_density_sub_epsilon_le_sq` — theorem

### [RH/DampedMobiusExplicitReciprocalCriterion.lean](RH/DampedMobiusExplicitReciprocalCriterion.lean)

Namespace: `RiemannResearch.RH.DampedMobiusExplicitReciprocalCriterion`.

- `damping` — def
- `conductorCutoff` — def
- `approximant` — def
- `damping_pos` — theorem
- `conductorCutoff_pos` — theorem
- `nat_cutoff_reciprocal_budget` — theorem
- `conductorCutoff_reciprocal_budget` — theorem
- `approximant_mem_squarefreeSpan` — theorem
- `approximant_mem_legalSpan` — theorem
- `approximant_reciprocal_error_le` — theorem
- `approximant_reciprocal_tendsto` — theorem
- `riemannHypothesis_of_explicit_subpower_energy` — theorem

### [RH/DampedMobiusFiniteRichardson.lean](RH/DampedMobiusFiniteRichardson.lean)

Namespace: `RiemannResearch.RH.DampedMobiusFiniteRichardson`.

- `qRichardsonPartial` — def
- `qRichardsonPartial_mem_squarefreeSpan` — theorem
- `qRichardsonPartial_mem_legalSpan` — theorem
- `qRichardsonPartial_truncation_error_le` — theorem
- `qRichardsonPartial_reciprocal_error_le` — theorem
- `reciprocalTail_antitone_damping` — theorem
- `nat_cutoff_quadratic_budget` — theorem
- `richardsonDamping` — def
- `richardsonCutoff` — def
- `richardsonApproximant` — def
- `richardsonDamping_pos` — theorem
- `richardsonCutoff_pos` — theorem
- `richardsonCutoff_half_budget` — theorem
- `richardsonCutoff_full_budget` — theorem
- `richardsonApproximant_mem_squarefreeSpan` — theorem
- `richardsonApproximant_mem_legalSpan` — theorem
- `richardsonApproximant_reciprocal_error_le` — theorem
- `richardsonApproximant_reciprocal_tendsto` — theorem
- `riemannHypothesis_of_richardson_subpower_energy` — theorem

### [RH/DampedMobiusReciprocalEnvelope.lean](RH/DampedMobiusReciprocalEnvelope.lean)

Namespace: `RiemannResearch.RH.Pareto`.

- `dampedMobiusPrefix_sub_one_bounds` — theorem
- `dampedMobius_reciprocal_error_le_log` — theorem
- `dampedDivisorCoefficient_le_sq_mul_log_sq_of_two_primes` — theorem

### [RH/DampedMobiusReciprocalHilbert.lean](RH/DampedMobiusReciprocalHilbert.lean)

Namespace: `RiemannResearch.RH.DampedMobiusReciprocalHilbert`.

- `qLogEnvelope_square_summable` — theorem
- `qLogEnvelopeSequence` — def
- `qLogEnvelopeSequence_square_summable` — theorem
- `qLogEnvelope` — def
- `qSequence_qLogEnvelope` — theorem
- `reciprocalDampedSequence` — def
- `reciprocalDampedSequence_zero` — theorem
- `dampedMobiusPrefix_bounds` — theorem
- `reciprocalDampedSequence_abs_le` — theorem
- `reciprocalDampedQ` — def
- `qSequence_reciprocalDampedQ` — theorem
- `reciprocalDampedQ_error_coordinate` — theorem
- `reciprocalDampedQ_error_norm_sq_le` — theorem
- `reciprocalDampedQ_error_norm_le` — theorem
- `reciprocalDampedQ_tendsto` — theorem
- `dampedMobiusReciprocalQ` — def
- `qSequence_dampedMobiusReciprocalQ` — theorem
- `dampedMobiusReciprocalQ_error_norm_le` — theorem
- `dampedMobiusReciprocalQ_error_norm_sq_le` — theorem
- `dampedMobiusReciprocalQ_tendsto` — theorem

### [RH/DampedMobiusSecondOrder.lean](RH/DampedMobiusSecondOrder.lean)

Namespace: `RiemannResearch.RH.Pareto`.

- `dampedDivisorCoefficient_prime_pow_second_order` — theorem

### [RH/DampedMobiusSecondOrderHilbert.lean](RH/DampedMobiusSecondOrderHilbert.lean)

Namespace: `RiemannResearch.RH.DampedMobiusSecondOrderHilbert`.

- `qLogSquareEnvelope_square_summable` — theorem
- `qLogSquareEnvelopeSequence` — def
- `qLogSquareEnvelopeSequence_square_summable` — theorem
- `qLogSquareEnvelope` — def
- `qSequence_qLogSquareEnvelope` — theorem
- `qChebyshevDirectionSequence` — def
- `qChebyshevDirectionSequence_zero` — theorem
- `qChebyshevDirectionSequence_abs_le` — theorem
- `qChebyshevDirectionSequence_square_summable` — theorem
- `qChebyshevDirection` — def
- `qSequence_qChebyshevDirection` — theorem
- `norm_le_of_coordinate_envelope` — private theorem
- `dampedMobiusReciprocalQ_second_order_coordinate` — theorem
- `dampedMobiusReciprocalQ_second_order_norm_le` — theorem
- `qRichardsonMobius` — def
- `qRichardsonMobius_error_norm_le` — theorem
- `dampedMobiusReciprocalQ_differenceQuotient_norm_le` — theorem
- `dampedMobiusReciprocalQ_differenceQuotient_tendsto` — theorem

### [RH/DampedMobiusSecondOrderPrefix.lean](RH/DampedMobiusSecondOrderPrefix.lean)

Namespace: `RiemannResearch.RH.Pareto`.

- `dampedDivisorCoefficient_second_order` — theorem
- `dampedMobiusPrefix_second_order` — theorem
- `dampedMobius_reciprocal_second_order_of_density_bound` — theorem
- `dampedMobius_reciprocal_second_order` — theorem

### [RH/DampedMobiusSmoothedSeries.lean](RH/DampedMobiusSmoothedSeries.lean)

Namespace: `RiemannResearch.RH.DampedMobiusSmoothedSeries`.

- `qDampedSmoothedTerm` — def
- `qDampedSmoothedTerm_norm_le` — theorem
- `qDampedSmoothedTerm_norm_summable` — theorem
- `qDampedSmoothedTerm_summable` — theorem
- `qDampedMobiusSmoothed` — def
- `qDampedMobiusPartial_mem_squarefreeSpan` — theorem
- `qDampedMobiusPartial_B_eq` — theorem
- `qDampedMobiusPartial_B_tendsto` — theorem
- `qDampedMobiusSmoothed_partial_error_eq` — theorem
- `qDampedMobiusSmoothed_partial_error_le` — theorem
- `qDampedMobiusSmoothed_sequence` — theorem
- `qDampedMobiusSmoothed_eq_reciprocalQ` — theorem
- `qDampedMobiusPartial_reciprocal_error_le` — theorem
- `qDampedMobiusPartial_reciprocal_tendsto` — theorem

### [RH/QBoundedReciprocalLift.lean](RH/QBoundedReciprocalLift.lean)

Namespace: `RiemannResearch.RH.QBoundedReciprocalLift`.

- `reciprocal_injective` — theorem
- `mem_of_bounded_reciprocal_tendsto` — theorem
- `riemannHypothesis_of_bounded_reciprocal_target` — theorem

### [RH/QFiniteEnergyIntervals.lean](RH/QFiniteEnergyIntervals.lean)

Namespace: `RiemannResearch.RH.QFiniteEnergyIntervals`.

- `headNumerator` — def
- `norm_sq_interval_of_tail_bound` — theorem
- `norm_sq_remainder_interval` — theorem
- `qSequence_sum_residues` — theorem
- `sum_residues_physical_bound` — theorem
- `sum_residues_norm_sq_interval` — theorem

### [RH/QReciprocalCompleteTail.lean](RH/QReciprocalCompleteTail.lean)

Namespace: `RiemannResearch.RH.QReciprocalCompleteTail`.

- `tendsto_of_reciprocal_tendsto_cauchySeq` — theorem
- `finiteHead_sub` — theorem
- `finiteHead_absorb_of_le` — theorem
- `completeTail_norm_antitone` — theorem
- `finiteHead_norm_le_reciprocal` — theorem
- `finiteHead_error_tendsto_zero` — theorem
- `tendsto_of_reciprocal_tendsto_uniform_completeTail` — theorem
- `mem_of_reciprocal_tendsto_uniform_completeTail` — theorem
- `riemannHypothesis_of_reciprocal_uniform_completeTail` — theorem

### [RH/QReciprocalDualCertificate.lean](RH/QReciprocalDualCertificate.lean)

Namespace: `RiemannResearch.RH.QReciprocalDualCertificate`.

- `reciprocal_head_dual_identity_of_orthogonal` — theorem
- `reciprocal_head_dual_bound_of_orthogonal` — theorem
- `reciprocal_head_dual_identity` — theorem
- `reciprocal_head_dual_bound` — theorem
- `weighted_two_term_bound` — theorem
- `tikhonov_finite_dual_bound_of_orthogonal` — theorem
- `tikhonov_finite_dual_bound` — theorem
- `full_tikhonov_remainder` — theorem

### [RH/QReciprocalFiniteHead.lean](RH/QReciprocalFiniteHead.lean)

Namespace: `RiemannResearch.RH.QReciprocalFiniteHead`.

- `finiteHead_norm_sq_le_reciprocal` — theorem
- `inverseFiniteHead` — def
- `B_single` — theorem
- `B_inverseFiniteHead` — theorem

### [RH/QReciprocalLiftDivergence.lean](RH/QReciprocalLiftDivergence.lean)

Namespace: `RiemannResearch.RH.QReciprocalLiftDivergence`.

- `norm_tendsto_atTop_of_not_mem_reciprocal_tendsto` — theorem
- `reciprocal_target_norm_tendsto_atTop_of_not_RH` — theorem

### [RH/QReciprocalMeanZeroCounterexample.lean](RH/QReciprocalMeanZeroCounterexample.lean)

Namespace: `RiemannResearch.RH.QReciprocalMeanZeroCounterexample`.

- `qOne_coordinate` — private theorem
- `qOne_coordinate_pos` — private theorem
- `qOne_coordinate_sq` — private theorem
- `meanSpike` — def
- `meanSpike_apply` — theorem
- `inner_qOne_meanSpike` — theorem
- `meanZero` — def
- `meanZero_isClosed` — theorem
- `meanZeroApproximant` — def
- `meanZeroApproximant_mem` — theorem
- `qOne_not_mem_meanZero` — theorem
- `reciprocal_spike_coordinate_bound` — private theorem
- `reciprocal_meanSpike_norm_sq_le` — theorem
- `meanZeroApproximant_reciprocal_error_sq_le` — theorem
- `meanZeroApproximant_reciprocal_tendsto` — theorem
- `actual_reciprocal_lifting_counterexample` — theorem

### [RH/QReciprocalMellinCriterion.lean](RH/QReciprocalMellinCriterion.lean)

Namespace: `RiemannResearch.RH.QReciprocalMellinCriterion`.

- `qMellin_head_tail_identity` — theorem
- `qMellin_norm_sq_le_reciprocal_split` — theorem
- `qMellin_legalSpan_zero` — theorem
- `zeta_ne_zero_of_reciprocal_budget` — theorem
- `riemannHypothesis_of_variable_head_subpower_residual` — theorem
- `riemannHypothesis_of_variable_head_subpower_norm` — theorem
- `riemannHypothesis_of_cofinal_variable_head_budget` — theorem
- `riemannHypothesis_of_reciprocal_rate_subpower_norm` — theorem

### [RH/QReciprocalMellinSharpHead.lean](RH/QReciprocalMellinSharpHead.lean)

Namespace: `RiemannResearch.RH.QReciprocalMellinSharpHead`.

- `reciprocalMellinCoeff` — def
- `qMellin_head_reciprocal_sum` — theorem
- `reciprocalMellinCoeff_energy_eq` — theorem
- `reciprocalMellinCoeff_energy_le` — theorem
- `reciprocalMellinCoeff_head_energy_le` — theorem
- `qMellin_head_norm_sq_le_reciprocal` — theorem
- `qMellin_head_tail_energy_identity` — theorem
- `qMellin_norm_sq_le_sharp_reciprocal_split` — theorem
- `zeta_ne_zero_of_sharp_reciprocal_budget` — theorem

### [RH/QReciprocalNoncoercivity.lean](RH/QReciprocalNoncoercivity.lean)

Namespace: `RiemannResearch.RH.QReciprocalNoncoercivity`.

- `residue_reciprocal_inverse_amplification` — theorem
- `reciprocal_residue_norm_sq_pos` — theorem
- `residue_exceeds_reciprocal_inverse_constant` — theorem
- `exists_prime_exceeding_reciprocal_inverse_constant` — theorem
- `exists_dictionary_atom_exceeding_reciprocal_inverse_constant` — theorem
- `no_uniform_reciprocal_inverse_on_prime_atoms` — theorem
- `no_uniform_reciprocal_inverse_on_dictionary_space` — theorem

### [RH/QReciprocalPowerRateCriterion.lean](RH/QReciprocalPowerRateCriterion.lean)

Namespace: `RiemannResearch.RH.QReciprocalMellinCriterion`.

- `riemannHypothesis_of_reciprocal_power_rate_subpower_norm` — theorem

### [RH/QReciprocalRegularizedCriterion.lean](RH/QReciprocalRegularizedCriterion.lean)

Namespace: `RiemannResearch.RH.QReciprocalRegularizedCriterion`.

- `reciprocalCost` — def
- `regularizationScale` — def
- `regularizationScale_pos` — theorem
- `reciprocalCost_nonneg` — theorem
- `riemannHypothesis_of_near_linear_regularized_cost` — theorem

## Next proof obligation

Establish the complete unsmoothed subpower-energy bound for either explicit family,
or establish the near-linear complete Tikhonov cost on an actual legal family.
The bounded-lift and graph routes remain alternatives with their stronger source
control hypotheses. Improved reciprocal approximation alone does not close RH.
