import RiemannResearch.RH.ExactHeadOccurrenceCriterion
import RiemannResearch.RH.ExactHeadOccurrencePartition
import RiemannResearch.NumberTheory.DivisorReturnCoordinates

import RiemannResearch.RH.ExactHeadOccurrenceBudgets
import RiemannResearch.NumberTheory.UnitCenteredReturnSampling

open RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection
open RiemannResearch.Analysis.FiniteAtomDispersion
open RiemannResearch.NumberTheory.UnitCenteredReturnSampling

/-! Guarded dependency audits for the exact identities, corrected inferences,
and conditional RH criteria. Substantive hypotheses remain visible in the
theorem types; this audit checks the transitive axiom dependencies only. -/

/--
info: 'RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection.reuse_green_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  reuse_green_identity

/--
info: 'RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection.reuseEnergy_le_five_returnDispersion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  reuseEnergy_le_five_returnDispersion

/--
info: 'RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection.riemannHypothesis_of_cofinal_bounded_returnDispersion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  riemannHypothesis_of_cofinal_bounded_returnDispersion

/--
info: 'RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection.riemannHypothesis_of_cofinal_bounded_green_trial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  riemannHypothesis_of_cofinal_bounded_green_trial

/--
info: 'RiemannResearch.Analysis.FiniteAtomDispersion.no_uniform_dyadic_inference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  RiemannResearch.Analysis.FiniteAtomDispersion.no_uniform_dyadic_inference

/--
info: 'RiemannResearch.NumberTheory.DivisorReturnCoordinates.parity_return_bias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  RiemannResearch.NumberTheory.DivisorReturnCoordinates.parity_return_bias

/--
info: 'RiemannResearch.Analysis.FiniteAtomDispersion.l1_sq_add_pairwise_eq_card_mul_loss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms l1_sq_add_pairwise_eq_card_mul_loss

/--
info: 'RiemannResearch.Analysis.FiniteAtomDispersion.l1_sq_le_normalized_fiber_budgets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms l1_sq_le_normalized_fiber_budgets

/--
info: 'RiemannResearch.NumberTheory.UnitCenteredReturnSampling.parity_centered_return_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms parity_centered_return_sum

/--
info: 'RiemannResearch.NumberTheory.UnitCenteredReturnSampling.return_average_error_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms return_average_error_exact

/--
info: 'RiemannResearch.NumberTheory.UnitCenteredReturnSampling.return_second_moment_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms return_second_moment_le

/--
info: 'RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection.riemannHypothesis_of_cofinal_fiber_budgets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms riemannHypothesis_of_cofinal_fiber_budgets

/--
info: 'RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection.occurrence_trial_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms occurrence_trial_identity

/--
info: 'RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection.occurrenceCoefficients_eq_of_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms occurrenceCoefficients_eq_of_normal

/--
info: 'RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection.occurrence_block_pairwise_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms occurrence_block_pairwise_identity

/--
info: 'RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection.occurrence_block_pair_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms occurrence_block_pair_lower

/--
info: 'RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection.occurrenceEnergy_eq_block_variances' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms occurrenceEnergy_eq_block_variances

/--
info: 'RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection.occurrenceEnergy_le_gapBudget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms occurrenceEnergy_le_gapBudget

/--
info: 'RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection.occurrenceCoefficients_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms occurrenceCoefficients_boundary

/--
info: 'RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection.occurrenceCoefficients_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms occurrenceCoefficients_nonneg

/--
info: 'RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection.occurrence_fit_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms occurrence_fit_mono

/--
info: 'RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection.riemannHypothesis_of_cofinal_gap_green_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms riemannHypothesis_of_cofinal_gap_green_budget
