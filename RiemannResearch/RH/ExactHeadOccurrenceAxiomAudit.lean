import RiemannResearch.RH.ExactHeadOccurrenceCriterion
import RiemannResearch.NumberTheory.DivisorReturnCoordinates

open RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection

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
