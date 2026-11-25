import RiemannResearch.RH.CenteredMeanSquarefreeConverse
import RiemannResearch.RH.ResidueClosureDensity
import RiemannResearch.RH.ThresholdTwoSeedEquivalence

/-! # The two-seed criterion from squarefree approximation

The natural-dilation approximants supplied under RH put the constant in
the complete residue space. Dilation of that constant yields full positive
residue density, so the existing two-seed rigidity theorem applies.
-/

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
open CoefficientStabilization

/-- Under RH the full positive-remainder legal closure is the entire Hilbert space. -/
theorem positiveResidueDensityFromRH : PositiveResidueDensityFromRH := by
  intro hRH
  have hOne := BaezDuarte.naturalApproximation_iff_one_mem.mp
    (riemannHypothesis_iff_naturalApproximation.mp hRH)
  have htop := closedSpace_eq_top_iff_one_mem.mpr hOne
  apply top_unique
  simpa only [htop] using closedSpace_le_legalClosure

/-- RH is equivalent to approximation of the constant by the closed legal
two-seed family, with every positive integer dilation allowed. -/
theorem riemannHypothesis_iff_twoSeedClosure :
    RiemannHypothesis ↔ hilbertOne ∈ hilbertLegalClosure {2, 3} :=
  riemannHypothesis_iff_twoSeed_closure_of_density_from_rh positiveResidueDensityFromRH

/-- The same two-seed family is dense precisely under RH. -/
theorem riemannHypothesis_iff_twoSeedDensity :
    RiemannHypothesis ↔ hilbertLegalClosure {2, 3} = ⊤ :=
  riemannHypothesis_iff_twoSeed_density_of_density_from_rh positiveResidueDensityFromRH

/-- info:
'RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.riemannHypothesis_iff_twoSeedDensity'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms riemannHypothesis_iff_twoSeedDensity

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
