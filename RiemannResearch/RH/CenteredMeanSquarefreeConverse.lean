import RiemannResearch.RH.ParetoSquarefreeDampingConverse
import RiemannResearch.RH.CenteredMeanMellinCharacters
import RiemannResearch.RH.CenteredMeanRHCriteria
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import RiemannResearch.RH.QSquarefreeCapacity

/-! # RH, squarefree approximation and the actual centered unit

Continuation of the damped Mellin test supplies the analytic implication
used by the earlier categorical criterion. The approximation is existential
in the coefficients and cutoff. -/

noncomputable section
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake

open CoefficientStabilization MixedConductorBasis CategoryTheory
open scoped LegalMeanAlgebra
open RiemannResearch.RH ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer

/-- Membership of the Pareto constant in the squarefree span closure
is equivalent to the Riemann hypothesis. -/
theorem riemannHypothesis_iff_squarefreeClosure :
    RiemannHypothesis ↔ hilbertOne ∈ squarefreeCRTSpan.topologicalClosure := by
  refine ⟨ResidueMellin.hilbertOne_mem_squarefreeClosure_of_riemannHypothesis, fun h => ?_⟩
  apply riemannHypothesis_of_qOne_mem_squarefree_closure
  rw [QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure]
  exact qSquarefreeClosure_iff_paretoSquarefreeClosure.mpr h

/-- Each finite stage sees the same unit boundary, and its vanishing
is equivalent to RH. -/
theorem stageUnit_zero_iff_RH (n : ℕ) :
    stageMeanBoundary n 1 = 0 ↔ RiemannHypothesis := by
  refine ⟨riemannHypothesis_of_stageUnit_zero, fun hRH => ?_⟩
  apply (stageUnit_zero_iff_boundary n).mpr
  apply boundary_eq_zero_iff_one_mem.mpr
  apply paretoOne_mem_closedSpace_of_qOne_mem_closure
  rw [QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure]
  exact qSquarefreeClosure_iff_paretoSquarefreeClosure.mpr
    (riemannHypothesis_iff_squarefreeClosure.mp hRH)

/-- The natural dilation approximation, with coefficients free to vary,
is equivalent to RH in the complete norm. -/
theorem riemannHypothesis_iff_naturalApproximation :
    RiemannHypothesis ↔ BaezDuarte.NaturalApproximation :=
  (stageUnit_zero_iff_RH 0).symm.trans
    ((stageUnit_zero_iff_boundary 0).trans boundary_eq_zero_iff_naturalApproximation)

/-- The epimorphism condition on the original mean boundary detects RH. -/
theorem boundary_epi_iff_RH :
    Epi (TopModuleCat.ofHom boundary) ↔ RiemannHypothesis :=
  boundary_epi_iff_riemannHypothesis riemannHypothesis_iff_naturalApproximation.mp

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake

/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.riemannHypothesis_iff_squarefreeClosure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms riemannHypothesis_iff_squarefreeClosure

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake

/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.stageUnit_zero_iff_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms stageUnit_zero_iff_RH

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake

/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.riemannHypothesis_iff_naturalApproximation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms riemannHypothesis_iff_naturalApproximation

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake

/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.boundary_epi_iff_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms boundary_epi_iff_RH

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
