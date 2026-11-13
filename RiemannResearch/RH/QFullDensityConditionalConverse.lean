import RiemannResearch.RH.QFullTargetTotality
import RiemannResearch.RH.MertensBaezDuarteConverse
import RiemannResearch.RH.QOptimizerParityRH

/-!
# Full density equivalences with an explicit analytic provider

Source: PQ_Density_Operators_and_RH_Agenda.pdf, agenda 7.
The published Baez-Duarte approximation theorem is an explicit hypothesis.
This file does not claim to have formalized that analytic theorem.
-/

noncomputable section
namespace RiemannResearch.RH.QFullDensityConditionalConverse
open ZetaTwoHilbert ZetaTwoProbability QFullResidueProjection
open Pareto.BaezDuarte QFullTargetTotality

theorem squarefreeClosure_le_full :
    qSquarefreeCRTSpan.topologicalClosure ≤ QFullResidueProjection.closure := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro x ⟨d, rfl⟩
    exact legalSpan.le_topologicalClosure
      (QFloorDilation.qResidue_mem_legalSpan d.val (by have := d.property.1; omega))
  · exact legalSpan.isClosed_topologicalClosure

theorem riemannHypothesis_iff_one_mem
    (hBD : BaezDuarteMobiusApproximation) :
    RiemannHypothesis ↔ qOne ∈ QFullResidueProjection.closure := by
  constructor
  · intro hRH
    apply squarefreeClosure_le_full
    exact qSquarefreeClosure_iff_paretoSquarefreeClosure.mpr
      (squarefreeClosure_of_baezDuarteMobiusApproximation hBD hRH)
  · exact riemannHypothesis_of_qOne_mem_full_closure

theorem riemannHypothesis_iff_totality
    (hBD : BaezDuarteMobiusApproximation) :
    RiemannHypothesis ↔ QFullResidueProjection.closure = ⊤ :=
  (riemannHypothesis_iff_one_mem hBD).trans closure_eq_top_iff_one_mem.symm

theorem riemannHypothesis_iff_density_invariant
    (hBD : BaezDuarteMobiusApproximation) :
    RiemannHypothesis ↔
      ∀ f ∈ QFullResidueProjection.closure, QDensityMetric.B f ∈
        QFullResidueProjection.closure :=
  (riemannHypothesis_iff_one_mem hBD).trans one_mem_iff_density_invariant

#print axioms riemannHypothesis_iff_totality

end RiemannResearch.RH.QFullDensityConditionalConverse
