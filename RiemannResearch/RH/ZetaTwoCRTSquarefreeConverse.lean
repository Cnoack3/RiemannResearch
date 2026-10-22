/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CRTSquarefreeConverse
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ZetaTwoCRTReciprocalEnergy

/-!
# The squarefree exact-head closure criterion in the Q measure

Source: user-provided sharp inverse-square comparison and converse,
13 October 2026. The entire physical sequence is preserved in the two
directions of weight transfer. No analytic RH-to-density bridge is assumed.
-/

noncomputable section
namespace RiemannResearch.RH.ZetaTwoProbability
open Pareto ZetaTwoHilbert ZetaTwoParetoTransfer

def qSquarefreeCRTSpan : Submodule ℝ QHilbert :=
  Submodule.span ℝ (Set.range (fun d : {d : ℕ // 2 ≤ d ∧ Squarefree d} => qResidue d.val))

theorem qSquarefreeCRTSpan_map :
    qSquarefreeCRTSpan.map toParetoLinear = squarefreeCRTSpan := by
  rw [squarefreeCRTSpan_eq_span, qSquarefreeCRTSpan, Submodule.map_span]
  congr 1
  ext f
  constructor
  · rintro ⟨q, ⟨d, rfl⟩, rfl⟩
    refine ⟨d, ?_⟩
    change normalizedResidueHilbert d.val _ = toPareto (qResidue d.val)
    rw [toPareto_qResidue _ (by have := d.property.1; omega)]
    simp [BaezDuarte.residueVector, show 0 < d.val by have := d.property.1; omega]
  · rintro ⟨d, rfl⟩
    refine ⟨qResidue d.val, ⟨d, rfl⟩, ?_⟩
    change toPareto (qResidue d.val) = normalizedResidueHilbert d.val _
    rw [toPareto_qResidue _ (by have := d.property.1; omega)]
    simp [BaezDuarte.residueVector, show 0 < d.val by have := d.property.1; omega]

/-- The squarefree closure condition is unchanged by the complete Q/P
change of weights, in both directions. -/
theorem qSquarefreeClosure_iff_paretoSquarefreeClosure :
    qOne ∈ qSquarefreeCRTSpan.topologicalClosure ↔
      hilbertOne ∈ squarefreeCRTSpan.topologicalClosure := by
  constructor
  · intro h
    have hm (q : QHilbert) (hq : q ∈ qSquarefreeCRTSpan) :
        toParetoCLM q ∈ squarefreeCRTSpan.topologicalClosure := by
      apply squarefreeCRTSpan.le_topologicalClosure
      rw [← qSquarefreeCRTSpan_map]
      exact ⟨q, hq, rfl⟩
    have hclosed : IsClosed
        (toParetoCLM ⁻¹' (squarefreeCRTSpan.topologicalClosure : Set ThresholdHilbert)) :=
      squarefreeCRTSpan.isClosed_topologicalClosure.preimage toParetoCLM.continuous
    have hh := closure_minimal hm hclosed h
    change toPareto qOne ∈ squarefreeCRTSpan.topologicalClosure at hh
    rw [toPareto_qOne] at hh
    exact hh
  · intro h
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨f, hf, hd⟩ := Metric.mem_closure_iff.mp h (ε / 2) (half_pos hε)
    rw [← qSquarefreeCRTSpan_map] at hf
    obtain ⟨q, hq, hf⟩ := hf
    refine ⟨q, hq, ?_⟩
    have hz : 1 ≤ zetaTwo := by
      simpa [zetaTwo] using inverseSquare_summable.le_tsum (1 : ℕ+)
        (fun k _ => by positivity)
    have he : toPareto (qOne - q) = hilbertOne - f := by
      change toParetoLinear (qOne - q) = _
      rw [map_sub]
      change toPareto qOne - toPareto q = _
      rw [toPareto_qOne]
      exact congrArg (hilbertOne - ·) hf
    have hc := zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq (qOne - q)
    rw [he] at hc
    have hsmall : ‖hilbertOne - f‖ < ε / 2 := by
      simpa only [dist_eq_norm] using hd
    rw [dist_eq_norm]
    have hlow : ‖qOne - q‖ ^ 2 ≤ zetaTwo * ‖qOne - q‖ ^ 2 :=
      le_mul_of_one_le_left (sq_nonneg _) hz
    nlinarith [norm_nonneg (qOne - q), norm_nonneg (hilbertOne - f)]

/-- The bounded exact-head finite-tail criterion is precisely Q squarefree
closure membership. This equivalence contains no RH-to-density assumption. -/
theorem qSquarefreeClosure_iff_exact_head_tail_bound :
    qOne ∈ qSquarefreeCRTSpan.topologicalClosure ↔ SquarefreeExactHeadTailBound :=
  qSquarefreeClosure_iff_paretoSquarefreeClosure.trans
    squarefreeClosure_iff_exact_head_tail_bound

end RiemannResearch.RH.ZetaTwoProbability
