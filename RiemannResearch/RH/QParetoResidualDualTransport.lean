/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QParetoMetric
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.RH.QAnnihilatorTailEscape
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.QSquarefreeExactHeadResidualBarrier
import RiemannResearch.RH.QSquarefreeResidualTail
import RiemannResearch.RH.QProjectionMoments
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The exact dual change of measure for the actual squarefree residual

Source: the user's symbolic Ramanujan/Pareto closure request, 28 October 2026.
The physical-sequence equivalence alone does not preserve orthogonality.
The correct dual vector includes the full reciprocal correction:
V(u) = toPareto(u) + D(toPareto(u)). Its pairing is exactly zetaTwo times
the original Q pairing. This identifies an explicit Pareto annihilator for
the actual Q residual without asserting that this residual vanishes.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QParetoResidualDualTransport
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QParetoMetric
open ZetaTwoOptimizerStage QFiniteSupportDualCriterion QAnnihilatorTailEscape
open QSquarefreeResidualTail QSquarefreeExactHeadResidualBarrier

/-- The metric-corrected transport of continuous dual tests. -/
def dualTransport : QHilbert →L[ℝ] ThresholdHilbert :=
  toParetoCLM + reciprocalD.comp toParetoCLM

@[simp] theorem dualTransport_apply (u : QHilbert) :
    dualTransport u = toPareto u + reciprocalD (toPareto u) := rfl

/-- Every signed pairing is transported with its complete correction. -/
theorem dualTransport_pairing (u f : QHilbert) :
    inner ℝ (dualTransport u) (toPareto f) = zetaTwo * inner ℝ u f := by
  rw [dualTransport_apply, inner_add_left, reciprocalD_symmetric]
  exact (inner_identity u f).symm

/-- The dual correction is faithful, rather than the primal sequence-preserving map. -/
theorem dualTransport_eq_zero_iff (u : QHilbert) : dualTransport u = 0 ↔ u = 0 := by
  constructor
  · intro hu
    have hp := dualTransport_pairing u u
    rw [hu, inner_zero_left, real_inner_self_eq_norm_sq] at hp
    have hs : ‖u‖ ^ 2 = 0 :=
      (mul_eq_zero.mp hp.symm).resolve_left (ne_of_gt zetaTwo_pos)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hs)
  · rintro rfl
    exact map_zero dualTransport

/-- Orthogonality is preserved by the dual transport, not by a silent change
of inner product. No closedness or positive-definite finite Gram hypothesis is used. -/
theorem dualTransport_mem_orthogonal_map_iff (S : Submodule ℝ QHilbert) (u : QHilbert) :
    dualTransport u ∈ (S.map toParetoLinear)ᗮ ↔ u ∈ Sᗮ := by
  constructor
  · intro hu
    apply (S.mem_orthogonal' u).mpr
    intro f hf
    have hp := ((S.map toParetoLinear).mem_orthogonal' (dualTransport u)).mp hu
      (toPareto f) ⟨f, hf, rfl⟩
    rw [dualTransport_pairing] at hp
    exact (mul_eq_zero.mp hp).resolve_left (ne_of_gt zetaTwo_pos)
  · intro hu
    apply ((S.map toParetoLinear).mem_orthogonal' (dualTransport u)).mpr
    rintro v ⟨f, hf, rfl⟩
    change inner ℝ (dualTransport u) (toPareto f) = 0
    rw [dualTransport_pairing, (S.mem_orthogonal' u).mp hu f hf, mul_zero]

theorem actualResidual_dual_mem_pareto_orthogonal :
    dualTransport limitingResidual ∈ squarefreeCRTSpan.topologicalClosureᗮ := by
  rw [Submodule.orthogonal_closure, ← qSquarefreeCRTSpan_map,
    dualTransport_mem_orthogonal_map_iff]
  apply (qSquarefreeCRTSpan.mem_orthogonal' limitingResidual).mpr
  intro F hF
  rw [real_inner_comm]
  exact Submodule.inner_right_of_mem_orthogonal
    (legal_mem_optimizer_closure F hF) limitingResidual_mem_squarefree_orthogonal

theorem actualResidual_dual_mean :
    inner ℝ (dualTransport limitingResidual) hilbertOne = zetaTwo * ‖limitingResidual‖ ^ 2 := by
  rw [← toPareto_qOne, dualTransport_pairing]
  exact congrArg (zetaTwo * ·) (qResidual_inner_qOne ZetaTwoOptimizerStage.closure)

theorem toPareto_finiteHead (H : ℕ) (u : QHilbert) :
    toPareto (finiteHead H u) = finiteHead H (toPareto u) := by
  apply lp.ext
  funext n
  change Real.sqrt (paretoWeight n) *
    ((finiteHead H u) n / Real.sqrt (qWeight n)) = (finiteHead H (toPareto u)) n
  by_cases hn : n < H
  · rw [finiteHead_apply_of_lt H u n hn, finiteHead_apply_of_lt H (toPareto u) n hn]
    rfl
  · rw [finiteHead_apply_eq_zero H u n (by omega),
      finiteHead_apply_eq_zero H (toPareto u) n (by omega)]
    simp

theorem reciprocalD_finiteHead (H : ℕ) (u : ThresholdHilbert) :
    reciprocalD (finiteHead H u) = finiteHead H (reciprocalD u) := by
  apply lp.ext
  funext n
  rw [reciprocalD_apply]
  by_cases hn : n < H
  · rw [finiteHead_apply_of_lt H u n hn,
      finiteHead_apply_of_lt H (reciprocalD u) n hn, reciprocalD_apply]
  · rw [finiteHead_apply_eq_zero H u n (by omega),
      finiteHead_apply_eq_zero H (reciprocalD u) n (by omega), zero_div]

theorem dualTransport_finiteHead (H : ℕ) (u : QHilbert) :
    dualTransport (finiteHead H u) = finiteHead H (dualTransport u) := by
  rw [dualTransport_apply, toPareto_finiteHead, reciprocalD_finiteHead]
  apply lp.ext
  funext n
  change (finiteHead H (toPareto u)) n + (finiteHead H (reciprocalD (toPareto u))) n =
    (finiteHead H (toPareto u + reciprocalD (toPareto u))) n
  by_cases hn : n < H
  · rw [finiteHead_apply_of_lt H _ n hn, finiteHead_apply_of_lt H _ n hn,
      finiteHead_apply_of_lt H _ n hn]
    rfl
  · rw [finiteHead_apply_eq_zero H _ n (by omega), finiteHead_apply_eq_zero H _ n (by omega),
      finiteHead_apply_eq_zero H _ n (by omega), add_zero]

theorem dualTransport_tail (H : ℕ) (u : QHilbert) :
    dualTransport (tail H u) = tail H (dualTransport u) := by
  simp only [tail, map_sub, dualTransport_finiteHead]

/-- The actual residual's exact-head identity in Pareto coordinates. -/
theorem actualResidual_pareto_tail_identity (H : ℕ) (F : QHilbert)
    (hF : F ∈ qSquarefreeCRTSpan)
    (hh : ∀ k, 0 < k → k ≤ H → qSequence F k = 1) :
    zetaTwo * ‖limitingResidual‖ ^ 2 =
      inner ℝ (tail H (dualTransport limitingResidual)) (hilbertOne - toPareto F) := by
  rw [← dualTransport_tail]
  have he : hilbertOne - toPareto F = toPareto (qOne - F) := by
    rw [show toPareto (qOne - F) = toPareto qOne - toPareto F from
      toParetoLinear.map_sub qOne F, toPareto_qOne]
  rw [he, dualTransport_pairing]
  exact congrArg (zetaTwo * ·) (exact_head_residual_tail_identity H F hF hh)

theorem actualResidual_pareto_tail_sq_bound (H : ℕ) (F : QHilbert)
    (hF : F ∈ qSquarefreeCRTSpan)
    (hh : ∀ k, 0 < k → k ≤ H → qSequence F k = 1) :
    zetaTwo ^ 2 * ‖limitingResidual‖ ^ 4 ≤
      ‖tail H (dualTransport limitingResidual)‖ ^ 2 * ‖hilbertOne - toPareto F‖ ^ 2 := by
  have h := abs_real_inner_le_norm (tail H (dualTransport limitingResidual))
    (hilbertOne - toPareto F)
  rw [← actualResidual_pareto_tail_identity H F hF hh,
    abs_of_nonneg (mul_nonneg zetaTwo_pos.le (sq_nonneg _))] at h
  have hs := mul_self_le_mul_self (mul_nonneg zetaTwo_pos.le (sq_nonneg ‖limitingResidual‖)) h
  nlinarith

theorem paretoSequence_reciprocalD (u : ThresholdHilbert) (k : ℕ) :
    hilbertSequence (reciprocalD u) k = hilbertSequence u k / (k : ℝ) := by
  cases k with
  | zero => simp
  | succ n =>
    simp only [hilbertSequence_succ, reciprocalD_apply, Nat.cast_add, Nat.cast_one]
    ring

/-- Physical dual coordinates acquire the exact positive factor 1 + 1/k. -/
theorem dualTransport_sequence (u : QHilbert) (k : ℕ) :
    hilbertSequence (dualTransport u) k = (1 + 1 / (k : ℝ)) * qSequence u k := by
  change hilbertSequenceLinear (toPareto u + reciprocalD (toPareto u)) k = _
  rw [map_add]
  change hilbertSequence (toPareto u) k + hilbertSequence (reciprocalD (toPareto u)) k = _
  rw [paretoSequence_reciprocalD, toPareto_sequence]
  ring

/-- This is a precise additional arithmetic target, not a consequence of
changing coordinates: boundedness of the corrected dual residual forces closure. -/
theorem actualResidual_eq_zero_iff_dual_physically_bounded :
    limitingResidual = 0 ↔ ∃ C : ℝ, 0 ≤ C ∧
      ∀ k : ℕ, |hilbertSequence (dualTransport limitingResidual) k| ≤ C := by
  constructor
  · intro hr
    refine ⟨0, le_rfl, ?_⟩
    intro k
    change |hilbertSequenceLinear (dualTransport limitingResidual) k| ≤ 0
    simp only [hr, map_zero, Pi.zero_apply, abs_zero, le_refl]
  · rintro ⟨C, hC, hb⟩
    apply limitingResidual_eq_zero_iff_physically_bounded.mpr
    refine ⟨C, hC, ?_⟩
    intro k
    have hfac : 1 ≤ 1 + 1 / (k : ℝ) := by
      have hd : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
      linarith
    have hm : |qSequence limitingResidual k| ≤
        (1 + 1 / (k : ℝ)) * |qSequence limitingResidual k| :=
      le_mul_of_one_le_left (abs_nonneg _) hfac
    have hbound := hb k
    rw [dualTransport_sequence, abs_mul, abs_of_nonneg (by positivity)] at hbound
    exact hm.trans hbound

end RiemannResearch.RH.QParetoResidualDualTransport
