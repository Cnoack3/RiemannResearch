/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeCompatibleHeads
import RiemannResearch.RH.SquarefreeMobiusProjection
import RiemannResearch.RH.ZetaTwoCoordinateDual
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.QSquarefreeCapacity
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Explicit squarefree repair of an approximate head

Source: research with the user, 29 October 2026. The finite interpolation
is reused from QSquarefreeCompatibleHeads. This module packages the actual
operator and its complete norm bound. Its norm is a concrete finite
operator norm, not an unresolved uniform-bound assumption.

The sharper paper estimate 15 H^(3/2) is not asserted in this module.
Producing arbitrarily accurate input approximants remains open.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeQuantitativeRepair
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open SquarefreeMobiusProjection QSquarefreeCompatibleHeads

theorem coefficient_eq_charge (d : ℕ) (f : QHilbert) :
    qCoefficientCLM d f = -Pareto.mobiusDifference d (qSequence f) := by
  change -Pareto.mobiusDifferenceCLM d (toPareto f) = _
  rw [Pareto.mobiusDifferenceCLM_apply, toPareto_sequence]

/-- The literal finite interpolation operator, including its slope correction. -/
def repairOperator (H p : ℕ) : QHilbert →L[ℝ] QHilbert :=
  (∑ d ∈ Finset.Icc 2 H, (qCoefficientCLM d).smulRight (qResidue d)) +
    ((innerSL ℝ (qSiteRiesz 1)) -
      ∑ d ∈ Finset.Icc 2 H, (1 / (d : ℝ)) • qCoefficientCLM d).smulRight
        ((p : ℝ) • qResidue p)

theorem repairOperator_apply (H p : ℕ) (f : QHilbert) :
    repairOperator H p f =
      (∑ d ∈ Finset.Icc 2 H, qCoefficientCLM d f • qResidue d) +
        ((p : ℝ) * (qSequence f 1 -
          ∑ d ∈ Finset.Icc 2 H, qCoefficientCLM d f / (d : ℝ))) • qResidue p := by
  simp only [repairOperator, add_apply,
    sum_apply, ContinuousLinearMap.smulRight_apply,
    sub_apply, smul_apply, smul_eq_mul]
  change _ + (inner ℝ (qSiteRiesz 1) f -
    ∑ d ∈ Finset.Icc 2 H, (1 / (d : ℝ)) * qCoefficientCLM d f) •
    ((p : ℝ) • qResidue p) = _
  rw [qSiteRiesz_inner 1 (by norm_num), smul_smul]
  have hs : (∑ d ∈ Finset.Icc 2 H, (1 / (d : ℝ)) * qCoefficientCLM d f) =
      ∑ d ∈ Finset.Icc 2 H, qCoefficientCLM d f / (d : ℝ) := by
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [hs, mul_comm (qSequence f 1 -
    ∑ d ∈ Finset.Icc 2 H, qCoefficientCLM d f / (d : ℝ)) (p : ℝ)]

theorem repairOperator_eq_interpolant (H p : ℕ) (hHp : H < p)
    (f : QHilbert) :
    repairOperator H p f = headInterpolant (qSequence f) H p := by
  have hpnot : p ∉ Finset.Icc 2 H := by simp only [Finset.mem_Icc]; omega
  rw [repairOperator_apply, headInterpolant, headSupport, Finset.sum_insert hpnot]
  have hlow : (∑ d ∈ Finset.Icc 2 H, qCoefficientCLM d f • qResidue d) =
      ∑ d ∈ Finset.Icc 2 H, headCoefficient (qSequence f) H p d • qResidue d := by
    apply Finset.sum_congr rfl
    intro d hd
    have hdH := (Finset.mem_Icc.mp hd).2
    rw [coefficient_eq_charge]
    simp [headCoefficient, show d ≠ p by omega]
  have hslope : qSequence f 1 -
      (∑ d ∈ Finset.Icc 2 H, qCoefficientCLM d f / (d : ℝ)) =
      headSlope (qSequence f) H := by
    simp only [coefficient_eq_charge, neg_div, Finset.sum_neg_distrib,
      sub_neg_eq_add, headSlope]
  rw [hlow, hslope]
  simp only [headCoefficient]
  exact add_comm _ _

theorem repairOperator_head (H p : ℕ) (hp : 1 < p) (hHp : H < p)
    (f : QHilbert) (n : ℕ) (hn : n ≤ H) :
    qSequence (repairOperator H p f) n = qSequence f n := by
  rw [repairOperator_eq_interpolant H p hHp]
  exact headInterpolant_exact_head (qSequence f) H p (qSequence_zero f) hp hHp n hn

/-- The corrected vector retains all input coefficients plus the signed repair. -/
def repaired (H p : ℕ) (f : QHilbert) : QHilbert :=
  f + repairOperator H p (qOne - f)

theorem repaired_exact_head (H p : ℕ) (hp : 1 < p) (hHp : H < p)
    (f : QHilbert) (n : ℕ) (hn : 0 < n) (hnH : n ≤ H) :
    qSequence (repaired H p f) n = 1 := by
  change qSequenceLinear (f + repairOperator H p (qOne - f)) n = _
  simp only [map_add, Pi.add_apply]
  change qSequence f n + qSequence (repairOperator H p (qOne - f)) n = _
  rw [repairOperator_head H p hp hHp (qOne - f) n hnH]
  change qSequence f n + qSequenceLinear (qOne - f) n = _
  simp only [map_sub, Pi.sub_apply]
  change qSequence f n + (qSequence qOne n - qSequence f n) = _
  rw [qSequence_qOne]
  simp [qOneSequence, ne_of_gt hn]

theorem repaired_legal (H p : ℕ) (hp : 2 ≤ p) (hpsf : Squarefree p)
    (f : QHilbert) (hf : f ∈ qSquarefreeCRTSpan) :
    repaired H p f ∈ qSquarefreeCRTSpan := by
  have hfcl : f ∈ ZetaTwoOptimizerStage.closure := by
    rw [QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure]
    exact qSquarefreeCRTSpan.le_topologicalClosure hf
  unfold repaired
  apply Submodule.add_mem _ hf
  rw [repairOperator_apply]
  apply Submodule.add_mem
  · apply Submodule.sum_mem
    intro d hd
    have hd2 := (Finset.mem_Icc.mp hd).1
    by_cases hsf : Squarefree d
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨d, hd2, hsf⟩, rfl⟩)
    · have he : d - 2 + 2 = d := by omega
      have hz := q_omitted_coordinate_zero (d - 2) (by simpa only [he] using hsf) hfcl
      rw [he] at hz
      rw [map_sub, q_target_coordinate d (by omega), hz,
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
      simp only [Int.cast_zero, neg_zero, sub_zero, zero_smul]
      exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨p, hp, hpsf⟩, rfl⟩)

/-- Exact full error identity before estimating its signed cross term. -/
theorem repaired_error_identity (H p : ℕ) (f : QHilbert) :
    ‖qOne - repaired H p f‖ ^ 2 =
      ‖qOne - f‖ ^ 2 - 2 * inner ℝ (qOne - f) (repairOperator H p (qOne - f)) +
        ‖repairOperator H p (qOne - f)‖ ^ 2 := by
  have he : qOne - repaired H p f =
      (qOne - f) - repairOperator H p (qOne - f) := by unfold repaired; abel
  rw [he, norm_sub_sq_real]

theorem repaired_error_le (H p : ℕ) (f : QHilbert) :
    ‖qOne - repaired H p f‖ ≤ (1 + ‖repairOperator H p‖) * ‖qOne - f‖ := by
  have he : qOne - repaired H p f =
      (qOne - f) - repairOperator H p (qOne - f) := by unfold repaired; abel
  rw [he]
  calc
    _ ≤ ‖qOne - f‖ + ‖repairOperator H p (qOne - f)‖ := norm_sub_le _ _
    _ ≤ ‖qOne - f‖ + ‖repairOperator H p‖ * ‖qOne - f‖ :=
      add_le_add le_rfl ((repairOperator H p).le_opNorm (qOne - f))
    _ = _ := by ring

/-- A sufficiently accurate input pays the explicit finite repair cost.
This does not assert existence of such an input at every head. -/
theorem repaired_energy_of_accuracy (H p : ℕ) (hH : 0 < H) (f : QHilbert)
    (haccuracy : ‖qOne - f‖ ≤
      1 / (4 * (H : ℝ) * (1 + ‖repairOperator H p‖))) :
    ‖repaired H p f‖ ^ 2 ≤ 1 + 5 / (8 * (H : ℝ)) := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hC : 0 < 1 + ‖repairOperator H p‖ := by positivity
  have he : ‖qOne - repaired H p f‖ ≤ 1 / (4 * (H : ℝ)) := by
    apply (repaired_error_le H p f).trans
    calc
      _ ≤ (1 + ‖repairOperator H p‖) *
          (1 / (4 * (H : ℝ) * (1 + ‖repairOperator H p‖))) :=
        mul_le_mul_of_nonneg_left haccuracy hC.le
      _ = _ := by field_simp
  have hn := norm_sub_le qOne (qOne - repaired H p f)
  rw [sub_sub_cancel, qOne_norm] at hn
  have hnorm : ‖repaired H p f‖ ≤ 1 + 1 / (4 * (H : ℝ)) := by linarith
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hnorm
  have hfinal : (1 + 1 / (4 * (H : ℝ))) ^ 2 ≤ 1 + 5 / (8 * (H : ℝ)) := by
    field_simp
    nlinarith
  exact hsq.trans hfinal

end RiemannResearch.RH.QSquarefreeQuantitativeRepair
