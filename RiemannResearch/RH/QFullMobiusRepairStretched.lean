/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFullMobiusRepairRates
import RiemannResearch.RH.QMobiusStretchedEnergy
import RiemannResearch.Analysis.StretchedFloorConvolution
import RiemannResearch.Analysis.StretchedExponentialBounds
import RiemannResearch.NumberTheory.MobiusReciprocalSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Unconditional stretched saving for complete reciprocal repair energy

Source: user-provided `Reciprocal_Head_Investigation_2026-11-07.md`, Section 3.
The analytic providers are the already established complete Möbius-head
energy estimates. No assumption about the actual RH residual is inserted.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QFullDilatedMobiusRepair
open ZetaTwoHilbert ZetaTwoProbability QMobiusExactHead
open RiemannResearch.Analysis
open StretchedFloorConvolution

/-- A global complete-energy envelope with one fixed positive stretched exponent. -/
theorem exactHead_global_stretched_energy :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 / 2 ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      ‖exactHead n‖ ^ 2 ≤ C * scale a n := by
  obtain ⟨a₀, ha₀, C, hC, hsource⟩ :=
    QMobiusStretchedEnergy.exactHead_eventual_stretched_energy
  let a := min a₀ (1 / 2 : ℝ)
  have ha : 0 < a := lt_min ha₀ (by norm_num)
  have haa : a ≤ a₀ := min_le_left _ _
  have ha2 : a ≤ 1 / 2 := min_le_right _ _
  have hb : ∀ᶠ n : ℕ in atTop,
      ‖exactHead n‖ ^ 2 ≤ 6 / zetaTwo + C * scale a n := by
    filter_upwards [hsource] with n hn
    have hprof : 0 ≤ profile (LogFloorConvolution.logWeight n) := profile_nonneg (by
      have h := LogFloorConvolution.six_le_logWeight n
      linarith)
    have hexp : Real.exp (-a₀ * profile (LogFloorConvolution.logWeight n)) ≤
        Real.exp (-a * profile (LogFloorConvolution.logWeight n)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right haa hprof]
    have hmul := mul_le_mul_of_nonneg_left hexp
      (mul_nonneg hC (Nat.cast_nonneg n))
    have hn' : ‖exactHead n‖ ^ 2 ≤ 6 / zetaTwo + C * (n : ℝ) *
        Real.exp (-a₀ * profile (LogFloorConvolution.logWeight n)) := hn
    unfold scale
    nlinarith
  have hzero : ‖exactHead 0‖ ^ 2 = 0 := by
    simp [exactHead, Pareto.mobiusReciprocalSum]
  obtain ⟨D, hD, hglobal⟩ := StretchedFloorConvolution.global_envelope_of_eventual
    (fun n => ‖exactHead n‖ ^ 2) (fun n => sq_nonneg _) hzero ha.le ha2
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 6) zetaTwo_pos.le) hC hb
  exact ⟨a, ha, ha2, D, hD, hglobal⟩

/-- The entire actual floor budget retains a fixed stretched saving. -/
theorem dilationBudget_global_stretched :
    ∃ b : ℝ, 0 < b ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ N,
      dilationBudget N ≤ C * scale b N := by
  obtain ⟨a, ha, ha2, C, hC, hglobal⟩ := exactHead_global_stretched_energy
  refine ⟨a / 4, by positivity, C * ∑' k, kernel a k,
    mul_nonneg hC (tsum_nonneg (kernel_nonneg a)), ?_⟩
  intro N
  rw [dilationBudget_eq_floorConvolution]
  exact StretchedFloorConvolution.floorConvolution_le _ ha.le ha2 hC hglobal N

/-- Complete reciprocal repair energy has a fixed stretched-logarithmic saving,
with a constant independent of the input vector. -/
theorem reciprocalRepair_global_stretched_energy :
    ∃ b : ℝ, 0 < b ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ N (f : QHilbert),
      ‖reciprocalRepair N f‖ ^ 2 ≤ C * (N : ℝ) *
        Real.exp (-b * logProductPower (1 / 11)
          (6 + Real.log (N : ℝ))) * ‖f‖ ^ 2 := by
  obtain ⟨b, hb, C, hC, hbound⟩ := dilationBudget_global_stretched
  have hZ := zetaTwo_pos
  refine ⟨b, hb, 4 * zetaTwo * C, by positivity, ?_⟩
  intro N f
  calc
    ‖reciprocalRepair N f‖ ^ 2 ≤
        4 * zetaTwo * ‖f‖ ^ 2 * dilationBudget N :=
      reciprocalRepair_norm_sq_le_dilationBudget N f
    _ ≤ 4 * zetaTwo * ‖f‖ ^ 2 * (C * scale b N) :=
      mul_le_mul_of_nonneg_left (hbound N) (by positivity)
    _ = _ := by unfold scale profile LogFloorConvolution.logWeight; ring

end RiemannResearch.RH.QFullDilatedMobiusRepair
