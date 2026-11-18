/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroDensityLogExcess
import RiemannResearch.Analysis.FiniteStrictTail
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Integral of the inclusive zero count over the threshold

On the actual window `H < Im ρ ≤ T`, the right log excess is the integral
of the inclusive count from the source threshold to the line `Re s = 1`.
The finite identity retains analytic multiplicities and both height
endpoints.
-/

noncomputable section
open MeasureTheory Set

namespace RiemannResearch.Analysis.ActualZeroOrdinate
open Zeta23

private theorem intervalIntegrable_windowZero (H α β : ℝ) (ρ : ℂ) (m : ℝ) :
    IntervalIntegrable
      (fun σ : ℝ => m * (if H < ρ.im ∧ σ ≤ ρ.re then 1 else 0)) volume α β := by
  by_cases hw : H < ρ.im
  · have heq : (fun σ : ℝ => m * (if H < ρ.im ∧ σ ≤ ρ.re then 1 else 0)) =
        (Iic ρ.re).indicator (fun _ => m) := by
      funext σ
      by_cases hσ : σ ≤ ρ.re <;> simp [Set.indicator, hw, hσ]
    rw [heq]
    have hc := (continuous_const : Continuous (fun _ : ℝ => m)).intervalIntegrable
      (μ := volume) α β
    exact intervalIntegrable_iff.mpr (hc.def'.indicator measurableSet_Iic)
  · simp [hw]

/-- On every finite threshold interval the actual inclusive window count is
integrable. -/
theorem intervalIntegrable_rightInclusiveWindow (H T α β : ℝ) :
    IntervalIntegrable (rightInclusiveWindow H T) volume α β := by
  unfold rightInclusiveWindow realSum
  apply intervalIntegrable_iff.mpr
  exact integrable_finsetSum (cutoff T) (fun ρ _ =>
    (intervalIntegrable_windowZero H α β ρ (zeroMult ρ : ℝ)).def')

/-- Exact layer-cake formula for the actual log excess, with the inclusive
threshold convention of the density theorems. For each zero, including
equality at the threshold changes the integrand only on a null singleton. -/
theorem rightLogExcessWindow_eq_integral_rightInclusiveWindow (H T α : ℝ) (hα : α ≤ 1) :
    rightLogExcessWindow H T α = ∫ σ in α..(1 : ℝ), rightInclusiveWindow H T σ := by
  classical
  simp only [rightLogExcessWindow, rightInclusiveWindow, realSum]
  rw [intervalIntegral.integral_finsetSum (fun ρ _ =>
    intervalIntegrable_windowZero H α 1 ρ (zeroMult ρ : ℝ))]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [intervalIntegral.integral_const_mul]
  by_cases hw : H < ρ.im
  · simp only [hw, true_and, if_true]
    have hendpoint :
        (∫ σ in α..(1 : ℝ), if σ ≤ ρ.re then (1 : ℝ) else 0) =
          ∫ σ in α..(1 : ℝ), if σ < ρ.re then (1 : ℝ) else 0 := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [volume.ae_ne ρ.re] with σ hne _
      have h : σ ≤ ρ.re ↔ σ < ρ.re :=
        ⟨fun hle => lt_of_le_of_ne hle hne, le_of_lt⟩
      simp only [h]
    have hre : ρ.re ≤ 1 := (mem_cutoff.mp hρ).1.2.2.le
    rw [hendpoint, FiniteStrictTail.integral_strict_cut id (fun _ => (1 : ℝ))
      continuous_const (fun σ => hasDerivAt_id σ) α 1 ρ.re hα hre]
    by_cases ht : α < ρ.re
    · simp [ht, max_eq_right (sub_nonneg.mpr ht.le)]
    · simp [ht, max_eq_left (sub_nonpos.mpr (le_of_not_gt ht))]
  · simp [hw]

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.rightLogExcessWindow_eq_integral_rightInclusiveWindow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rightLogExcessWindow_eq_integral_rightInclusiveWindow

end RiemannResearch.Analysis.ActualZeroOrdinate
