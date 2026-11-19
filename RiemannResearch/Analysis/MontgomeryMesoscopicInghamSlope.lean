/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MontgomeryMesoscopicUnitSlope
import RiemannResearch.Analysis.MontgomeryTransitionHorizontalDefect

/-! # Mesoscopic unit slope using the internal Ingham horizontal bound

The fourth moment supplied internally by the zero-density route costs four
powers of log log T. It covers every power phase u = (log T)^q with q < 2/3.
The positive-cutoff third-signal and actual prime mean-square inputs remain
explicit. -/

noncomputable section
open Filter Set
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryHorizontalBessel
open MontgomeryHorizontalTransfer MontgomeryFormFactor

theorem raw_mesoscopic_combined_of_ingham
    (hthird : PositiveCutoffThirdSignalSource) (hprime : QuadraticPrimeSignalMeanSquareSource)
    (u : ℝ → ℝ) (hu : Tendsto u atTop atTop)
    (hsmall : Tendsto (fun T => (u T)^3*(Real.log (Real.log T))^4/(Real.log T)^2) atTop (𝓝 0)) :
    Tendsto (fun T => formFactor T (u T/Real.log T) / mesoscopicMain T (u T)) atTop (𝓝 1) := by
  have hcube : Tendsto (fun T => (u T)^3/(Real.log T)^2) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hsmall
    · filter_upwards [hu.eventually_ge_atTop 0] with T hT
      positivity
    · filter_upwards [hu.eventually_ge_atTop 0,
        (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1] with T hT hLL
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact le_mul_of_one_le_right (pow_nonneg hT _) (one_le_pow₀ hLL)
  have hS : ∀ᶠ T : ℝ in atTop, u T/Real.log T ≤ mesoscopicMain T (u T) := by
    filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
    exact div_le_div_of_nonneg_right (le_add_of_nonneg_left (div_nonneg (sq_nonneg _) (sq_nonneg _)))
      (Real.log_pos hT).le
  have hsharp := sharp_mesoscopic_combined_asymptotic hthird hprime u hu
    ((eventually_mesoscopic_band hu hcube (by norm_num : 0 < (1/2:ℝ))).mono
      (fun T h => by linarith only [h.2]))
  apply raw_relative_asymptotic_of_defect _ _ _ hsharp (mesoscopic_defect_relative_ingham u _ hu hsmall hS)
  filter_upwards [hS,hu.eventually_gt_atTop 0,eventually_gt_atTop (1:ℝ)] with T hT hU hT1
  exact (div_pos hU (Real.log_pos hT1)).trans_le hT

/-- The scalar spike condition is sufficient with the stronger internal
horizontal range u³ (log log T)^4 / (log T)^2 → 0. -/
theorem raw_mesoscopic_unit_slope_of_ingham
    (hthird : PositiveCutoffThirdSignalSource) (hprime : QuadraticPrimeSignalMeanSquareSource)
    (u : ℝ → ℝ) (hu : Tendsto u atTop atTop)
    (hsmall : Tendsto (fun T => (u T)^3*(Real.log (Real.log T))^4/(Real.log T)^2) atTop (𝓝 0))
    (hspike : Tendsto (fun T => (Real.log T)^2/(Real.exp (u T))^2/(u T)) atTop (𝓝 0)) :
    Tendsto (fun T => formFactor T (u T/Real.log T) / (u T/Real.log T)) atTop (𝓝 1) := by
  simpa only [zero_add] using raw_spike_ratio_of_combined hu
    (raw_mesoscopic_combined_of_ingham hthird hprime u hu hsmall) hspike

end RiemannResearch.Analysis.MontgomeryHorizontalBessel
