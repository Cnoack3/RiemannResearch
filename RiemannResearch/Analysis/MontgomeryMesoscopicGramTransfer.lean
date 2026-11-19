/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MontgomeryRawSecondOrderTransition

/-! # Relative horizontal transfer at mesoscopic frequencies

An absolute comparison of square roots transfers a relative asymptotic when the
defect divided by the chosen main term tends to zero. For the linear term
u/log T, the reflected quartic estimate requires u³/(log T)² → 0. -/

noncomputable section
open Filter Set
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryHorizontalBessel
open MontgomeryHorizontalTransfer MontgomeryFormFactor

/-- Arbitrary positive normalizations preserve a unit relative asymptotic
when the defect is negligible on the same scale. -/
theorem raw_relative_asymptotic_of_defect (α scale : ℝ → ℝ)
    (hpos : ∀ᶠ T : ℝ in atTop, 0 < scale T)
    (hsharp : Tendsto (fun T => sharpFormFactor T (α T) / scale T) atTop (𝓝 1))
    (hdef : Tendsto (fun T => horizontalDefect T (α T) / scale T) atTop (𝓝 0)) :
    Tendsto (fun T => formFactor T (α T) / scale T) atTop (𝓝 1) := by
  let R (T : ℝ) := Real.sqrt (formFactor T (α T) / scale T)
  let S (T : ℝ) := Real.sqrt (sharpFormFactor T (α T) / scale T)
  have hs : Tendsto S atTop (𝓝 1) := by
    simpa only [S, Function.comp_def, Real.sqrt_one] using
      (Real.continuous_sqrt.continuousAt (x:=1)).tendsto.comp hsharp
  have hd : Tendsto (fun T => Real.sqrt (horizontalDefect T (α T) / scale T)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.continuousAt (x:=0)).tendsto.comp hdef
  have hdiff : Tendsto (fun T => R T-S T) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hd
    filter_upwards [hpos] with T hT
    dsimp only [R,S]
    rw [Real.norm_eq_abs, Real.sqrt_div' _ hT.le, Real.sqrt_div' _ hT.le,
      Real.sqrt_div' _ hT.le, ← sub_div, abs_div, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_sub_comm]
    exact div_le_div_of_nonneg_right (sqrt_horizontal_error T (α T)) (Real.sqrt_nonneg _)
  have hr : Tendsto R atTop (𝓝 1) := by
    simpa only [sub_add_cancel, zero_add] using hdiff.add hs
  have hsq := hr.pow 2
  rw [one_pow] at hsq
  apply hsq.congr'
  filter_upwards [hpos, eventually_gt_atTop (1:ℝ)] with T hT hT1
  exact Real.sq_sqrt (div_nonneg (formFactor_nonneg hT1 _) hT.le)

/-- The upper phase range eventually fits every fixed subcritical frequency
band. The algebraic hypothesis is equivalent to u = o((log T)^(2/3)) for
nonnegative phases. -/
theorem eventually_mesoscopic_band {u : ℝ → ℝ} (hu : Tendsto u atTop atTop)
    (hsmall : Tendsto (fun T => (u T)^3 / (Real.log T)^2) atTop (𝓝 0))
    {b : ℝ} (hb : 0 < b) : ∀ᶠ T : ℝ in atTop, 1 ≤ u T ∧ u T ≤ b * Real.log T := by
  filter_upwards [hu.eventually_ge_atTop 1, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    hsmall.eventually_le_const (pow_pos hb 3)] with T hU hL hq
  refine ⟨hU, ?_⟩
  have hL0 : 0 < Real.log T := zero_lt_one.trans_le hL
  have hU3 := (div_le_iff₀ (pow_pos hL0 2)).mp hq
  have hL23 : (Real.log T)^2 ≤ (Real.log T)^3 := by
    rw [pow_succ]
    exact le_mul_of_one_le_right (sq_nonneg _) hL
  have hc : (u T)^3 ≤ (b*Real.log T)^3 := by
    rw [mul_pow]
    exact hU3.trans (mul_le_mul_of_nonneg_left hL23 (pow_nonneg hb.le _))
  by_contra! hlt
  exact ((pow_lt_pow_left₀ hlt (mul_nonneg hb.le hL0.le) (by decide : (3:ℕ) ≠ 0))).not_ge hc

/-- Relative quartic defect on any main term at least u/log T. -/
theorem mesoscopic_defect_relative {a : ℝ} (ha : 0 < a)
    (hQ : ReflectedQuarticDefectEstimate a) (u scale : ℝ → ℝ)
    (hu : Tendsto u atTop atTop)
    (hsmall : Tendsto (fun T => (u T)^3 / (Real.log T)^2) atTop (𝓝 0))
    (hscale : ∀ᶠ T : ℝ in atTop, u T / Real.log T ≤ scale T) :
    Tendsto (fun T => horizontalDefect T (u T/Real.log T) / scale T) atTop (𝓝 0) := by
  obtain ⟨C,hC,hq⟩ := hQ
  have hz : Tendsto (fun T => (16*C)*((u T)^3/(Real.log T)^2)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hsmall.const_mul (16*C)
  apply squeeze_zero' _ _ hz
  · filter_upwards [hscale, hu.eventually_gt_atTop 0, eventually_gt_atTop (1:ℝ)] with T hS hU hT
    have hL := Real.log_pos hT
    have hd : 0 ≤ horizontalDefect T (u T / Real.log T) := by
      unfold horizontalDefect defectIntegral
      exact div_nonneg (MeasureTheory.integral_nonneg (fun _ =>
        mul_nonneg (Real.exp_pos _).le (sq_nonneg _))) (by positivity)
    exact div_nonneg hd ((div_pos hU hL).le.trans hS)
  · filter_upwards [hq, hscale, eventually_gt_atTop (1:ℝ),
      eventually_mesoscopic_band hu hsmall (show 0 < a/4 by positivity)]
      with T hTQ hS hT hband
    let L := Real.log T
    have hL : 0 < L := Real.log_pos hT
    have hU : 0 < u T := zero_lt_one.trans_le hband.1
    let α := u T / L
    have hα : 0 < α := div_pos hU hL
    have harg : α * L = u T := div_mul_cancel₀ _ hL.ne'
    have hβ : |α*L| ≤ a*L/4 := by rw [harg, abs_of_pos hU]; linarith only [hband.2]
    have hD := hTQ α hβ
    change horizontalDefect T α ≤ C*(1+|α*L|)^4/L^3 at hD
    rw [harg, abs_of_pos hU] at hD
    have hp : (1+u T)^4 ≤ (2*u T)^4 := pow_le_pow_left₀ (by linarith) (by linarith only [hband.1]) 4
    have hD' := hD.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp hC) (pow_nonneg hL.le _))
    have hSP : 0 < scale T := hα.trans_le hS
    apply (div_le_iff₀ hSP).mpr
    have hK : 0 ≤ (16*C)*((u T)^3/L^2) := by positivity
    calc
      _ ≤ C*(2*u T)^4/L^3 := hD'
      _ = ((16*C)*((u T)^3/L^2))*α := by dsimp only [α]; field_simp [hL.ne']; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hS hK

/-- De-spiked mesoscopic slope once the complex statistic has that slope. -/
theorem raw_mesoscopic_slope_of_sharp {a : ℝ} (ha : 0 < a)
    (hQ : ReflectedQuarticDefectEstimate a) (u : ℝ → ℝ)
    (hu : Tendsto u atTop atTop)
    (hsmall : Tendsto (fun T => (u T)^3 / (Real.log T)^2) atTop (𝓝 0))
    (hsharp : Tendsto (fun T => sharpFormFactor T (u T/Real.log T) / (u T/Real.log T))
      atTop (𝓝 1)) :
    Tendsto (fun T => formFactor T (u T/Real.log T) / (u T/Real.log T)) atTop (𝓝 1) := by
  apply raw_relative_asymptotic_of_defect _ _ _ hsharp
    (mesoscopic_defect_relative ha hQ u _ hu hsmall (.of_forall fun _ => le_rfl))
  filter_upwards [hu.eventually_gt_atTop 0, eventually_gt_atTop (1:ℝ)] with T hU hT
  exact div_pos hU (Real.log_pos hT)

end RiemannResearch.Analysis.MontgomeryHorizontalBessel
