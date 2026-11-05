/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.StretchedExponentialBounds

/-! Bounds for the log increments of the arithmetic Mertens profile. -/
noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.Analysis

/-- The elementary logarithmic-product profile eventually admits every fixed
coefficient in the log-increment bound. -/
theorem shifted_logProductPower_eventual_log_increment (β a : ℝ)
    (hβ : 0 ≤ β) (hβ2 : 2 * β < 1) (ha : 0 ≤ a) :
    ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ≤ y →
      a * (logProductPower β (6 + Real.log y) - logProductPower β (6 + Real.log x)) ≤
        Real.log y - Real.log x := by
  have hs : Tendsto (fun x : ℝ => 6 + Real.log x) atTop atTop := by
    apply tendsto_atTop.2
    intro r
    filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop r)] with x hx
    linarith
  have habs := ((tendsto_logProductPower_div_self β hβ hβ2).comp hs).const_mul a
  simp only [mul_zero] at habs
  have hband := (tendsto_order.1 habs).2 (1 : ℝ) (by norm_num)
  filter_upwards [hband, eventually_ge_atTop (1 : ℝ)] with x hx hx1 y hxy
  let s : ℝ := 6 + Real.log x
  let t : ℝ := 6 + Real.log y
  have hs6 : 6 ≤ s := by dsimp [s]; linarith [Real.log_nonneg hx1]
  have hs0 : 0 < s := by linarith
  have hst : s ≤ t := by
    dsimp [s,t]
    linarith [Real.log_le_log (by linarith : 0 < x) hxy]
  have ht0 : 0 < t := hs0.trans_le hst
  have hr := (div_le_div_iff₀ ht0 hs0).1 (logProductPower_div_antitone β hβ hβ2.le hs6 hst)
  have hstep : logProductPower β t - logProductPower β s ≤
      (logProductPower β s / s) * (t - s) := by
    calc
      _ ≤ (logProductPower β s * (t-s)) / s := (le_div_iff₀ hs0).2 (by nlinarith only [hr])
      _ = _ := by ring
  have hsmall : a * (logProductPower β s / s) ≤ 1 := hx.le
  have hh := mul_le_mul_of_nonneg_right hsmall (sub_nonneg.mpr hst)
  calc
    a * (logProductPower β t - logProductPower β s)
        ≤ a * ((logProductPower β s / s) * (t - s)) := mul_le_mul_of_nonneg_left hstep ha
    _ = (a * (logProductPower β s / s)) * (t - s) := (mul_assoc _ _ _).symm
    _ ≤ 1 * (t - s) := hh
    _ = Real.log y - Real.log x := by dsimp [t,s]; ring

end RiemannResearch.Analysis
