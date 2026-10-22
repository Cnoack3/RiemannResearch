/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# The obstruction for positive Abel majorants

The conclusions concern the numerical certificate obtained by multiplying
a supplied sublinear-exponential endpoint profile by an increasing weight.
They are not lower bounds for the signed arithmetic residual or its norm.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.Analysis

/-- Every fixed positive linear exponent eventually dominates any fixed
multiple of a profile whose ratio to its argument tends to zero. -/
theorem eventually_profile_lt_linear
    (P : ℝ → ℝ) (hP : Tendsto (fun T => P T / T) atTop (𝓝 0))
    (a δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, a * P T < δ * T := by
  have hlim : Tendsto (fun T => a * (P T / T)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hP.const_mul a
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hlim.eventually (gt_mem_nhds hδ)] with T hT hsmall
  apply (div_lt_iff₀ hT).mp
  simpa only [mul_div_assoc] using hsmall

/-- The exponent in a fixed increasing weight times a sublinear-exponential
endpoint profile tends to positive infinity. Neither positivity nor
monotonicity of the profile is needed. -/
theorem tendsto_linear_sub_sublinear_profile_atTop
    (P : ℝ → ℝ) (hP : Tendsto (fun T => P T / T) atTop (𝓝 0))
    (a δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun T : ℝ => δ * T - a * P T) atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [eventually_ge_atTop (2 * B / δ),
    eventually_profile_lt_linear P hP a (δ / 2) (by linarith)] with T hT hsmall
  have hlinear : 2 * B ≤ T * δ := (div_le_iff₀ hδ).mp hT
  linarith

/-- A fixed shift in logarithmic scale does not repair the terminal
positive Abel majorant. The positive leading constant is essential:
an identically zero endpoint profile is excluded. -/
theorem positiveAbel_terminal_profile_tendsto_atTop
    (P : ℝ → ℝ) (hP : Tendsto (fun T => P T / T) atTop (𝓝 0))
    (a δ C k : ℝ) (hδ : 0 < δ) (hC : 0 < C) :
    Tendsto (fun T : ℝ => C * Real.exp (δ * (T - k) - a * P T)) atTop atTop := by
  have hlin := tendsto_linear_sub_sublinear_profile_atTop P hP a δ hδ
  have hshift : Tendsto (fun T : ℝ => δ * (T - k) - a * P T) atTop atTop := by
    convert tendsto_atTop_add_const_right atTop (-δ * k) hlin using 1
    funext T
    ring
  exact (Real.tendsto_exp_atTop.comp hshift).const_mul_atTop hC

/-- Adding any nonnegative remainder to this terminal certificate cannot
make the positive Abel budget tend to zero; in fact the budget diverges.
This says nothing about cancellation in the actual signed Abel identity. -/
theorem positiveAbel_budget_tendsto_atTop
    (P : ℝ → ℝ) (hP : Tendsto (fun T => P T / T) atTop (𝓝 0))
    (a δ C k : ℝ) (hδ : 0 < δ) (hC : 0 < C)
    (L B : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hB : ∀ᶠ j in atTop, 0 ≤ B j) :
    Tendsto (fun j => C * Real.exp (δ * (L j - k) - a * P (L j)) + B j)
      atTop atTop := by
  have hterm := (positiveAbel_terminal_profile_tendsto_atTop P hP a δ C k hδ hC).comp hL
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [tendsto_atTop.mp hterm b, hB] with j hj hBj
  exact hj.trans (le_add_of_nonneg_right hBj)

/-- More generally the weight coordinate may differ from the endpoint
profile coordinate by any bounded one-sided shift. This covers the
one-index displacement in the finite Abel boundary term. -/
theorem positiveAbel_shifted_terminal_tendsto_atTop
    (P : ℝ → ℝ) (hP : Tendsto (fun T => P T / T) atTop (𝓝 0))
    (a δ C k : ℝ) (hδ : 0 < δ) (hC : 0 < C)
    (L s : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hs : ∀ᶠ j in atTop, L j - k ≤ s j) :
    Tendsto (fun j => C * Real.exp (δ * s j - a * P (L j))) atTop atTop := by
  have hterm := (positiveAbel_terminal_profile_tendsto_atTop P hP a δ C k hδ hC).comp hL
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [tendsto_atTop.mp hterm b, hs] with j hj hsj
  apply hj.trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.exp_le_exp.mpr
  exact sub_le_sub_right (mul_le_mul_of_nonneg_left hsj hδ.le) _

end RiemannResearch.Analysis
