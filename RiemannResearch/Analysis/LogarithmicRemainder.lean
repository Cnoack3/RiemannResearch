/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Logarithmic remainder at the next coefficient scale

This elementary limit comparison is used by the actual rational zeta-zero
third-coefficient reduction. The estimate is an explicit hypothesis, not
a supplied analytic theorem about zeros. Source: the comparison argument
developed for that concrete consumer; no novelty claim is made.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.Analysis

/-- An inverse-cubic logarithmic bound is negligible at the next coefficient scale. -/
theorem log_mul_tendsto_zero_of_inv_log_cube
    (E : ℝ → ℂ) (K : ℝ)
    (hbound : ∀ᶠ T : ℝ in atTop, ‖E T‖ ≤ K / (Real.log T) ^ 3) :
    Tendsto (fun T : ℝ => (Real.log T : ℂ) * E T) atTop (𝓝 0) := by
  have hi : Tendsto (fun T : ℝ => (Real.log T)⁻¹) atTop (𝓝 0) :=
    (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).comp
      Real.tendsto_log_atTop
  have hb : Tendsto (fun T : ℝ => K * ((Real.log T)⁻¹) ^ 2) atTop (𝓝 0) := by
    simpa using (hi.pow 2).const_mul K
  apply squeeze_zero_norm' _ hb
  filter_upwards [hbound, eventually_gt_atTop (1 : ℝ)] with T hT hT1
  have hL : 0 < Real.log T := Real.log_pos hT1
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
  calc
    Real.log T * ‖E T‖ ≤ Real.log T * (K / (Real.log T) ^ 3) :=
      mul_le_mul_of_nonneg_left hT hL.le
    _ = K * ((Real.log T)⁻¹) ^ 2 := by
      field_simp

end RiemannResearch.Analysis
