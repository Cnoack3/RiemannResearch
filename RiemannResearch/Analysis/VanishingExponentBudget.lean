/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.SubpolynomialWindowGrowth
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Vanishing exponent budgets

Source: CRT tail-energy research, 13 October 2026. A countable budget with
exponents tending to zero gives logarithmic subpolynomial growth.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.Analysis.SubpolynomialWindow

theorem relativeLog_tendsto_zero_of_reciprocal_exponent
    (x E : ℕ → ℝ)
    (hx : ∀ j : ℕ, (j : ℝ) + 2 ≤ x j)
    (hE : ∀ j, 0 ≤ E j)
    (hbudget : ∀ j, E j ≤ (x j) ^ (1 / ((j : ℝ) + 1))) :
    Tendsto (fun j => Real.log (1 + E j) / Real.log (x j))
      atTop (𝓝 0) := by
  have hxTop : Tendsto x atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [(tendsto_natCast_atTop_atTop :
      Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop).eventually
        (eventually_ge_atTop b)] with j hj
    linarith [hx j]
  have hnTop : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun j => by change (j : ℝ) ≤ (j : ℝ) + 1; linarith)
      tendsto_natCast_atTop_atTop
  have hup : Tendsto (fun j => Real.log 2 / Real.log (x j) +
      1 / ((j : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, add_zero] using
      ((Real.tendsto_log_atTop.comp hxTop).const_div_atTop (Real.log 2)).add
        (hnTop.const_div_atTop 1)
  apply squeeze_zero _ _ hup
  · intro j
    exact div_nonneg (Real.log_nonneg (by linarith [hE j]))
      (Real.log_nonneg (by linarith [hx j, Nat.cast_nonneg (α := ℝ) j]))
  · intro j
    have hx1 : 1 < x j := by linarith [hx j, Nat.cast_nonneg (α := ℝ) j]
    have hx0 : 0 < x j := by linarith
    have hlogx : 0 < Real.log (x j) := Real.log_pos hx1
    have hp : 1 ≤ (x j) ^ (1 / ((j : ℝ) + 1)) :=
      Real.one_le_rpow hx1.le (by positivity)
    have hplus : 1 + E j ≤ 2 * (x j) ^ (1 / ((j : ℝ) + 1)) := by
      linarith [hbudget j]
    have hl := Real.log_le_log (by linarith [hE j] : 0 < 1 + E j) hplus
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (ne_of_gt (Real.rpow_pos_of_pos hx0 _)), Real.log_rpow hx0] at hl
    apply (div_le_iff₀ hlogx).mpr
    calc
      _ ≤ Real.log 2 + (1 / ((j : ℝ) + 1)) * Real.log (x j) := hl
      _ = _ := by field_simp

end RiemannResearch.Analysis.SubpolynomialWindow
