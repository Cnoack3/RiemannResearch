/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Scalar logarithmic margins and exponential remainder decay

These elementary real asymptotic lemmas serve the actual zero-density cutoff
and retained finite-height harmonic remainder. They assert no zeta estimate.
-/

open Filter
namespace Real
theorem cubic_mul_exp_neg_half_tendsto_zero :
    Tendsto (fun L : ℝ => ((1+L^2)*(1+L))*Real.exp (-L/2))
      atTop (nhds 0) := by
  have hscale : Tendsto (fun L : ℝ => L/2) atTop atTop :=
    tendsto_id.atTop_div_const (by norm_num)
  have h0 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp hscale
  have h1 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscale).const_mul (2:ℝ)
  have h2 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hscale).const_mul (4:ℝ)
  have h3 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).comp hscale).const_mul (8:ℝ)
  have h := ((h0.add h1).add h2).add h3
  convert h using 1
  · funext L
    dsimp only [Function.comp_def]
    simp only [pow_zero, pow_one, one_mul]
    rw [show -(L/2) = -L/2 by ring]
    ring
  · norm_num


theorem positivePart_div_tendsto_zero {α : Type*} {F : Filter α} (n L : α → ℝ)
    (hL : ∀ᶠ t in F, 0 < L t)
    (hn : Tendsto (fun t => n t/L t) F (nhds 0)) :
    Tendsto (fun t => max 0 (n t)/L t) F (nhds 0) := by
  have ha : Tendsto (fun t => |n t/L t|) F (nhds 0) := by simpa using hn.abs
  refine squeeze_zero' ?_ ?_ ha
  · filter_upwards [hL] with t ht
    exact div_nonneg (le_max_left _ _) ht.le
  · filter_upwards [hL] with t ht
    by_cases hn0 : 0 ≤ n t
    · rw [max_eq_right hn0, abs_of_nonneg (div_nonneg hn0 ht.le)]
    · rw [max_eq_left (le_of_not_ge hn0), zero_div]
      exact abs_nonneg _

theorem log_div_self_tendsto_zero :
    Tendsto (fun L : ℝ => Real.log L/L) atTop (nhds 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp Real.tendsto_log_atTop
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hl
  simp [Real.exp_neg, Real.exp_log hl, div_eq_mul_inv]



end Real
