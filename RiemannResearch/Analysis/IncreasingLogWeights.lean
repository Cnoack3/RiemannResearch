/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Increasing power weights against logarithmic error profiles

The primitive `(exp (δ*s)-1)*(c+s)^(-α)/(1-α)` dominates the
positive density `δ*exp (δ*s)*(c+s)^(-α)` when `δ ≥ 0`, `c > 0`,
and `0 ≤ α < 1`. This gives a uniform finite Abel kernel estimate,
including triangular exponents tending to zero. This is an elementary
calculus estimate developed for the quantitative Möbius endpoint consumer.
-/

noncomputable section
open Set
open scoped BigOperators
namespace RiemannResearch.Analysis

private theorem exp_sub_one_le_mul_exp (z : ℝ) :
    Real.exp z - 1 ≤ z * Real.exp z := by
  have h := mul_le_mul_of_nonneg_right (Real.one_sub_le_exp_neg z)
    (Real.exp_nonneg z)
  rw [← Real.exp_add] at h
  norm_num at h
  nlinarith

/-- A finite increment estimate for the primitive controlling increasing
exponential weights against a decreasing shifted power profile. -/
theorem increasingExp_shiftedRpow_increment_le
    {δ α c a b : ℝ} (hδ : 0 ≤ δ) (hc : 0 < c)
    (hα : 0 ≤ α) (hα1 : α < 1) (ha : 0 ≤ a) (hab : a ≤ b) :
    (1 - α) * (Real.exp (δ * b) - Real.exp (δ * a)) * (c + b) ^ (-α) ≤
      (Real.exp (δ * b) - 1) * (c + b) ^ (-α) -
        (Real.exp (δ * a) - 1) * (c + a) ^ (-α) := by
  let H : ℝ → ℝ := fun t =>
    (Real.exp (δ * t) - 1) * (c + t) ^ (-α) -
      (1 - α) * Real.exp (δ * t) * (c + b) ^ (-α)
  let D : ℝ → ℝ := fun t =>
    δ * Real.exp (δ * t) * (c + t) ^ (-α) -
      α * (Real.exp (δ * t) - 1) * (c + t) ^ (-α - 1) -
      (1 - α) * δ * Real.exp (δ * t) * (c + b) ^ (-α)
  have hder (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt H (D t) t := by
    have hct : c + t ≠ 0 := ne_of_gt (by linarith [ht.1])
    have he := ((hasDerivAt_id t).const_mul δ).exp
    have hr := ((hasDerivAt_id t).const_add c).rpow_const (p := -α) (Or.inl hct)
    apply (((he.sub_const 1).mul hr).sub
      ((he.const_mul (1 - α)).mul_const ((c + b) ^ (-α)))).congr_deriv
    dsimp only [D, id_eq]
    ring
  have hD (t : ℝ) (ht : t ∈ Icc a b) : 0 ≤ D t := by
    have ht0 : 0 ≤ t := ha.trans ht.1
    have hct : 0 < c + t := by linarith
    have hpow : (c + t) ^ (-α) = (c + t) * (c + t) ^ (-α - 1) := by
      calc
        (c + t) ^ (-α) = (c + t) ^ ((-α - 1) + 1) := by congr 1; ring
        _ = (c + t) ^ (-α - 1) * (c + t) := Real.rpow_add_one (ne_of_gt hct) _
        _ = _ := mul_comm _ _
    have he : Real.exp (δ * t) - 1 ≤ δ * Real.exp (δ * t) * (c + t) := by
      have hx := exp_sub_one_le_mul_exp (δ * t)
      have hy : 0 ≤ δ * c * Real.exp (δ * t) := by positivity
      nlinarith
    have hq : 0 ≤ (c + t) ^ (-α - 1) := Real.rpow_nonneg hct.le _
    have hpr : α * (Real.exp (δ * t) - 1) * (c + t) ^ (-α - 1) ≤
        α * δ * Real.exp (δ * t) * (c + t) ^ (-α) := by
      rw [hpow]
      have hh := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right he hq) hα
      nlinarith
    have hprofile : (c + b) ^ (-α) ≤ (c + t) ^ (-α) :=
      Real.rpow_le_rpow_of_nonpos hct (by linarith [ht.2]) (by linarith)
    have hz : 0 ≤ (1 - α) * δ * Real.exp (δ * t) := by positivity
    have hh := mul_le_mul_of_nonneg_left hprofile hz
    dsimp [D]
    nlinarith
  have hm : MonotoneOn H (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · intro t ht
      exact (hder t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hder t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hder t (interior_subset ht)).deriv]
      exact hD t (interior_subset ht)
  have hh := hm (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  dsimp [H] at hh
  nlinarith

/-- The full right-endpoint sum has a bound uniform in the nonnegative
exponent. The constant does not deteriorate as the exponent tends to zero. -/
theorem increasingExp_shiftedRpow_sum_le
    {δ α c : ℝ} (hδ : 0 ≤ δ) (hc : 0 < c)
    (hα : 0 ≤ α) (hα1 : α < 1)
    (s : ℕ → ℝ) (hs : Monotone s) (hs0 : s 0 = 0) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      (Real.exp (δ * s (n + 1)) - Real.exp (δ * s n)) *
        (c + s (n + 1)) ^ (-α)) ≤
      ((Real.exp (δ * s N) - 1) * (c + s N) ^ (-α)) / (1 - α) := by
  have hscaled : (1 - α) * (∑ n ∈ Finset.range N,
      (Real.exp (δ * s (n + 1)) - Real.exp (δ * s n)) *
        (c + s (n + 1)) ^ (-α)) ≤
      (Real.exp (δ * s N) - 1) * (c + s N) ^ (-α) := by
    induction N with
    | zero => simp [hs0]
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hn : 0 ≤ s N := by simpa [hs0] using hs (Nat.zero_le N)
      have hinc := increasingExp_shiftedRpow_increment_le hδ hc hα hα1 hn
        (hs (Nat.le_succ N))
      nlinarith
  apply (le_div_iff₀ (by linarith : 0 < 1 - α)).mpr
  simpa [mul_comm] using hscaled

/-- Natural power increments preserve the shifted logarithmic decay
profile with the explicit constant `1/(1-α)`. -/
theorem increasingPower_logProfile_sum_le
    {δ α c : ℝ} (hδ : 0 ≤ δ) (hc : 0 < c)
    (hα : 0 ≤ α) (hα1 : α < 1) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      (((n : ℝ) + 2) ^ δ - ((n : ℝ) + 1) ^ δ) *
        (c + Real.log ((n : ℝ) + 2)) ^ (-α)) ≤
      ((((N : ℝ) + 1) ^ δ - 1) *
        (c + Real.log ((N : ℝ) + 1)) ^ (-α)) / (1 - α) := by
  have hm : Monotone (fun n : ℕ => Real.log ((n : ℝ) + 1)) := by
    intro m n hmn
    apply Real.log_le_log (by positivity)
    exact_mod_cast Nat.add_le_add_right hmn 1
  have h := increasingExp_shiftedRpow_sum_le hδ hc hα hα1
    (fun n : ℕ => Real.log ((n : ℝ) + 1)) hm (by simp) N
  have hexp (n : ℕ) :
      Real.exp (δ * Real.log ((n : ℝ) + 1)) = ((n : ℝ) + 1) ^ δ := by
    rw [Real.rpow_def_of_pos (by positivity), mul_comm]
  simp_rw [hexp] at h
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using h

end RiemannResearch.Analysis
