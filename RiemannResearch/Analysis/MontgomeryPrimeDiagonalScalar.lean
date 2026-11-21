/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Elementary exponential comparisons for the classical quantitative prime number theorem. -/

open Real
noncomputable section
namespace RiemannResearch.Analysis.MontgomeryHorizontalBessel

/-- A square-root times one logarithm is absorbed into the classical PNT
envelope, uniformly from one, with an explicit constant at any rate. -/
theorem diagonal_sqrt_mul_one_add_log_le_rootExp (b : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    Real.sqrt x * (1 + Real.log x) ≤
      (5 * Real.exp (b ^ 2)) * x * Real.exp (-b * Real.sqrt (Real.log x)) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hL := Real.log_nonneg hx
  have he : 1 + Real.log x ≤ 5 * Real.exp (Real.log x / 4) := by
    have h := Real.add_one_le_exp (Real.log x / 4)
    linarith [Real.exp_pos (Real.log x / 4)]
  have hs : Real.sqrt x = Real.exp (Real.log x / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0]
    congr 1
    ring
  have hquad := sq_nonneg (b - Real.sqrt (Real.log x) / 2)
  have hle : Real.log x / 2 + Real.log x / 4 ≤ b ^ 2 + Real.log x + -b * Real.sqrt (Real.log x) := by
    nlinarith only [hquad, Real.sq_sqrt hL]
  calc
    _ ≤ Real.sqrt x * (5 * Real.exp (Real.log x / 4)) :=
      mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg x)
    _ = 5 * Real.exp (Real.log x / 2 + Real.log x / 4) := by rw [hs, Real.exp_add]; ring
    _ ≤ 5 * Real.exp (b ^ 2 + Real.log x + -b * Real.sqrt (Real.log x)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) (by norm_num)
    _ = _ := by rw [Real.exp_add, Real.exp_add, Real.exp_log hx0]; ring

/-- All points from the square-root split onward retain half the
coefficient of the root-log exponential. -/
theorem diagonal_rootExp_mono_from_sqrt {a x t : ℝ} (ha : 0 ≤ a) (hx : 1 ≤ x)
    (ht : Real.sqrt x ≤ t) :
    Real.exp (-a * Real.sqrt (Real.log t)) ≤
      Real.exp (-(a / 2) * Real.sqrt (Real.log x)) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hs : 1 ≤ Real.sqrt x := by simpa using Real.sqrt_le_sqrt hx
  have ht1 := hs.trans ht
  have hl := Real.log_le_log (Real.sqrt_pos.2 hx0) ht
  rw [Real.log_sqrt hx0.le] at hl
  have h2 : Real.sqrt (Real.log x) ≤ 2 * Real.sqrt (Real.log t) := by
    nlinarith only [hl, Real.sq_sqrt (Real.log_nonneg hx), Real.sq_sqrt (Real.log_nonneg ht1),
      Real.sqrt_nonneg (Real.log t), Real.sqrt_nonneg (Real.log x), Real.log_nonneg ht1]
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_le_mul_of_nonneg_left h2 ha]

end RiemannResearch.Analysis.MontgomeryHorizontalBessel
