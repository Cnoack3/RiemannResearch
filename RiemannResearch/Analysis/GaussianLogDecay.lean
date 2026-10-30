/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Gaussian decay evaluated at logarithmic arguments

The exact completed-square identity is retained before its nonpositive
remainder is dropped. Polynomial Gaussian envelopes consequently dominate
every fixed exponential rate, with a global explicit constant.

Source: user-provided prime-power convergence argument, 30 October 2026.
The RH consumer and proof are documented in
RiemannResearch/RH/GaussianPolynomialPrimePowerSummability20261030.md.
These elementary estimates make no arithmetic or RH assumption.
-/

noncomputable section

namespace RiemannResearch.Analysis.GaussianLogDecay

theorem completed_square {R : ℝ} (hR : 0 < R) (c t : ℝ) :
    c*t - t^2/(4*R) = R*c^2 - (t-2*R*c)^2/(4*R) := by
  field_simp
  ring

theorem polynomial_gaussian_le {R : ℝ} (hR : 0 < R)
    (M : ℕ) (a : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (1+t)^M * Real.exp (-t^2/(4*R)) ≤
      Real.exp (R*((M : ℝ)+a)^2) * Real.exp (-a*t) := by
  have hp : (1+t)^M ≤ Real.exp ((M : ℝ)*t) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp t]) M
  have hs : ((M : ℝ)+a)*t-t^2/(4*R) ≤ R*((M : ℝ)+a)^2 := by
    rw [completed_square hR]
    exact sub_le_self _ (by positivity)
  calc
    _ ≤ Real.exp ((M : ℝ)*t) * Real.exp (-t^2/(4*R)) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)
    _ ≤ _ := by
      rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
      convert sub_le_sub_right hs (a*t) using 1 <;> ring

theorem exp_neg_nat_mul_log {x : ℝ} (hx : 0 < x) (k : ℕ) :
    Real.exp (-(k : ℝ)*Real.log x) = (x^k)⁻¹ := by
  rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hx]

end RiemannResearch.Analysis.GaussianLogDecay
