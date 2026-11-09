/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Elementary exponential remainder used by damped Mobius coefficients. -/

noncomputable section
namespace Real

/-- The sharp one-sided quadratic envelope, valid on the entire positive ray. -/
theorem exp_neg_first_order_remainder (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ x - (1 - Real.exp (-x)) ∧
      x - (1 - Real.exp (-x)) ≤ x ^ 2 / 2 := by
  have hP : 0 ≤ 1 - x + x ^ 2 / 2 := by nlinarith [sq_nonneg (x - 1)]
  have hquad := Real.quadratic_le_exp_of_nonneg hx
  have hm := mul_le_mul_of_nonneg_left hquad hP
  have hfactor : (1 - x + x ^ 2 / 2) * (1 + x + x ^ 2 / 2) =
      1 + x ^ 4 / 4 := by ring
  rw [hfactor] at hm
  have hprod : 1 ≤ (1 - x + x ^ 2 / 2) * Real.exp x := by
    nlinarith [sq_nonneg (x ^ 2)]
  have hu := mul_le_mul_of_nonneg_right hprod (Real.exp_pos (-x)).le
  rw [one_mul, mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at hu
  have hl := Real.add_one_le_exp (-x)
  constructor <;> linarith


end Real
