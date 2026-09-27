/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Elementary polynomial cutoff budgets

The exponent hypothesis is precisely the condition making a scalar
M^(-epsilon) tail harmless after a head of length H is squared.
-/

noncomputable section
namespace RiemannResearch.Analysis

theorem le_succ_pow (H k : ℕ) (hk : 1 ≤ k) : H ≤ (H + 1) ^ k := by
  cases k with
  | zero => exact False.elim (Nat.not_succ_le_zero 0 hk)
  | succ k =>
    rw [pow_succ]
    have hp : 0 < (H + 1) ^ k := by positivity
    nlinarith

theorem head_mul_polynomial_cutoff_rpow_le (H k : ℕ) (ε : ℝ)
    (hscale : 1 ≤ 2 * (k : ℝ) * ε) :
    (H : ℝ) * (((H + 1) ^ k : ℕ) : ℝ) ^ (-2 * ε) ≤
      (H : ℝ) / ((H : ℝ) + 1) := by
  have hx : (1 : ℝ) ≤ (H : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) H]
  have hxp : (0 : ℝ) < (H : ℝ) + 1 := by positivity
  have he : (k : ℝ) * (-2 * ε) ≤ -1 := by nlinarith
  have hb : (((H + 1) ^ k : ℕ) : ℝ) ^ (-2 * ε) ≤
      ((H : ℝ) + 1) ^ (-1 : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one, ← Real.rpow_natCast,
      ← Real.rpow_mul hxp.le]
    exact Real.rpow_le_rpow_of_exponent_le hx he
  have hm := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg H : (0 : ℝ) ≤ H)
  simpa only [Real.rpow_neg_one, div_eq_mul_inv] using hm

theorem head_mul_polynomial_cutoff_rpow_le_one (H k : ℕ) (ε : ℝ)
    (hscale : 1 ≤ 2 * (k : ℝ) * ε) :
    (H : ℝ) * (((H + 1) ^ k : ℕ) : ℝ) ^ (-2 * ε) ≤ 1 := by
  apply (head_mul_polynomial_cutoff_rpow_le H k ε hscale).trans
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (H : ℝ) + 1)).mpr
  linarith

/-- The minimum admissible head size is included even at the index H=0. -/
theorem natural_polynomial_cutoff_budget (H k : ℕ) (ε : ℝ)
    (hk : 1 ≤ k) (hscale : 1 ≤ 2 * (k : ℝ) * ε) :
    H ≤ (H + 1) ^ k ∧
      (H : ℝ) * (((H + 1) ^ k : ℕ) : ℝ) ^ (-2 * ε) ≤ 1 :=
  ⟨le_succ_pow H k hk, head_mul_polynomial_cutoff_rpow_le_one H k ε hscale⟩

end RiemannResearch.Analysis
