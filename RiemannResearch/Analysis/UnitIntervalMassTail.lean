/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # An inverse-cubic test against a density with bounded unit-interval mass

A dyadic width contrast has an inverse-cubic envelope away from zero.
The integral of its absolute value against a nonnegative density is bounded
uniformly in the number of consecutive unit intervals by an inverse-square
tail. Both ends of the telescoping estimate are retained below.
-/

noncomputable section

open MeasureTheory Set

namespace RiemannResearch.Analysis

private theorem inverse_cube_le_square_difference {x : ℝ} (hx : 1 < x) :
    1 / x ^ 3 ≤ 1 / (x - 1) ^ 2 - 1 / x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have h : 1 / (x - 1) ^ 2 - 1 / x ^ 2 - 1 / x ^ 3 =
      (x ^ 2 + x - 1) / ((x - 1) ^ 2 * x ^ 3) := by
    field_simp [ne_of_gt hx0, ne_of_gt hx1]
    ring
  have hpos : 0 ≤ (x ^ 2 + x - 1) / ((x - 1) ^ 2 * x ^ 3) :=
    div_nonneg (by nlinarith only [sq_nonneg x, hx]) (by positivity)
  linarith only [h, hpos]

/-- A nonnegative density with mass at most `B` on successive unit intervals
gives an inverse-square upper bound for the absolute pairing with a test
of decay at most `C / x^3`. The bound is uniform in the truncation `m`. -/
theorem integral_abs_mul_le_of_unit_mass_inverse_cube
    {F W : ℝ → ℝ} (hF : Continuous F) (hW : Continuous W)
    {N B C : ℝ} (hN : 1 < N) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hFnonneg : ∀ x, N ≤ x → 0 ≤ F x)
    (hdecay : ∀ x, N ≤ x → |W x| ≤ C / x ^ 3)
    (hmass : ∀ k : ℕ, (∫ x in N + k..N + k + 1, F x) ≤ B) (m : ℕ) :
    (∫ x in N..N + m, |W x * F x|) ≤
      C * B * (1 / (N - 1) ^ 2 - 1 / (N + m - 1) ^ 2) := by
  have hwf : Continuous (fun x => |W x * F x|) := (hW.mul hF).abs
  have hstep (k : ℕ) :
      (∫ x in N + k..N + k + 1, |W x * F x|) ≤
        C * B * (1 / (N + k - 1) ^ 2 - 1 / (N + k) ^ 2) := by
    let y : ℝ := N + k
    have hNy : N ≤ y := le_add_of_nonneg_right (Nat.cast_nonneg k)
    have hy : 1 < y := hN.trans_le hNy
    have hy0 : 0 < y := by linarith only [hy]
    have hbound (x : ℝ) (hx : x ∈ Icc y (y + 1)) :
        |W x * F x| ≤ (C / y ^ 3) * F x := by
      have hNx := hNy.trans hx.1
      rw [abs_mul, abs_of_nonneg (hFnonneg x hNx)]
      apply mul_le_mul_of_nonneg_right _ (hFnonneg x hNx)
      exact (hdecay x hNx).trans (div_le_div_of_nonneg_left hC
        (pow_pos hy0 _) (pow_le_pow_left₀ hy0.le hx.1 3))
    calc
      _ ≤ ∫ x in y..y + 1, (C / y ^ 3) * F x :=
        intervalIntegral.integral_mono_on (by linarith : y ≤ y + 1)
          (hwf.intervalIntegrable _ _) ((continuous_const.mul hF).intervalIntegrable _ _) hbound
      _ = (C / y ^ 3) * (∫ x in y..y + 1, F x) := intervalIntegral.integral_const_mul _ _
      _ ≤ (C / y ^ 3) * B := mul_le_mul_of_nonneg_left (hmass k) (by positivity)
      _ = C * B * (1 / y ^ 3) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (inverse_cube_le_square_difference hy) (mul_nonneg hC hB)
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.cast_succ, ← add_assoc, ← intervalIntegral.integral_add_adjacent_intervals
      (hwf.intervalIntegrable N (N + m)) (hwf.intervalIntegrable (N + m) (N + m + 1))]
    calc
      _ ≤ _ := add_le_add ih (hstep m)
      _ = _ := by
        simp only [← add_assoc, add_sub_cancel_right]
        ring

end RiemannResearch.Analysis
