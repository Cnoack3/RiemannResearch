/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Summable weights from bounds for positive prefixes

If a nonnegative prefix has growth at most C w(n)^(-B), where w decreases
inside [0,1], one additional power of the weight gives a summable series.
The proof retains the finite boundary term in summation by parts.
Source: standard summation by parts for a positive sequence and a decreasing weight.
-/

open scoped BigOperators
namespace RiemannResearch.Analysis

private theorem pow_difference_bound (x y : ℝ) (hy : 0 ≤ y) (hyx : y ≤ x) (B : ℕ) :
    x ^ (B + 1) - y ^ (B + 1) ≤ ((B + 1 : ℕ) : ℝ) * x ^ B * (x - y) := by
  have hx : 0 ≤ x := hy.trans hyx
  induction B with
  | zero => simp
  | succ B ih =>
    have hfirst := mul_le_mul_of_nonneg_left ih hx
    have hsecond := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hy hyx (B+1)) (sub_nonneg.mpr hyx)
    calc
      x ^ (B + 1 + 1) - y ^ (B + 1 + 1) =
          x * (x ^ (B+1) - y ^ (B+1)) + y ^ (B+1) * (x-y) := by
        rw [pow_succ x (B+1), pow_succ y (B+1)]
        ring
      _ ≤ x * (((B+1 : ℕ) : ℝ) * x ^ B * (x-y)) + x ^ (B+1) * (x-y) :=
        add_le_add hfirst hsecond
      _ = _ := by simp only [pow_succ, Nat.cast_add, Nat.cast_one]; ring

/-- A decreasing weight needs one extra power beyond the prefix-growth
exponent. The summability conclusion includes the first index. -/
theorem summable_weighted_of_prefix_bound (a w : ℕ → ℝ) (B : ℕ) (C : ℝ)
    (ha : ∀ n, 0 ≤ a n) (hw : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1)
    (hanti : Antitone w) (hC : 0 ≤ C)
    (hbound : ∀ n, (∑ k ∈ Finset.range (n+1), a k) * w n ^ B ≤ C) :
    Summable (fun n => a n * w n ^ (B+1)) := by
  let A (n : ℕ) := ∑ k ∈ Finset.range (n+1), a k
  let T (n : ℕ) := ∑ k ∈ Finset.range (n+1), a k * w k ^ (B+1)
  have hA (n : ℕ) : 0 ≤ A n := Finset.sum_nonneg fun k _ => ha k
  have hAsucc (n : ℕ) : A (n+1) = A n + a (n+1) := Finset.sum_range_succ _ _
  have hTsucc (n : ℕ) : T (n+1) = T n + a (n+1) * w (n+1) ^ (B+1) :=
    Finset.sum_range_succ _ _
  have hfinite (n : ℕ) : T n ≤ A n * w n ^ (B+1) +
      C * ((B+1 : ℕ) : ℝ) * (w 0 - w n) := by
    induction n with
    | zero => simp [A, T]
    | succ n ih =>
      have hdiff : A n * (w n ^ (B+1) - w (n+1) ^ (B+1)) ≤
          C * ((B+1 : ℕ) : ℝ) * (w n - w (n+1)) := by
        have hm : w (n+1) ≤ w n := hanti (Nat.le_succ n)
        calc
          _ ≤ A n * (((B+1 : ℕ) : ℝ) * w n ^ B * (w n - w (n+1))) :=
            mul_le_mul_of_nonneg_left (pow_difference_bound _ _ (hw _) hm B) (hA n)
          _ = (A n * w n ^ B) * (((B+1 : ℕ) : ℝ) * (w n - w (n+1))) := by ring
          _ ≤ C * (((B+1 : ℕ) : ℝ) * (w n - w (n+1))) :=
            mul_le_mul_of_nonneg_right (hbound n)
              (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hm))
          _ = _ := by ring
      calc
        T (n+1) = T n + a (n+1) * w (n+1) ^ (B+1) := hTsucc n
        _ ≤ (A n * w n ^ (B+1) + C * ((B+1 : ℕ) : ℝ) * (w 0-w n)) +
            a (n+1) * w (n+1) ^ (B+1) := add_le_add ih le_rfl
        _ = (A (n+1) * w (n+1) ^ (B+1) + C * ((B+1 : ℕ) : ℝ) * (w 0-w n)) +
            A n * (w n ^ (B+1) - w (n+1) ^ (B+1)) := by rw [hAsucc]; ring
        _ ≤ (A (n+1) * w (n+1) ^ (B+1) + C * ((B+1 : ℕ) : ℝ) * (w 0-w n)) +
            C * ((B+1 : ℕ) : ℝ) * (w n-w (n+1)) := add_le_add le_rfl hdiff
        _ = _ := by ring
  have htotal (n : ℕ) : T n ≤ C * ((B+1 : ℕ) : ℝ) := by
    have hhead : A n * w n ^ (B+1) ≤ C * w n := by
      simpa only [pow_succ, mul_assoc] using mul_le_mul_of_nonneg_right (hbound n) (hw n)
    have htail : 0 ≤ C * (B : ℝ) * w n := mul_nonneg (mul_nonneg hC (Nat.cast_nonneg B)) (hw n)
    have hstart := mul_le_mul_of_nonneg_left (hw1 0)
      (mul_nonneg hC (Nat.cast_nonneg (B+1)))
    have hstep := (hfinite n).trans (add_le_add hhead le_rfl)
    simp only [Nat.cast_add, Nat.cast_one] at hstep hstart ⊢
    nlinarith
  apply summable_of_sum_range_le (fun n => mul_nonneg (ha n) (pow_nonneg (hw n) _))
  intro N
  cases N with
  | zero => simpa using mul_nonneg hC (Nat.cast_nonneg (B+1))
  | succ n => simpa only [T, Nat.cast_add, Nat.cast_one] using htotal n

end RiemannResearch.Analysis
