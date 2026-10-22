/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Positive arithmetic prefixes and finite Abel summation

The finite Abel identity below is the standard summation-by-parts identity,
proved by induction. It retains the exact terminal term and every signed
increment; it does not assert any analytic estimate.
-/

open scoped BigOperators

namespace RiemannResearch.Analysis

/-- Partial sum over the positive integers up to and including `N`. -/
def positiveArithmeticPrefix (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, a (n + 1)

@[simp] theorem positiveArithmeticPrefix_zero (a : ℕ → ℝ) :
    positiveArithmeticPrefix a 0 = 0 := by
  simp [positiveArithmeticPrefix]

theorem positiveArithmeticPrefix_succ (a : ℕ → ℝ) (N : ℕ) :
    positiveArithmeticPrefix a (N + 1) =
      positiveArithmeticPrefix a N + a (N + 1) := by
  exact Finset.sum_range_succ _ _

/-- Finite Abel summation with both the terminal term and every signed
increment retained. There is no convergence assumption. -/
theorem positiveArithmeticPrefix_weighted_abel (a g : ℕ → ℝ) (N : ℕ) :
    positiveArithmeticPrefix (fun n => a n * g n) N =
      positiveArithmeticPrefix a N * g (N + 1) +
        ∑ n ∈ Finset.range N,
          positiveArithmeticPrefix a (n + 1) * (g (n + 1) - g (n + 2)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [positiveArithmeticPrefix_succ, ih, Finset.sum_range_succ,
        positiveArithmeticPrefix_succ]
      ring

/-- The signed Abel increments have exact total mass equal to the first
weight, including the terminal mass. -/
theorem positiveArithmeticPrefix_abel_mass (g : ℕ → ℝ) (N : ℕ) :
    g (N + 1) + (∑ n ∈ Finset.range N, (g (n + 1) - g (n + 2))) = g 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      linarith

/-- Decreasing nonnegative weights cannot enlarge a uniform bound for the
ordinary prefixes by more than their first value. -/
theorem positiveArithmeticPrefix_weighted_bound (a g : ℕ → ℝ) (N : ℕ) (B : ℝ)
    (hA : ∀ n : ℕ, n ≤ N → |positiveArithmeticPrefix a n| ≤ B)
    (hg : 0 ≤ g (N + 1))
    (hgmono : ∀ n : ℕ, n < N → g (n + 2) ≤ g (n + 1)) :
    |positiveArithmeticPrefix (fun n => a n * g n) N| ≤ B * g 1 := by
  rw [positiveArithmeticPrefix_weighted_abel]
  have hend : |positiveArithmeticPrefix a N * g (N + 1)| ≤ B * g (N + 1) := by
    rw [abs_mul, abs_of_nonneg hg]
    exact mul_le_mul_of_nonneg_right (hA N le_rfl) hg
  have hsum :
      |∑ n ∈ Finset.range N,
        positiveArithmeticPrefix a (n + 1) * (g (n + 1) - g (n + 2))| ≤
      ∑ n ∈ Finset.range N, B * (g (n + 1) - g (n + 2)) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro n hn
    have hnN : n < N := Finset.mem_range.mp hn
    have hd : 0 ≤ g (n + 1) - g (n + 2) := sub_nonneg.mpr (hgmono n hnN)
    rw [abs_mul, abs_of_nonneg hd]
    exact mul_le_mul_of_nonneg_right (hA (n + 1) (by omega)) hd
  calc
    _ ≤ |positiveArithmeticPrefix a N * g (N + 1)| +
        |∑ n ∈ Finset.range N,
          positiveArithmeticPrefix a (n + 1) * (g (n + 1) - g (n + 2))| := abs_add_le _ _
    _ ≤ B * g (N + 1) +
        ∑ n ∈ Finset.range N, B * (g (n + 1) - g (n + 2)) := add_le_add hend hsum
    _ = B * g 1 := by
      rw [← Finset.mul_sum, ← mul_add, positiveArithmeticPrefix_abel_mass]

end RiemannResearch.Analysis
