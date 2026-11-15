/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! # Finite reciprocal square-root sums
Source: user-provided `Reciprocal_Head_Investigation_2026-11-07.md`, Section 2.
The elementary telescoping estimate includes its initial endpoint exactly.
-/

open scoped BigOperators
namespace RiemannResearch.Analysis

theorem reciprocal_sqrt_succ_le (n : ℕ) :
    1 / Real.sqrt ((n + 1 : ℕ) : ℝ) ≤
      2 * (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ)) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hn1 : (0 : ℝ) < (n + 1 : ℕ) := Nat.cast_pos.mpr (Nat.succ_pos n)
  have hsq0 := Real.sq_sqrt hn
  have hsq1 := Real.sq_sqrt hn1.le
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hn1)).mpr
  have hnonneg := sq_nonneg
    (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ))
  simp only [Nat.cast_add, Nat.cast_one] at hsq1 hnonneg ⊢
  nlinarith

theorem sum_inverse_sqrt_range_le (N : ℕ) :
    (∑ k ∈ Finset.range N, 1 / Real.sqrt ((k + 1 : ℕ) : ℝ)) ≤
      2 * Real.sqrt (N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have h := reciprocal_sqrt_succ_le N
      linarith

theorem sum_inverse_sqrt_Icc_le (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, 1 / Real.sqrt (k : ℝ)) ≤
      2 * Real.sqrt (N : ℝ) := by
  have he : (∑ k ∈ Finset.range N, 1 / Real.sqrt ((k + 1 : ℕ) : ℝ)) =
      ∑ k ∈ Finset.Icc 1 N, 1 / Real.sqrt (k : ℝ) := by
    apply Finset.sum_bij (fun k _ => k + 1)
    · intro k hk
      exact Finset.mem_Icc.mpr ⟨Nat.succ_pos k, by
        have h := Finset.mem_range.mp hk
        omega⟩
    · intro k hk j hj hkj
      omega
    · intro j hj
      obtain ⟨hj1, hjN⟩ := Finset.mem_Icc.mp hj
      exact ⟨j - 1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro k hk
      rfl
  rw [← he]
  exact sum_inverse_sqrt_range_le N

end RiemannResearch.Analysis
