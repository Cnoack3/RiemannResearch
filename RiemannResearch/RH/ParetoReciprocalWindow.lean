/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.NearbyDilationGram
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite reciprocal windows and explicit infinite tails

Source: CRT tail-energy research, 13 October 2026.
An exact finite-window decomposition precedes the envelope estimate;
the cutoff need not be a common period.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto

/-- Exact finite-window/infinite-tail split. No signed term is discarded. -/
theorem paretoInner_eq_reciprocal_window_and_tail
    (R : ℕ → ℝ) (M T : ℕ) {A : ℝ}
    (hR : ∀ n, |R n| ≤ A)
    (hhead : ∀ n, 0 < n → n ≤ M → R n = 0) :
    paretoInner R R =
      (∑ n ∈ Finset.Icc (M + 1) T, positiveWeight n * R n ^ 2) +
      ∑' k : ℕ, positiveWeight (k + (T + 1)) * R (k + (T + 1)) ^ 2 := by
  have hs := weighted_summable_of_bounded (bounded_product hR hR)
  have hprefix :
      (∑ n ∈ Finset.range (T + 1), positiveWeight n * (R n * R n)) =
      ∑ n ∈ Finset.Icc (M + 1) T, positiveWeight n * (R n * R n) := by
    symm
    apply Finset.sum_subset
    · intro n hn
      simp only [Finset.mem_Icc, Finset.mem_range] at *
      omega
    · intro n hn hnot
      by_cases hn0 : n = 0
      · subst n
        simp [positiveWeight]
      · have hnT : n ≤ T := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hn
        have hnM : n ≤ M := by
          simp only [Finset.mem_Icc] at hnot
          omega
        rw [hhead n (Nat.pos_of_ne_zero hn0) hnM]
        simp
  have hsplit := hs.sum_add_tsum_nat_add (T + 1)
  rw [hprefix] at hsplit
  simpa only [paretoInner, pow_two] using hsplit.symm

/-- A finite reciprocal window plus an explicit envelope controls the
entire infinite error. The cutoff need not be a CRT period. -/
theorem paretoInner_le_reciprocal_window_add_tail
    (R : ℕ → ℝ) (M T : ℕ) {A : ℝ}
    (hR : ∀ n, |R n| ≤ A)
    (hhead : ∀ n, 0 < n → n ≤ M → R n = 0) :
    paretoInner R R ≤
      (∑ n ∈ Finset.Icc (M + 1) T, |R n| ^ 2 / (n : ℝ) ^ 2) +
        A ^ 2 / ((T + 1 : ℕ) : ℝ) := by
  have hs := weighted_summable_of_bounded (bounded_product hR hR)
  have hsTail := (summable_nat_add_iff (T + 1)).mpr hs
  have hw := (summable_nat_add_iff (T + 1)).mpr positiveWeight_summable
  have hsq (n : ℕ) : R n * R n ≤ A * A := by
    have hb := mul_self_le_mul_self (abs_nonneg (R n)) (hR n)
    nlinarith only [hb, sq_abs (R n)]
  have htail :
      (∑' k : ℕ, positiveWeight (k + (T + 1)) *
        R (k + (T + 1)) ^ 2) ≤ A ^ 2 / ((T + 1 : ℕ) : ℝ) := by
    calc
      _ = ∑' k : ℕ, positiveWeight (k + (T + 1)) *
          (R (k + (T + 1)) * R (k + (T + 1))) := by simp only [pow_two]
      _ ≤ ∑' k : ℕ, positiveWeight (k + (T + 1)) * (A * A) := by
        exact hsTail.tsum_le_tsum
          (fun k => mul_le_mul_of_nonneg_left (hsq _) (positiveWeight_nonneg _))
          (hw.mul_right _)
      _ = _ := by
        rw [hw.tsum_mul_right, positiveWeight_tail_tsum (T + 1) (by omega)]
        ring
  have hprefix_le :
      (∑ n ∈ Finset.Icc (M + 1) T, positiveWeight n * R n ^ 2) ≤
      ∑ n ∈ Finset.Icc (M + 1) T, |R n| ^ 2 / (n : ℝ) ^ 2 := by
    apply Finset.sum_le_sum
    intro n hn
    have hn0 : (0 : ℝ) < n := by
      have hn' := (Finset.mem_Icc.mp hn).1
      exact_mod_cast (show 0 < n by omega)
    have hwle : positiveWeight n ≤ 1 / (n : ℝ) ^ 2 := by
      unfold positiveWeight
      apply one_div_le_one_div_of_le (sq_pos_of_pos hn0)
      nlinarith
    calc
      _ ≤ (1 / (n : ℝ) ^ 2) * R n ^ 2 :=
        mul_le_mul_of_nonneg_right hwle (sq_nonneg _)
      _ = _ := by rw [sq_abs]; ring
  rw [paretoInner_eq_reciprocal_window_and_tail R M T hR hhead]
  exact add_le_add hprefix_le htail

end RiemannResearch.RH.Pareto
