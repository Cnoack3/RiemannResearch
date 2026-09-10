import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite logarithmic block estimates

Source: user-provided argument, §3 of
`Dyadic_Gram_Prefix_Ordinary_Proof_20260910.md`, reproduced in the supplied
`DyadicRegularizedVerificationContinuation20260910 (2).md`.
This supplies the elementary finite logarithmic sum used in packing blocks of
the irrational rotation in the actual dyadic Gram prefix estimate. The proof
uses only `log x ≤ x - 1`, without Stirling's formula or an asymptotic input.
-/

open scoped BigOperators

namespace Real

/-- The elementary lower factorial-log estimate, in its exact finite-sum form. -/
theorem nat_mul_log_sub_sum_log_succ_le (q : ℕ) :
    (q : ℝ) * log q - (∑ i ∈ Finset.range q, log ((i : ℝ) + 1)) ≤ q := by
  induction q with
  | zero => simp
  | succ q ih =>
      by_cases hq : q = 0
      · subst q
        norm_num
      have hq0 : 0 < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq
      have hstep := log_le_sub_one_of_pos
        (div_pos (show 0 < (q : ℝ) + 1 by positivity) hq0)
      rw [log_div (by positivity) (ne_of_gt hq0)] at hstep
      have hmul := mul_le_mul_of_nonneg_left hstep (le_of_lt hq0)
      have hcancel : (q : ℝ) * (((q : ℝ) + 1) / q - 1) = 1 := by
        field_simp [ne_of_gt hq0] <;> ring
      rw [hcancel] at hmul
      rw [Finset.sum_range_succ]
      simp only [Nat.cast_add, Nat.cast_one]
      nlinarith

/-- The logarithmic block estimate with arbitrary positive scale. -/
theorem sum_log_scaled_nat_div_succ_le (K : ℝ) (hK : 0 < K) (q : ℕ) :
    (∑ i ∈ Finset.range q, log (K * q / ((i : ℝ) + 1))) ≤
      (1 + log K) * q := by
  by_cases hq : q = 0
  · simp [hq]
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq
  have hlog (i : ℕ) : log (K * q / ((i : ℝ) + 1)) =
      log K + log q - log ((i : ℝ) + 1) := by
    rw [log_div (ne_of_gt (mul_pos hK hq0)) (by positivity),
      log_mul (ne_of_gt hK) (ne_of_gt hq0)]
  have he : (∑ i ∈ Finset.range q, log (K * q / ((i : ℝ) + 1))) =
      (q : ℝ) * log K + (q : ℝ) * log q -
        (∑ i ∈ Finset.range q, log ((i : ℝ) + 1)) := by
    simp_rw [hlog]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp
  rw [he]
  have h := nat_mul_log_sub_sum_log_succ_le q
  nlinarith

/-- The exact scale needed by the centered-circle block packing argument. -/
theorem sum_log_four_nat_div_succ_le (q : ℕ) :
    (∑ i ∈ Finset.range q, log (4 * q / ((i : ℝ) + 1))) ≤
      (1 + log 4) * q := by
  exact sum_log_scaled_nat_div_succ_le 4 (by norm_num) q

/-- One exceptional point plus a ranked spacing lower bound controls the whole
block. The rank assumptions are explicit; circular packing supplies them in the
rotation application. -/
theorem sum_log_inv_le_of_rank_lower
    (q s : ℕ) (hq : 0 < q) (hs : s ≤ q) (C : ℝ) (hC : 0 ≤ C)
    (d : ℕ → ℝ)
    (hd : ∀ i < s, 0 < d i)
    (hfirst : log (1 / d 0) ≤ C * q)
    (hrank : ∀ i, i + 1 < s →
      ((i : ℝ) + 1) / (4 * q) ≤ d (i + 1)) :
    (∑ i ∈ Finset.range s, log (1 / d i)) ≤
      (C + 1 + log 4) * q := by
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq
  have h4 : 0 ≤ log (4 : ℝ) := log_nonneg (by norm_num)
  cases s with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      positivity
  | succ s =>
      have hsle : s ≤ q := le_trans (Nat.le_succ s) hs
      have hcompare :
          (∑ i ∈ Finset.range s, log (1 / d (i + 1))) ≤
          ∑ i ∈ Finset.range s, log (4 * q / ((i : ℝ) + 1)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hiS : i + 1 < s + 1 := Nat.succ_lt_succ (Finset.mem_range.mp hi)
        have hd0 := hd (i + 1) hiS
        have hi0 : 0 < (i : ℝ) + 1 := by positivity
        have hr := (div_le_iff₀ (show 0 < (4 : ℝ) * q by positivity)).mp
          (hrank i hiS)
        apply log_le_log (one_div_pos.mpr hd0)
        apply (div_le_div_iff₀ hd0 hi0).mpr
        nlinarith
      have hpad :
          (∑ i ∈ Finset.range s, log (4 * q / ((i : ℝ) + 1))) ≤
          ∑ i ∈ Finset.range q, log (4 * q / ((i : ℝ) + 1)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hsle)
        intro i hi _
        have hiq : (i : ℝ) + 1 ≤ q := by
          exact_mod_cast Nat.succ_le_iff.mpr (Finset.mem_range.mp hi)
        apply log_nonneg
        apply (le_div_iff₀ (show 0 < (i : ℝ) + 1 by positivity)).mpr
        nlinarith
      have hsum := sum_log_four_nat_div_succ_le q
      rw [Finset.sum_range_succ']
      nlinarith

end Real

namespace Nat

/-- The last possibly short block costs at most one additional block length.
For positive `N`, `(N - 1) / q + 1` is the number of consecutive blocks of
length at most `q`. -/
theorem mul_ceilBlockCount_le_two_mul (N q : ℕ) (hqN : q ≤ N) :
    q * ((N - 1) / q + 1) ≤ 2 * N := by
  have hdiv : q * ((N - 1) / q) ≤ N - 1 := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (N - 1) q
  have hsub : N - 1 ≤ N := Nat.sub_le N 1
  nlinarith

end Nat
