/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoAmplitudeCertificates
import Lean.Elab.Tactic.Omega
import RiemannResearch.RH.ParetoWeights
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A nonarithmetic exact-head countermodel in the actual Pareto measure

Source: the user-provided five-attempt capacity note, Attempt 3.
These are actual complete weighted sums with P(n)=1/(n(n+1)). The functions
are deliberately not asserted to belong to the legal arithmetic span.
Matching every finite head alone does not control energy or correlations.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExactHeadCountermodel
open RiemannResearch.RH.Pareto
open RiemannResearch.RH.Pareto.AmplitudeCertificates

def residual (N n : ℕ) : ℝ := if n ≤ N then 0 else (N : ℝ) + 1
def trial (N n : ℕ) : ℝ := 1 - residual N n

theorem trial_exact_head (N n : ℕ) (hn : n ≤ N) : trial N n = 1 := by
  simp [trial, residual, hn]

private theorem weighted_tail_summable (N : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    Summable (fun n => paretoWeight n * (if n + 1 ≤ N then 0 else c)) := by
  apply Summable.of_nonneg_of_le _ _ (paretoWeight_hasSum.summable.mul_right c)
  · intro n
    exact mul_nonneg (paretoWeight_pos n).le (by split_ifs <;> positivity)
  · intro n
    exact mul_le_mul_of_nonneg_left (by split_ifs <;> linarith) (paretoWeight_pos n).le

private theorem weighted_tail_sum (N : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    (∑' n, paretoWeight n * (if n + 1 ≤ N then 0 else c)) =
      c / ((N : ℝ) + 1) := by
  have hs := weighted_tail_summable N c hc
  have he := hs.sum_add_tsum_nat_add N
  have hh : (∑ n ∈ Finset.range N,
      paretoWeight n * (if n + 1 ≤ N then 0 else c)) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hn' : n + 1 ≤ N := by have := Finset.mem_range.mp hn; omega
    simp [hn']
  rw [hh, zero_add] at he
  have hm : (∑' n, paretoWeight (n + N)) = 1 / ((N : ℝ) + 1) := by
    have h := paretoWeight_hasSum.summable.sum_add_tsum_nat_add N
    rw [paretoWeight_tsum, paretoWeight_partial_sum] at h
    linarith
  rw [← he]
  calc
    _ = ∑' n, paretoWeight (n + N) * c := by
      apply tsum_congr
      intro n
      rw [if_neg (by omega)]
    _ = c / ((N : ℝ) + 1) := by rw [tsum_mul_right, hm]; ring

theorem residual_mean (N : ℕ) :
    (∑' n, paretoWeight n * residual N (n + 1)) = 1 := by
  unfold residual
  rw [weighted_tail_sum N ((N : ℝ) + 1) (by positivity)]
  exact div_self (by positivity)

theorem trial_mean_zero (N : ℕ) :
    (∑' n, paretoWeight n * trial N (n + 1)) = 0 := by
  have hs : Summable (fun n => paretoWeight n * residual N (n + 1)) :=
    weighted_tail_summable N ((N : ℝ) + 1) (by positivity)
  simp only [trial, mul_sub, mul_one]
  rw [paretoWeight_hasSum.summable.tsum_sub hs, paretoWeight_tsum, residual_mean]
  ring

theorem residual_covariance_of_le (N M : ℕ) (hNM : N ≤ M) :
    (∑' n, paretoWeight n * (residual N (n + 1) * residual M (n + 1))) =
      (N : ℝ) + 1 := by
  calc
    _ = ∑' n, paretoWeight n *
        (if n + 1 ≤ M then 0 else ((N : ℝ) + 1) * ((M : ℝ) + 1)) := by
      apply tsum_congr
      intro n
      by_cases hn : n + 1 ≤ M
      · simp [residual, hn]
      · have hnN : ¬ n + 1 ≤ N := by omega
        simp [residual, hn, hnN]
    _ = (((N : ℝ) + 1) * ((M : ℝ) + 1)) / ((M : ℝ) + 1) :=
      weighted_tail_sum M _ (by positivity)
    _ = (N : ℝ) + 1 := by field_simp [show (M : ℝ) + 1 ≠ 0 by positivity]

theorem residual_covariance (N M : ℕ) :
    (∑' n, paretoWeight n * (residual N (n + 1) * residual M (n + 1))) =
      ((min N M : ℕ) : ℝ) + 1 := by
  rcases le_total N M with h | h
  · rw [min_eq_left h]
    exact residual_covariance_of_le N M h
  · rw [min_eq_right h]
    calc
      _ = ∑' n, paretoWeight n *
          (residual M (n + 1) * residual N (n + 1)) := by
        apply tsum_congr
        intro n
        rw [mul_comm (residual N (n + 1)) (residual M (n + 1))]
      _ = _ := residual_covariance_of_le M N h

theorem residual_energy (N : ℕ) : energy (residual N) = (N : ℝ) + 1 := by
  simpa only [energy, pow_two] using residual_covariance_of_le N N le_rfl

theorem trial_error_energy (N : ℕ) :
    energy (fun n => trial N n - 1) = (N : ℝ) + 1 := by
  have h : energy (fun n => trial N n - 1) = energy (residual N) := by
    unfold energy
    apply tsum_congr
    intro n
    simp only [trial]
    ring
  rw [h, residual_energy]

end RiemannResearch.RH.Pareto.ExactHeadCountermodel
