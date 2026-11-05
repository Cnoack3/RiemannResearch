/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # Cofinal pairs of consecutive primes with a logarithmic gap

A lower bound on every consecutive prime gap would telescope to an upper bound
on Chebyshev's theta. Its elementary lower bound excludes this possibility.
-/

noncomputable section
open Filter Asymptotics
open scoped BigOperators Topology

namespace RiemannResearch.NumberTheory

local notation "nthPrime" => Nat.nth Nat.Prime

private theorem eventually_quarter_le_theta :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) / 4 ≤ Chebyshev.theta n := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).bound
    (by norm_num : (0 : ℝ) < 1 / 16)
  have hNat : ∀ᶠ n : ℕ in atTop, ‖Real.log (n : ℝ)‖ ≤
      (1 / 16 : ℝ) * ‖(n : ℝ) ^ (1 / 2 : ℝ)‖ :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually h
  filter_upwards [hNat, eventually_ge_atTop (2 : ℕ)] with n hlog hn
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hnpos : (0 : ℝ) < n := by linarith
  have hl0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hs1 : 1 ≤ Real.sqrt (n : ℝ) := by
    have hMon := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ n by linarith)
    simpa only [Real.sqrt_one] using hMon
  rw [← Real.sqrt_eq_rpow] at hlog
  simp only [Real.norm_eq_abs, abs_of_nonneg hl0, abs_of_nonneg (Real.sqrt_nonneg _)] at hlog
  have hlnext : Real.log ((n : ℝ) + 1) ≤ 2 * Real.log n := calc
    _ ≤ Real.log (2 * (n : ℝ)) :=
      Real.log_le_log (by positivity) (by linarith)
    _ = Real.log 2 + Real.log n := Real.log_mul (by norm_num) (ne_of_gt hnpos)
    _ ≤ _ := by linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hn2]
  have hlin := mul_le_mul_of_nonneg_right hs1 hl0
  have hprod := mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg (n : ℝ))
  have h2 := mul_le_mul_of_nonneg_left
    (show (1 / 2 : ℝ) ≤ Real.log 2 by linarith [Real.log_two_gt_d9]) hn0
  have htheta : (n : ℝ) * Real.log 2 - Real.log ((n : ℝ) + 1) -
      2 * Real.sqrt n * Real.log n ≤ Chebyshev.theta n := by
    simpa only [Nat.cast_add, Nat.cast_one] using Chebyshev.theta_ge n
  nlinarith [Real.sq_sqrt hn0]

private theorem theta_nthPrime_succ (j : ℕ) :
    Chebyshev.theta (nthPrime (j + 1)) =
      Chebyshev.theta (nthPrime j) + Real.log (nthPrime (j + 1)) := by
  have hlt : nthPrime j < nthPrime (j + 1) :=
    Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self j)
  have hset : Nat.primesLE (nthPrime (j + 1)) =
      insert (nthPrime (j + 1)) (Nat.primesLE (nthPrime j)) := by
    ext p
    simp only [Nat.mem_primesLE, Finset.mem_insert]
    constructor
    · rintro ⟨h, hp⟩
      rcases lt_or_eq_of_le h with h | h
      · exact Or.inr ⟨Nat.le_nth_of_lt_nth_succ h hp, hp⟩
      · exact Or.inl h
    · rintro (rfl | ⟨h, hp⟩)
      · exact ⟨le_rfl, Nat.prime_nth_prime _⟩
      · exact ⟨h.trans hlt.le, hp⟩
  have hnot : nthPrime (j + 1) ∉ Nat.primesLE (nthPrime j) :=
    fun h => hlt.not_ge (Nat.le_of_mem_primesLE h)
  rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log,
    hset, Finset.sum_insert hnot, add_comm]

/-- For each lower bound there is a consecutive prime gap beyond it of size
at most eight times the natural logarithm of the upper prime. -/
theorem exists_consecutive_prime_gap_le_eight_log (B : ℕ) :
    ∃ k : ℕ, B ≤ k ∧
      (nthPrime (k + 1) : ℝ) - (nthPrime k : ℝ) ≤ 8 * Real.log (nthPrime (k + 1)) := by
  by_contra! hall
  have hcum (j : ℕ) : 8 * (Chebyshev.theta (nthPrime (B + j)) - Chebyshev.theta (nthPrime B)) ≤
      (nthPrime (B + j) : ℝ) - (nthPrime B : ℝ) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [show B + (j + 1) = (B + j) + 1 by omega, theta_nthPrime_succ]
      have hs := hall (B + j) (by omega)
      linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 eventually_quarter_le_theta
  obtain ⟨K, hK⟩ := exists_nat_ge (8 * Chebyshev.theta (nthPrime B))
  let j := N + K + 1
  have hindex : B + j + 2 ≤ nthPrime (B + j) := Nat.add_two_le_nth_prime _
  have hN' : N ≤ nthPrime (B + j) := by dsimp [j] at *; omega
  have hK' : K < nthPrime (B + j) := by dsimp [j] at *; omega
  have hK'' : (K : ℝ) < nthPrime (B + j) := by exact_mod_cast hK'
  have hq := hN _ hN'
  have hg := hcum j
  linarith [Nat.cast_nonneg (α := ℝ) (nthPrime B)]

/-- The same pair with the physical conductors and the nonnegative natural
gap exposed for use in estimates. -/
theorem exists_primes_gap_le_eight_log (B : ℕ) :
    ∃ q p : ℕ, B ≤ q ∧ q.Prime ∧ p.Prime ∧ q < p ∧
      ((p - q : ℕ) : ℝ) ≤ 8 * Real.log (p : ℝ) := by
  obtain ⟨k, hk, hgap⟩ := exists_consecutive_prime_gap_le_eight_log B
  have hlt : nthPrime k < nthPrime (k + 1) :=
    Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self k)
  have hkq : k ≤ nthPrime k := (by omega : k ≤ k + 2).trans (Nat.add_two_le_nth_prime k)
  refine ⟨nthPrime k, nthPrime (k + 1), hk.trans hkq,
    Nat.prime_nth_prime _, Nat.prime_nth_prime _, hlt, ?_⟩
  rwa [Nat.cast_sub hlt.le]

/-- A quarter-power bound follows with constant one, cofinally in the lower
prime. This form absorbs the sixteenth power of the gap in a Schur-row bound. -/
theorem exists_primes_gap_le_quarter_power (B : ℕ) :
    ∃ q p : ℕ, B ≤ q ∧ q.Prime ∧ p.Prime ∧ q < p ∧
      ((p - q : ℕ) : ℝ) ≤ (p : ℝ) ^ (1 / 4 : ℝ) := by
  have hsmall := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).bound
    (by norm_num : (0 : ℝ) < 1 / 8)
  obtain ⟨X, hX⟩ := eventually_atTop.1 hsmall
  obtain ⟨K, hK⟩ := exists_nat_ge X
  obtain ⟨q, p, hq, hqprime, hpprime, hqp, hgap⟩ :=
    exists_primes_gap_le_eight_log (max B K)
  refine ⟨q, p, (le_max_left _ _).trans hq, hqprime, hpprime, hqp, ?_⟩
  have hKp : K ≤ p := ((le_max_right B K).trans hq).trans hqp.le
  have h := hX (p : ℝ) (hK.trans (by exact_mod_cast hKp))
  change ‖Real.log (p : ℝ)‖ ≤ (1 / 8 : ℝ) * ‖(p : ℝ) ^ (1 / 4 : ℝ)‖ at h
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpprime.one_le
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hp1),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) (1 / 4 : ℝ))] at h
  linarith

end RiemannResearch.NumberTheory
