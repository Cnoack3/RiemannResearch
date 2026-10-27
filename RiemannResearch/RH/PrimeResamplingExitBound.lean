/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.InverseSquareAbelTail
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# A summable exit envelope for prime resampling

A positive integer has at most n prime divisors. The sum of p⁻² over
all primes is at most the inverse-square tail beginning at two, hence
at most one. No prime number theorem is needed.
-/

noncomputable section
open scoped BigOperators ENNReal
namespace RiemannResearch.RH.PrimeResampling
open RiemannResearch.Analysis.InverseSquareAbelTail

/-- The indicator of the actual prime divisors has finite total mass. -/
theorem prime_divisor_indicator_tsum_le (n : ℕ) (hn : n ≠ 0) :
    (∑' p : ℕ, if p.Prime ∧ p ∣ n then (1 : ℝ≥0∞) else 0) ≤
      ENNReal.ofReal (n : ℝ) := by
  classical
  have hs : (∑' p : ℕ, if p.Prime ∧ p ∣ n then (1 : ℝ≥0∞) else 0) =
      ∑ p ∈ Finset.Icc 1 n, if p.Prime ∧ p ∣ n then (1 : ℝ≥0∞) else 0 := by
    apply tsum_eq_sum
    intro p hp
    by_cases h : p.Prime ∧ p ∣ n
    · have hmem : p ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr
        ⟨h.1.pos, Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h.2⟩
      exact False.elim (hp hmem)
    · simp only [if_neg h]
  rw [hs]
  calc
    _ ≤ ∑ _p ∈ Finset.Icc 1 n, (1 : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro p hp
      split_ifs <;> simp
    _ = ENNReal.ofReal (n : ℝ) := by simp

private def primeInverseSquare (p : ℕ) : ℝ :=
  if p.Prime then 1 / (p : ℝ) ^ 2 else 0

private theorem primeInverseSquare_nonneg (p : ℕ) :
    0 ≤ primeInverseSquare p := by
  unfold primeInverseSquare
  split_ifs <;> positivity

private theorem primeInverseSquare_summable : Summable primeInverseSquare := by
  apply Summable.of_nonneg_of_le primeInverseSquare_nonneg _
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
  intro p
  unfold primeInverseSquare
  split_ifs
  · exact le_rfl
  · positivity

private theorem primeInverseSquare_tsum_le_one :
    (∑' p : ℕ, primeInverseSquare p) ≤ 1 := by
  have hs := primeInverseSquare_summable
  have hshift : (∑' p : ℕ, primeInverseSquare p) =
      ∑' p : ℕ, primeInverseSquare (p + 2) := by
    have he := hs.sum_add_tsum_nat_add 2
    norm_num [primeInverseSquare, Finset.sum_range_succ, Nat.not_prime_one] at he
    simpa only [primeInverseSquare, Nat.cast_add, Nat.cast_ofNat, one_div] using he.symm
  rw [hshift]
  calc
    _ ≤ ∑' k : ℕ, weight 1 k := by
      apply ((summable_nat_add_iff 2).mpr hs).tsum_le_tsum _ (weight_summable 1)
      intro k
      unfold primeInverseSquare weight
      split_ifs
      · simp [Nat.add_assoc]
      · positivity
    _ ≤ 1 := by simpa using weight_mass_upper 1 (by norm_num)

/-- The full prime inverse-square sum has no tail omission. -/
theorem prime_inverse_square_tsum_le_one :
    (∑' p : ℕ, if p.Prime then ENNReal.ofReal (1 / (p : ℝ) ^ 2) else 0) ≤ 1 := by
  have he : (∑' p : ℕ, if p.Prime then ENNReal.ofReal (1 / (p : ℝ) ^ 2) else 0) =
      ENNReal.ofReal (∑' p : ℕ, primeInverseSquare p) := by
    rw [ENNReal.ofReal_tsum_of_nonneg primeInverseSquare_nonneg primeInverseSquare_summable]
    apply tsum_congr
    intro p
    unfold primeInverseSquare
    split_ifs <;> simp
  rw [he]
  simpa using ENNReal.ofReal_le_ofReal primeInverseSquare_tsum_le_one

/-- The actual prime-resampling exit majorant has at most linear total rate. -/
theorem prime_exit_majorant_tsum_le (n : ℕ) (hn : n ≠ 0) :
    (∑' p : ℕ, if p.Prime then
      ENNReal.ofReal ((if p ∣ n then (1 : ℝ) else 0) + 1 / (p : ℝ) ^ 2)
      else 0) ≤ ENNReal.ofReal ((n : ℝ) + 1) := by
  have he : (∑' p : ℕ, if p.Prime then
      ENNReal.ofReal ((if p ∣ n then (1 : ℝ) else 0) + 1 / (p : ℝ) ^ 2)
      else 0) =
      (∑' p : ℕ, if p.Prime ∧ p ∣ n then (1 : ℝ≥0∞) else 0) +
      ∑' p : ℕ, if p.Prime then ENNReal.ofReal (1 / (p : ℝ) ^ 2) else 0 := by
    rw [← ENNReal.tsum_add]
    apply tsum_congr
    intro p
    by_cases hp : p.Prime
    · by_cases hd : p ∣ n
      · simp only [hp, hd, and_self, if_true]
        rw [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) (by positivity)]
        simp
      · simp [hp, hd]
    · simp [hp]
  rw [he]
  calc
    _ ≤ ENNReal.ofReal (n : ℝ) + 1 := add_le_add
      (prime_divisor_indicator_tsum_le n hn) prime_inverse_square_tsum_le_one
    _ = _ := by rw [ENNReal.ofReal_add (Nat.cast_nonneg n) zero_le_one]; simp

end RiemannResearch.RH.PrimeResampling
