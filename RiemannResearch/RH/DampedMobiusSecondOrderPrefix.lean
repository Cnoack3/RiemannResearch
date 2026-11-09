/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.DampedMobiusSecondOrder
import RiemannResearch.RH.DampedMobiusReciprocalEnvelope
import RiemannResearch.RH.DampedMobiusDensityBounds
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Chebyshev first derivative of the reciprocal damped Mobius family

Source: continuation of the user-provided reciprocal-density report,
8 November 2026. The actual prime-power and mixed-prime coefficient estimates
give a uniform quadratic remainder for the physical reciprocal sequence.
The unsmoothed Chebyshev discrepancy is not asserted to belong to QHilbert.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto

/-- The actual first-order coefficient is von Mangoldt; the quadratic
bound treats prime powers and mixed-prime integers with their exact signs. -/
theorem dampedDivisorCoefficient_second_order {ε : ℝ} (hε : 0 ≤ ε)
    {n : ℕ} (hn : 2 ≤ n) :
    |dampedDivisorCoefficient ε n - ε * ArithmeticFunction.vonMangoldt n| ≤
      ε ^ 2 * (Real.log n) ^ 2 := by
  by_cases hpp : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := hpp
    rw [← Nat.prime_iff] at hp
    cases k with
    | zero => omega
    | succ k =>
      rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega : k + 1 ≠ 0),
        ArithmeticFunction.vonMangoldt_apply_prime hp]
      have he := dampedDivisorCoefficient_prime_pow_second_order hε hp k
      have hlog : 0 ≤ Real.log (p : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hp.one_le)
      have hpn : (p : ℝ) ≤ ((p ^ (k + 1) : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_of_dvd (pow_pos hp.pos (k + 1))
          (dvd_pow_self p (by omega : k + 1 ≠ 0))
      have hl := Real.log_le_log (by exact_mod_cast hp.pos : (0 : ℝ) < p) hpn
      have hsq : (Real.log p) ^ 2 ≤ (Real.log ((p ^ (k + 1) : ℕ) : ℝ)) ^ 2 := by
        nlinarith
      have hs := mul_le_mul_of_nonneg_left hsq (sq_nonneg ε)
      nlinarith [mul_nonneg (sq_nonneg ε) (sq_nonneg (Real.log p))]
  · obtain ⟨p, hp, q, hq, hpq⟩ :=
      (Nat.not_isPrimePow_iff_nontrivial_of_two_le hn).mp hpp
    rw [(ArithmeticFunction.vonMangoldt_eq_zero_iff).mpr hpp, mul_zero, sub_zero,
      abs_of_nonneg (dampedDivisorCoefficient_nonneg hε n)]
    simpa only [mul_pow] using
      dampedDivisorCoefficient_le_sq_mul_log_sq_of_two_primes hε hp hq hpq

/-- The complete finite prefix has first derivative equal to the Chebyshev
prime-power sum, with a uniform log-squared pointwise remainder. -/
theorem dampedMobiusPrefix_second_order {ε : ℝ} (hε : 0 ≤ ε)
    {n : ℕ} (hn : 1 ≤ n) :
    |dampedMobiusPrefix ε n - 1 -
        ε * (∑ k ∈ Finset.range (n + 1), ArithmeticFunction.vonMangoldt k)| ≤
      (n : ℝ) * (ε ^ 2 * (Real.log n) ^ 2) := by
  have h1 : 1 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hprefix : dampedMobiusPrefix ε n =
      ∑ k ∈ Finset.range (n + 1), dampedDivisorCoefficient ε k :=
    dampedMobiusPrefix_eq_sum_divisors ε n
  have hsum : (∑ k ∈ Finset.range (n + 1),
      (dampedDivisorCoefficient ε k - ε * ArithmeticFunction.vonMangoldt k)) =
      dampedMobiusPrefix ε n -
        ε * (∑ k ∈ Finset.range (n + 1), ArithmeticFunction.vonMangoldt k) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← hprefix]
  have herase := Finset.sum_erase_add (Finset.range (n + 1))
    (fun k => dampedDivisorCoefficient ε k -
      ε * ArithmeticFunction.vonMangoldt k) h1
  rw [dampedDivisorCoefficient_one, ArithmeticFunction.vonMangoldt_apply_one,
    mul_zero, sub_zero, hsum] at herase
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hnonneg : 0 ≤ ε ^ 2 * (Real.log n) ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have heq : dampedMobiusPrefix ε n - 1 -
      ε * (∑ k ∈ Finset.range (n + 1), ArithmeticFunction.vonMangoldt k) =
      ∑ k ∈ (Finset.range (n + 1)).erase 1,
        (dampedDivisorCoefficient ε k - ε * ArithmeticFunction.vonMangoldt k) := by
    linarith
  rw [heq]
  calc
    _ ≤ ∑ k ∈ (Finset.range (n + 1)).erase 1,
        |dampedDivisorCoefficient ε k - ε * ArithmeticFunction.vonMangoldt k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ (Finset.range (n + 1)).erase 1, ε ^ 2 * (Real.log n) ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      obtain ⟨hk1, hkR⟩ := Finset.mem_erase.mp hk
      have hkn : k ≤ n := by
        have := Finset.mem_range.mp hkR
        omega
      by_cases hk0 : k = 0
      · simpa [hk0] using hnonneg
      · have hk2 : 2 ≤ k := by omega
        have hkl : 0 ≤ Real.log (k : ℝ) :=
          Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
        have hln := Real.log_le_log
          (by exact_mod_cast (by omega : 0 < k) : (0 : ℝ) < k)
          (by exact_mod_cast hkn : (k : ℝ) ≤ n)
        have hsq : (Real.log k) ^ 2 ≤ (Real.log n) ^ 2 := by nlinarith
        exact (dampedDivisorCoefficient_second_order hε hk2).trans
          (mul_le_mul_of_nonneg_left hsq (sq_nonneg ε))
    _ = _ := by simp [Finset.card_erase_of_mem h1]

/-- The centering error is combined with the genuine arithmetic prefix error. -/
theorem dampedMobius_reciprocal_second_order_of_density_bound
    {ε c : ℝ} (hε : 0 ≤ ε) (hc : |c - ε| ≤ ε ^ 2)
    {n : ℕ} (hn : 1 ≤ n) :
    |(dampedMobiusPrefix ε n - (n : ℝ) * c) / ((n : ℝ) + 1) -
        1 / ((n : ℝ) + 1) -
        ε * ((∑ k ∈ Finset.range (n + 1), ArithmeticFunction.vonMangoldt k) - n) /
          ((n : ℝ) + 1)| ≤ ε ^ 2 * (1 + (Real.log n) ^ 2) := by
  have hp := dampedMobiusPrefix_second_order hε hn
  have hnp : 0 < (n : ℝ) + 1 := by positivity
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hcenter : |(n : ℝ) * (c - ε)| ≤ (n : ℝ) * ε ^ 2 := by
    rw [abs_mul, abs_of_nonneg hn0]
    exact mul_le_mul_of_nonneg_left hc hn0
  have he : (dampedMobiusPrefix ε n - (n : ℝ) * c) / ((n : ℝ) + 1) -
        1 / ((n : ℝ) + 1) -
        ε * ((∑ k ∈ Finset.range (n + 1), ArithmeticFunction.vonMangoldt k) - n) /
          ((n : ℝ) + 1) =
      ((dampedMobiusPrefix ε n - 1 -
        ε * (∑ k ∈ Finset.range (n + 1), ArithmeticFunction.vonMangoldt k)) -
          (n : ℝ) * (c - ε)) / ((n : ℝ) + 1) := by ring
  rw [he, abs_div, abs_of_pos hnp]
  apply (div_le_iff₀ hnp).mpr
  calc
    _ ≤ |dampedMobiusPrefix ε n - 1 -
        ε * (∑ k ∈ Finset.range (n + 1), ArithmeticFunction.vonMangoldt k)| +
          |(n : ℝ) * (c - ε)| := abs_sub _ _
    _ ≤ (n : ℝ) * (ε ^ 2 * (Real.log n) ^ 2) + (n : ℝ) * ε ^ 2 :=
      add_le_add hp hcenter
    _ ≤ ε ^ 2 * (1 + (Real.log n) ^ 2) * ((n : ℝ) + 1) := by
      nlinarith [sq_nonneg ε,
        mul_nonneg (sq_nonneg ε) (sq_nonneg (Real.log n))]

/-- Unconditional pointwise second-order estimate for the actual reciprocal
Mobius/zeta family. The first derivative is the smoothed Chebyshev discrepancy. -/
theorem dampedMobius_reciprocal_second_order {ε : ℝ} (hε : 0 < ε)
    {n : ℕ} (hn : 1 ≤ n) :
    |(dampedMobiusPrefix ε n - (n : ℝ) *
        (1 / riemannZeta (1 + (ε : ℂ))).re) / ((n : ℝ) + 1) -
        1 / ((n : ℝ) + 1) -
        ε * ((∑ k ∈ Finset.range (n + 1), ArithmeticFunction.vonMangoldt k) - n) /
          ((n : ℝ) + 1)| ≤ ε ^ 2 * (1 + (Real.log n) ^ 2) :=
  dampedMobius_reciprocal_second_order_of_density_bound hε.le
    (dampedMobius_density_sub_epsilon_le_sq hε) hn

end RiemannResearch.RH.Pareto
