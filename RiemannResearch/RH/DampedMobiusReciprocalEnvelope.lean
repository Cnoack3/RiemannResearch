/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.DampedMobiusCoefficients
import RiemannResearch.RH.DampedMobiusMellinArithmetic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Logarithmic reciprocal envelopes for damped Mobius prefixes

Source: user-provided Reciprocal_Density_CRT_Nyman_Beurling_2026-11-08.pdf,
Theorem 6.2 and Section 10. The existing positive divisor coefficient
bounds improve the original log-squared pointwise envelope to log.
The scalar density constraints remain explicit in the second theorem.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto

/-- The positive damped divisor coefficients give a logarithmic prefix bound. -/
theorem dampedMobiusPrefix_sub_one_bounds {ε : ℝ} (hε : 0 ≤ ε)
    {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ dampedMobiusPrefix ε n - 1 ∧
      dampedMobiusPrefix ε n - 1 ≤ (n : ℝ) * (ε * Real.log n) := by
  have h1 : 1 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hprefix : dampedMobiusPrefix ε n =
      ∑ k ∈ Finset.range (n + 1), dampedDivisorCoefficient ε k := by
    exact dampedMobiusPrefix_eq_sum_divisors ε n
  have hs := Finset.sum_erase_add (Finset.range (n + 1))
    (fun k => dampedDivisorCoefficient ε k) h1
  rw [dampedDivisorCoefficient_one, ← hprefix] at hs
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hprod : 0 ≤ ε * Real.log n := mul_nonneg hε hlog
  have hnonneg : 0 ≤ ∑ k ∈ (Finset.range (n + 1)).erase 1,
      dampedDivisorCoefficient ε k :=
    Finset.sum_nonneg (fun k _ => dampedDivisorCoefficient_nonneg hε k)
  have hupper : (∑ k ∈ (Finset.range (n + 1)).erase 1,
      dampedDivisorCoefficient ε k) ≤ (n : ℝ) * (ε * Real.log n) := by
    calc
      _ ≤ ∑ _k ∈ (Finset.range (n + 1)).erase 1, ε * Real.log n := by
        apply Finset.sum_le_sum
        intro k hk
        obtain ⟨hk1, hkR⟩ := Finset.mem_erase.mp hk
        have hkn : k ≤ n := by
          have := Finset.mem_range.mp hkR
          omega
        by_cases hk0 : k = 0
        · simpa [hk0] using hprod
        · have hk2 : 2 ≤ k := by omega
          have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
          exact (dampedDivisorCoefficient_le_mul_log hε hk2).trans
            (mul_le_mul_of_nonneg_left
              (Real.log_le_log hkpos (by exact_mod_cast hkn)) hε)
      _ = _ := by simp [Finset.card_erase_of_mem h1]
  constructor <;> linarith

/-- Reciprocal smoothing turns the logarithmic arithmetic prefix estimate
into a logarithmic pointwise error envelope. The scalar c is kept explicit;
the zeta integral sandwich supplies 0≤c≤ε for c=1/zeta(1+ε). -/
theorem dampedMobius_reciprocal_error_le_log {ε c : ℝ}
    (hε : 0 ≤ ε) (hc : 0 ≤ c) (hcε : c ≤ ε)
    {n : ℕ} (hn : 1 ≤ n) :
    |(dampedMobiusPrefix ε n - (n : ℝ) * c) / ((n : ℝ) + 1) -
        1 / ((n : ℝ) + 1)| ≤ ε * (1 + Real.log n) := by
  obtain ⟨hlo, hup⟩ := dampedMobiusPrefix_sub_one_bounds hε hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnp : 0 < (n : ℝ) + 1 := by positivity
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hprod : 0 ≤ ε * Real.log n := mul_nonneg hε hlog
  have hnc : 0 ≤ (n : ℝ) * c := mul_nonneg hn0 hc
  have hncε : (n : ℝ) * c ≤ (n : ℝ) * ε :=
    mul_le_mul_of_nonneg_left hcε hn0
  have he : (dampedMobiusPrefix ε n - (n : ℝ) * c) / ((n : ℝ) + 1) -
      1 / ((n : ℝ) + 1) =
      ((dampedMobiusPrefix ε n - 1) - (n : ℝ) * c) / ((n : ℝ) + 1) := by ring
  rw [he, abs_div, abs_of_pos hnp]
  apply (div_le_iff₀ hnp).mpr
  calc
    _ ≤ |dampedMobiusPrefix ε n - 1| + |(n : ℝ) * c| := abs_sub _ _
    _ = (dampedMobiusPrefix ε n - 1) + (n : ℝ) * c := by
      rw [abs_of_nonneg hlo, abs_of_nonneg hnc]
    _ ≤ (n : ℝ) * (ε * Real.log n) + (n : ℝ) * ε := add_le_add hup hncε
    _ ≤ ε * (1 + Real.log n) * ((n : ℝ) + 1) := by nlinarith

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto

/-- Two distinct prime factors give a quadratic damping saving, retaining the
actual signed Mobius divisor coefficient through its nonnegative Euler product. -/
theorem dampedDivisorCoefficient_le_sq_mul_log_sq_of_two_primes
    {ε : ℝ} (hε : 0 ≤ ε) {n p q : ℕ}
    (hp : p ∈ n.primeFactors) (hq : q ∈ n.primeFactors) (hpq : p ≠ q) :
    dampedDivisorCoefficient ε n ≤ (ε * Real.log n)^2 := by
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hqq : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hn0 : n ≠ 0 := (Nat.mem_primeFactors.mp hp).2.2
  have hpn : (p : ℝ) ≤ n := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn0)
      (Nat.mem_primeFactors.mp hp).2.1
  have hqn : (q : ℝ) ≤ n := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn0)
      (Nat.mem_primeFactors.mp hq).2.1
  have hpl : 1 - (p : ℝ)^(-ε) ≤ ε * Real.log n :=
    (dampedPrimeFactor_le_mul_log ε hpp).trans
      (mul_le_mul_of_nonneg_left
        (Real.log_le_log (by exact_mod_cast hpp.pos) hpn) hε)
  have hql : 1 - (q : ℝ)^(-ε) ≤ ε * Real.log n :=
    (dampedPrimeFactor_le_mul_log ε hqq).trans
      (mul_le_mul_of_nonneg_left
        (Real.log_le_log (by exact_mod_cast hqq.pos) hqn) hε)
  have hap := (dampedPrimeFactor_bounds hε hpp).1
  have haq := (dampedPrimeFactor_bounds hε hqq).1
  have ht : 0 ≤ ε * Real.log n := hap.trans hpl
  have hqe : q ∈ n.primeFactors.erase p := Finset.mem_erase.mpr ⟨Ne.symm hpq, hq⟩
  have hrest :
      Finset.prod ((n.primeFactors.erase p).erase q) (fun r : ℕ => 1 - (r : ℝ)^(-ε)) ≤ 1 := by
    apply Finset.prod_le_one
    · intro r hr
      exact (dampedPrimeFactor_bounds hε
        (Nat.prime_of_mem_primeFactors
          (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hr)))).1
    · intro r hr
      exact (dampedPrimeFactor_bounds hε
        (Nat.prime_of_mem_primeFactors
          (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hr)))).2
  rw [dampedDivisorCoefficient_eq_prime_product ε hn0,
    ← Finset.mul_prod_erase n.primeFactors (fun r => 1 - (r : ℝ)^(-ε)) hp,
    ← Finset.mul_prod_erase (n.primeFactors.erase p)
      (fun r => 1 - (r : ℝ)^(-ε)) hqe]
  calc
    _ ≤ (1 - (p : ℝ)^(-ε)) * ((1 - (q : ℝ)^(-ε)) * 1) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hrest haq) hap
    _ = (1 - (p : ℝ)^(-ε)) * (1 - (q : ℝ)^(-ε)) := by ring
    _ ≤ (ε * Real.log n) * (ε * Real.log n) := mul_le_mul hpl hql haq ht
    _ = _ := (pow_two _).symm

end RiemannResearch.RH.Pareto
