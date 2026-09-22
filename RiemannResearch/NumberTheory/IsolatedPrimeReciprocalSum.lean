/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.NumberTheory.Bertrand
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# An isolated prime denominator prevents reciprocal-sum cancellation

Source: continuation of the user-provided Pareto capacity handoff, Section 11.
Bertrand's postulate supplies a prime in the upper half of a finite interval.
The remaining proof clears denominators in a finite integer sum.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.NumberTheory

/-- Bertrand supplies an isolated prime denominator in every positive
reciprocal Möbius sum beyond its first term. -/
theorem exists_prime_upper_half {N : ℕ} (hN : 2 ≤ N) :
    ∃ p : ℕ, Nat.Prime p ∧ p ≤ N ∧ N < 2 * p := by
  have hhalf : N / 2 ≠ 0 := by omega
  obtain ⟨p, hp, hlt, hle⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (N / 2) hhalf
  refine ⟨p, hp, ?_, ?_⟩ <;> omega

/-- An integer-weighted reciprocal sum cannot vanish if one denominator
has an isolated prime factor and its numerator is minus one. -/
theorem reciprocal_sum_ne_zero_of_isolated_prime
    (s : Finset ℕ) (a : ℕ → ℤ) (p : ℕ)
    (hp : Nat.Prime p) (hps : p ∈ s)
    (hpos : ∀ d ∈ s, 0 < d)
    (hiso : ∀ d ∈ s, p ∣ d → d = p)
    (hap : a p = -1) :
    (∑ d ∈ s, (a d : ℝ) / (d : ℝ)) ≠ 0 := by
  let t := s.erase p
  let D : ℕ := ∏ d ∈ t, d
  let A : ℤ := ∑ d ∈ t, a d * ((∏ e ∈ t.erase d, e : ℕ) : ℤ)
  have hnot : ∀ d ∈ t, ¬ p ∣ d := by
    intro d hd hpd
    have hdne : d ≠ p := (Finset.mem_erase.mp hd).1
    exact hdne (hiso d (Finset.mem_of_mem_erase hd) hpd)
  have hDnot : ¬ p ∣ D := by
    intro h
    obtain ⟨d, hd, hpd⟩ := (hp.prime.dvd_finsetProd_iff (fun d : ℕ => d)).mp h
    exact hnot d hd hpd
  have hclear :
      (D : ℝ) * (∑ d ∈ t, (a d : ℝ) / (d : ℝ)) = (A : ℝ) := by
    simp only [A, Int.cast_sum, Int.cast_mul, Int.cast_natCast, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have hd0 : (d : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (hpos d (Finset.mem_of_mem_erase hd)))
    have hprod : D = d * ∏ e ∈ t.erase d, e := by
      exact (Finset.mul_prod_erase t (fun e : ℕ => e) hd).symm
    rw [hprod, Nat.cast_mul]
    field_simp [hd0]
  intro hzero
  have hsplit : (∑ d ∈ t, (a d : ℝ) / (d : ℝ)) + (-1 : ℝ) / (p : ℝ) = 0 := by
    rw [← Finset.sum_erase_add s (fun d => (a d : ℝ) / (d : ℝ)) hps] at hzero
    simpa only [t, hap, Int.cast_neg, Int.cast_one] using hzero
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hsum : (∑ d ∈ t, (a d : ℝ) / (d : ℝ)) = 1 / (p : ℝ) := by
    rw [neg_div] at hsplit
    linarith
  have hDR : (p : ℝ) * (A : ℝ) = (D : ℝ) := by
    rw [← hclear, hsum]
    field_simp [hpR]
  have hDZ : (p : ℤ) * A = (D : ℤ) := by exact_mod_cast hDR
  exact hDnot (Int.natCast_dvd_natCast.mp ⟨A, hDZ.symm⟩)


end RiemannResearch.NumberTheory
