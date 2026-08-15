/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.GroupTheory.AddSubgroupCRT
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Prime.Int

/-!
# Exact Chinese remainder theory for two prime phases

For a prime (p), the phase `γ ↦ p^(iγ)` has additive period
(2π / \log p). This module defines the corresponding exact residue group and
specializes the two-subgroup Chinese remainder theorem to two distinct primes.

The resulting modular map is injective, its image is exactly the kernel of the
overlap-difference map, and that difference map is surjective. The proof of
injectivity is unconditional: unique factorization rules out a nonzero integer
relation between the logarithms of two distinct primes.

This module formalizes the exact algebraic CRT. Density and Haar
equidistribution of the phase orbit are separate topological statements and
are not asserted here.

Source: user-provided argument.
-/

namespace RiemannResearch.RH.PrimePhaseCRT

open RiemannResearch.GroupTheory

noncomputable section

/-- A nonnegative integer relation between logarithms of distinct primes is
trivial. -/
theorem natPrimeLogRelation
    {p q m n : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (h : (m : ℝ) * Real.log (q : ℝ) =
      (n : ℝ) * Real.log (p : ℝ)) :
    m = 0 ∧ n = 0 := by
  have hpLog : 0 < Real.log (p : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hp.one_lt
  have hqLog : 0 < Real.log (q : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hq.one_lt
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq.pos
  by_cases hm : m = 0
  · subst m
    have hnProd : (n : ℝ) * Real.log (p : ℝ) = 0 := by
      simpa using h.symm
    have hnR : (n : ℝ) = 0 :=
      (mul_eq_zero.mp hnProd).resolve_right hpLog.ne'
    have hn : n = 0 := by exact_mod_cast hnR
    exact ⟨rfl, hn⟩
  by_cases hn : n = 0
  · subst n
    have hmProd : (m : ℝ) * Real.log (q : ℝ) = 0 := by
      simpa using h
    have hmR : (m : ℝ) = 0 :=
      (mul_eq_zero.mp hmProd).resolve_right hqLog.ne'
    have hm' : m = 0 := by exact_mod_cast hmR
    exact (hm hm').elim
  have hlogpow :
      Real.log ((q : ℝ) ^ m) = Real.log ((p : ℝ) ^ n) := by
    simpa only [Real.log_pow] using h
  have hpowR : (q : ℝ) ^ m = (p : ℝ) ^ n :=
    Real.log_injOn_pos (pow_pos hqR m) (pow_pos hpR n) hlogpow
  have hpowN : q ^ m = p ^ n := by
    exact_mod_cast hpowR
  have hqp : q = p := (hq.pow_inj' hp hm hn hpowN).1
  exact (hpq hqp.symm).elim

private theorem nonnegIntPrimeLogRelation
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {m n : ℤ} (hm : 0 ≤ m) (hn : 0 ≤ n)
    (h : (m : ℝ) * Real.log (q : ℝ) =
      (n : ℝ) * Real.log (p : ℝ)) :
    m = 0 ∧ n = 0 := by
  have hmCast : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hm
  have hnCast : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hn
  have hnat :
      (m.toNat : ℝ) * Real.log (q : ℝ) =
        (n.toNat : ℝ) * Real.log (p : ℝ) := by
    rw [hmCast, hnCast]
    exact h
  obtain ⟨hm0, hn0⟩ := natPrimeLogRelation hp hq hpq hnat
  constructor
  · rw [← Int.toNat_of_nonneg hm, hm0]
    rfl
  · rw [← Int.toNat_of_nonneg hn, hn0]
    rfl

/-- An integer relation between logarithms of distinct primes is trivial. -/
theorem intPrimeLogRelation
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {m n : ℤ}
    (h : (m : ℝ) * Real.log (q : ℝ) =
      (n : ℝ) * Real.log (p : ℝ)) :
    m = 0 ∧ n = 0 := by
  have hpLog : 0 < Real.log (p : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hp.one_lt
  have hqLog : 0 < Real.log (q : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hq.one_lt
  by_cases hm : 0 ≤ m
  · have hn : 0 ≤ n := by
      by_contra hn
      have hnR : (n : ℝ) < 0 := by
        exact_mod_cast (lt_of_not_ge hn)
      have hmR : 0 ≤ (m : ℝ) := by exact_mod_cast hm
      have lhsNonneg :
          0 ≤ (m : ℝ) * Real.log (q : ℝ) :=
        mul_nonneg hmR hqLog.le
      have rhsNonneg :
          0 ≤ (n : ℝ) * Real.log (p : ℝ) := by
        rw [← h]
        exact lhsNonneg
      exact (not_lt_of_ge rhsNonneg)
        (mul_neg_of_neg_of_pos hnR hpLog)
    exact nonnegIntPrimeLogRelation hp hq hpq hm hn h
  · have hmneg : m < 0 := lt_of_not_ge hm
    have hn : n ≤ 0 := by
      by_contra hn
      have hnR : 0 < (n : ℝ) := by
        exact_mod_cast (lt_of_not_ge hn)
      have hmR : (m : ℝ) < 0 := by exact_mod_cast hmneg
      have lhsNeg :
          (m : ℝ) * Real.log (q : ℝ) < 0 :=
        mul_neg_of_neg_of_pos hmR hqLog
      have rhsPos :
          0 < (n : ℝ) * Real.log (p : ℝ) :=
        mul_pos hnR hpLog
      have lhsPos :
          0 < (m : ℝ) * Real.log (q : ℝ) := by
        rw [h]
        exact rhsPos
      exact (not_lt_of_ge (le_of_lt lhsPos)) lhsNeg
    have hneg :
        ((-m : ℤ) : ℝ) * Real.log (q : ℝ) =
          ((-n : ℤ) : ℝ) * Real.log (p : ℝ) := by
      norm_num only [Int.cast_neg]
      nlinarith [h]
    obtain ⟨hm0, hn0⟩ :=
      nonnegIntPrimeLogRelation hp hq hpq
        (neg_nonneg.mpr (le_of_lt hmneg)) (neg_nonneg.mpr hn) hneg
    exact ⟨neg_eq_zero.mp hm0, neg_eq_zero.mp hn0⟩

/-- An integer relation between the reciprocal logarithms of two distinct
primes is trivial. -/
theorem intDivLogRelation
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {m n : ℤ}
    (h : (m : ℝ) / Real.log (p : ℝ) =
      (n : ℝ) / Real.log (q : ℝ)) :
    m = 0 ∧ n = 0 := by
  have hpLog : Real.log (p : ℝ) ≠ 0 := by
    apply ne_of_gt
    apply Real.log_pos
    exact_mod_cast hp.one_lt
  have hqLog : Real.log (q : ℝ) ≠ 0 := by
    apply ne_of_gt
    apply Real.log_pos
    exact_mod_cast hq.one_lt
  apply intPrimeLogRelation hp hq hpq
  exact (div_eq_div_iff hpLog hqLog).mp h

/-- The period (2π / \log p) of the prime phase `γ ↦ p^(iγ)`. -/
def primePeriod (p : ℕ) : ℝ :=
  2 * Real.pi / Real.log (p : ℝ)

/-- The subgroup of real ordinates invisible to the `p`-phase. -/
def periodSubgroup (p : ℕ) : AddSubgroup ℝ :=
  AddSubgroup.zmultiples (primePeriod p)

/-- The exact additive residue group for the `p`-phase. -/
abbrev Residue (p : ℕ) :=
  ℝ ⧸ periodSubgroup p

/-- The exact two-prime modular map. -/
def modularMap (p q : ℕ) :
    ℝ →+ Residue p × Residue q :=
  AddSubgroupCRT.diagonal (periodSubgroup p) (periodSubgroup q)

/-- The pairwise overlap obstruction. -/
def overlapDifference (p q : ℕ) :
    Residue p × Residue q →+
      ℝ ⧸ (periodSubgroup p ⊔ periodSubgroup q) :=
  AddSubgroupCRT.difference (periodSubgroup p) (periodSubgroup q)

/-- Distinct prime-period subgroups have trivial intersection. -/
theorem periodSubgroup_inf
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    periodSubgroup p ⊓ periodSubgroup q = ⊥ := by
  ext x
  change
    (x ∈ AddSubgroup.zmultiples (primePeriod p) ∧
      x ∈ AddSubgroup.zmultiples (primePeriod q)) ↔ x = 0
  constructor
  · rintro ⟨hxp, hxq⟩
    rw [AddSubgroup.mem_zmultiples_iff] at hxp hxq
    rcases hxp with ⟨m, hm⟩
    rcases hxq with ⟨n, hn⟩
    have heq :
        (m : ℝ) * primePeriod p = (n : ℝ) * primePeriod q := by
      rw [← zsmul_eq_mul, hm, ← hn, zsmul_eq_mul]
    have htwoPi : (2 * Real.pi : ℝ) ≠ 0 :=
      mul_ne_zero (by norm_num) Real.pi_ne_zero
    have hdiv :
        (m : ℝ) / Real.log (p : ℝ) =
          (n : ℝ) / Real.log (q : ℝ) := by
      apply mul_left_cancel₀ htwoPi
      calc
        (2 * Real.pi) * ((m : ℝ) / Real.log (p : ℝ)) =
            (m : ℝ) * primePeriod p := by
              simp only [primePeriod]
              ring
        _ = (n : ℝ) * primePeriod q := heq
        _ = (2 * Real.pi) * ((n : ℝ) / Real.log (q : ℝ)) := by
              simp only [primePeriod]
              ring
    obtain ⟨hm0, _⟩ := intDivLogRelation hp hq hpq hdiv
    rw [hm0, zero_zsmul] at hm
    simpa using hm.symm
  · rintro rfl
    exact ⟨AddSubgroup.zero_mem _, AddSubgroup.zero_mem _⟩

/-- The exact two-prime modular map is injective. -/
theorem modularMap_injective
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Function.Injective (modularMap p q) :=
  (AddSubgroupCRT.diagonal_injective_iff
    (periodSubgroup p) (periodSubgroup q)).2
    (periodSubgroup_inf hp hq hpq)

/-- Exact two-prime phase gluing: a residue pair has a common real lift exactly
when its overlap difference vanishes. -/
theorem modularMap_exact (p q : ℕ) (z : Residue p × Residue q) :
    (∃ γ, modularMap p q γ = z) ↔ overlapDifference p q z = 0 :=
  AddSubgroupCRT.exists_diagonal_eq_iff
    (periodSubgroup p) (periodSubgroup q) z

/-- Every overlap obstruction class is represented by a residue difference. -/
theorem overlapDifference_surjective (p q : ℕ) :
    Function.Surjective (overlapDifference p q) :=
  AddSubgroupCRT.difference_surjective
    (periodSubgroup p) (periodSubgroup q)

end
end RiemannResearch.RH.PrimePhaseCRT
