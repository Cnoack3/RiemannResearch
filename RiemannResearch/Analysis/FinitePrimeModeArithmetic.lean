/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega

/-!
# Finite prime mode arithmetic

Finite prime products reduce integer torus modes to reduced rational frequencies.
Unique factorization proves both nonzero-frequency independence and the
single-prime-axis characterization of integer prime powers.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.PrimePhaseTorus

def primeProduct (P : Finset ℕ) (e : ℕ → ℕ) : ℕ :=
  ∏ p ∈ P, p ^ e p

def primeNumerator (P : Finset ℕ) (k : ℕ → ℤ) : ℕ :=
  primeProduct P (fun p => (k p).toNat)

def primeDenominator (P : Finset ℕ) (k : ℕ → ℤ) : ℕ :=
  primeProduct P (fun p => (-k p).toNat)

def primeFrequency (P : Finset ℕ) (k : ℕ → ℤ) : ℝ :=
  ∑ p ∈ P, (k p : ℝ) * Real.log p

theorem primeProduct_ne_zero (P : Finset ℕ) (e : ℕ → ℕ)
    (hP : ∀ p ∈ P, p.Prime) : primeProduct P e ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr
    (fun p hp => pow_ne_zero _ (hP p hp).ne_zero)

theorem primeProduct_pos (P : Finset ℕ) (e : ℕ → ℕ)
    (hP : ∀ p ∈ P, p.Prime) : 0 < primeProduct P e :=
  Nat.pos_of_ne_zero (primeProduct_ne_zero P e hP)

theorem primeProduct_factorization (P : Finset ℕ) (e : ℕ → ℕ)
    (hP : ∀ p ∈ P, p.Prime) (q : ℕ) :
    (primeProduct P e).factorization q = if q ∈ P then e q else 0 := by
  classical
  unfold primeProduct
  rw [Nat.factorization_prod_apply
    (fun p hp => pow_ne_zero _ (hP p hp).ne_zero)]
  calc
    _ = ∑ p ∈ P, (if p = q then e p else 0) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [(hP p hp).factorization_pow]
      simp [Finsupp.single_apply]
    _ = if q ∈ P then e q else 0 := by
      by_cases hq : q ∈ P
      · rw [if_pos hq]
        simpa using (Finset.sum_eq_single (s := P)
          (f := fun p => if p = q then e p else 0) q
          (fun p hp hpq => by simp [hpq])
          (fun h => (h hq).elim))
      · rw [if_neg hq]
        apply Finset.sum_eq_zero
        intro p hp
        have hpq : p ≠ q := by rintro rfl; exact hq hp
        simp [hpq]

theorem primeProduct_eq_iff (P : Finset ℕ) (e f : ℕ → ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    primeProduct P e = primeProduct P f ↔ ∀ p ∈ P, e p = f p := by
  constructor
  · intro h p hp
    have hq := congrArg (fun n : ℕ => n.factorization p) h
    simpa [primeProduct_factorization P e hP,
      primeProduct_factorization P f hP, hp] using hq
  · intro h
    apply Finset.prod_congr rfl
    intro p hp
    rw [h p hp]

theorem primeProduct_eq_one_iff (P : Finset ℕ) (e : ℕ → ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    primeProduct P e = 1 ↔ ∀ p ∈ P, e p = 0 := by
  simpa [primeProduct] using primeProduct_eq_iff P e (fun _ => 0) hP

theorem primeNumerator_eq_denominator_iff (P : Finset ℕ) (k : ℕ → ℤ)
    (hP : ∀ p ∈ P, p.Prime) :
    primeNumerator P k = primeDenominator P k ↔ ∀ p ∈ P, k p = 0 := by
  rw [primeNumerator, primeDenominator, primeProduct_eq_iff P _ _ hP]
  constructor
  · intro h p hp
    have hh := h p hp
    have hi := Int.toNat_sub_toNat_neg (k p)
    omega
  · intro h p hp
    simp [h p hp]

theorem primeNumerator_eq_one_iff (P : Finset ℕ) (k : ℕ → ℤ)
    (hP : ∀ p ∈ P, p.Prime) :
    primeNumerator P k = 1 ↔ ∀ p ∈ P, k p ≤ 0 := by
  rw [primeNumerator, primeProduct_eq_one_iff P _ hP]
  constructor <;> intro h p hp <;> have hh := h p hp <;> omega

theorem primeDenominator_eq_one_iff (P : Finset ℕ) (k : ℕ → ℤ)
    (hP : ∀ p ∈ P, p.Prime) :
    primeDenominator P k = 1 ↔ ∀ p ∈ P, 0 ≤ k p := by
  rw [primeDenominator, primeProduct_eq_one_iff P _ hP]
  constructor <;> intro h p hp <;> have hh := h p hp <;> omega

theorem primeNumerator_denominator_coprime (P : Finset ℕ) (k : ℕ → ℤ)
    (hP : ∀ p ∈ P, p.Prime) :
    Nat.Coprime (primeNumerator P k) (primeDenominator P k) := by
  by_contra h
  obtain ⟨q, hq, hqN, hqD⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have hN := hq.factorization_pos_of_dvd
    (primeProduct_ne_zero P (fun p => (k p).toNat) hP) hqN
  have hD := hq.factorization_pos_of_dvd
    (primeProduct_ne_zero P (fun p => (-k p).toNat) hP) hqD
  change 0 < (primeProduct P (fun p => (k p).toNat)).factorization q at hN
  change 0 < (primeProduct P (fun p => (-k p).toNat)).factorization q at hD
  rw [primeProduct_factorization P _ hP q] at hN hD
  by_cases hqP : q ∈ P
  · simp only [hqP, if_true] at hN hD
    omega
  · simp [hqP] at hN

theorem primeDenominator_dvd_numerator_iff (P : Finset ℕ) (k : ℕ → ℤ)
    (hP : ∀ p ∈ P, p.Prime) :
    primeDenominator P k ∣ primeNumerator P k ↔ primeDenominator P k = 1 := by
  constructor
  · exact (primeNumerator_denominator_coprime P k hP).symm.eq_one_of_dvd
  · intro h
    simp [h]

theorem primeProduct_log (P : Finset ℕ) (e : ℕ → ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    Real.log (primeProduct P e : ℝ) =
      ∑ p ∈ P, (e p : ℝ) * Real.log p := by
  unfold primeProduct
  push_cast
  rw [Real.log_prod (fun p hp =>
    pow_ne_zero _ (by exact_mod_cast (hP p hp).ne_zero))]
  simp only [Real.log_pow]

theorem prime_log_ratio_eq_frequency (P : Finset ℕ) (k : ℕ → ℤ)
    (hP : ∀ p ∈ P, p.Prime) :
    Real.log ((primeNumerator P k : ℝ) / (primeDenominator P k : ℝ)) =
      primeFrequency P k := by
  rw [Real.log_div
    (by exact_mod_cast primeProduct_ne_zero P (fun p => (k p).toNat) hP)
    (by exact_mod_cast primeProduct_ne_zero P (fun p => (-k p).toNat) hP)]
  rw [primeNumerator, primeDenominator, primeProduct_log P _ hP,
    primeProduct_log P _ hP, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hi : ((k p).toNat : ℝ) - ((-k p).toNat : ℝ) = (k p : ℝ) := by
    exact_mod_cast Int.toNat_sub_toNat_neg (k p)
  rw [← sub_mul, hi]

theorem primeFrequency_eq_zero_iff (P : Finset ℕ) (k : ℕ → ℤ)
    (hP : ∀ p ∈ P, p.Prime) :
    primeFrequency P k = 0 ↔ ∀ p ∈ P, k p = 0 := by
  constructor
  · intro h
    have hN : 0 < (primeNumerator P k : ℝ) := by
      exact_mod_cast primeProduct_pos P (fun p => (k p).toNat) hP
    have hD : 0 < (primeDenominator P k : ℝ) := by
      exact_mod_cast primeProduct_pos P (fun p => (-k p).toNat) hP
    have hr : (primeNumerator P k : ℝ) / (primeDenominator P k : ℝ) = 1 :=
      Real.eq_one_of_pos_of_log_eq_zero (div_pos hN hD)
        ((prime_log_ratio_eq_frequency P k hP).trans h)
    have heq : primeNumerator P k = primeDenominator P k := by
      exact_mod_cast (div_eq_one_iff_eq hD.ne').mp hr
    exact (primeNumerator_eq_denominator_iff P k hP).mp heq
  · intro h
    unfold primeFrequency
    apply Finset.sum_eq_zero
    intro p hp
    simp [h p hp]

theorem primeProduct_eq_single (P : Finset ℕ) (e : ℕ → ℕ)
    {p : ℕ} (hp : p ∈ P) (he : ∀ q ∈ P, q ≠ p → e q = 0) :
    primeProduct P e = p ^ e p := by
  classical
  unfold primeProduct
  exact Finset.prod_eq_single p
    (fun q hq hqp => by simp [he q hq hqp])
    (fun h => (h hp).elim)

theorem primeProduct_isPrimePow_iff (P : Finset ℕ) (e : ℕ → ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    IsPrimePow (primeProduct P e) ↔
      ∃ p ∈ P, 0 < e p ∧ ∀ q ∈ P, q ≠ p → e q = 0 := by
  classical
  constructor
  · intro h
    obtain ⟨p, a, ha, hf⟩ := isPrimePow_iff_factorization_eq_single.mp h
    have hap : (primeProduct P e).factorization p = a := by
      rw [hf]
      simp
    have hp : p ∈ P := by
      by_contra hp
      rw [primeProduct_factorization P e hP p, if_neg hp] at hap
      omega
    have hep : e p = a := by
      simpa [primeProduct_factorization P e hP p, hp] using hap
    refine ⟨p, hp, by omega, ?_⟩
    intro q hq hqp
    have heq : (primeProduct P e).factorization q = 0 := by
      rw [hf]
      simp [Finsupp.single_apply, hqp, Ne.symm hqp]
    simpa [primeProduct_factorization P e hP q, hq] using heq
  · intro h
    obtain ⟨p, hp, hep, he⟩ := h
    refine ⟨p, e p, (hP p hp).prime, hep, ?_⟩
    exact (primeProduct_eq_single P e hp he).symm

def PositivePrimeAxis (P : Finset ℕ) (k : ℕ → ℤ) : Prop :=
  ∃ p ∈ P, 0 < k p ∧ ∀ q ∈ P, q ≠ p → k q = 0

theorem prime_integer_prime_power_iff_positive_axis
    (P : Finset ℕ) (k : ℕ → ℤ) (hP : ∀ p ∈ P, p.Prime) :
    (primeDenominator P k ∣ primeNumerator P k ∧
      IsPrimePow (primeNumerator P k / primeDenominator P k)) ↔
        PositivePrimeAxis P k := by
  constructor
  · rintro ⟨hdiv, hpow⟩
    have hD : primeDenominator P k = 1 :=
      (primeDenominator_dvd_numerator_iff P k hP).mp hdiv
    have hnonneg := (primeDenominator_eq_one_iff P k hP).mp hD
    rw [hD, Nat.div_one] at hpow
    obtain ⟨p, hp, hep, he⟩ :=
      (primeProduct_isPrimePow_iff P (fun p => (k p).toNat) hP).mp hpow
    refine ⟨p, hp, by omega, ?_⟩
    intro q hq hqp
    have h0 := he q hq hqp
    have hpos := hnonneg q hq
    omega
  · rintro ⟨p, hp, hep, he⟩
    have hnonneg : ∀ q ∈ P, 0 ≤ k q := by
      intro q hq
      by_cases hqp : q = p
      · subst q; omega
      · rw [he q hq hqp]
    have hD := (primeDenominator_eq_one_iff P k hP).mpr hnonneg
    refine ⟨by simp [hD], ?_⟩
    rw [hD, Nat.div_one]
    apply (primeProduct_isPrimePow_iff P (fun q => (k q).toNat) hP).mpr
    refine ⟨p, hp, by omega, ?_⟩
    intro q hq hqp
    simp [he q hq hqp]

end RiemannResearch.Analysis.PrimePhaseTorus
