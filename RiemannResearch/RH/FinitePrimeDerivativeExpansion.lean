/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.RH.FinitePrimeDerivativeProjection
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Finite tensor expansion of the derivative optimizer.

Finite exact identities; no asymptotic arithmetic gain bound is assumed or proved.
-/
noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.FinitePrimeDerivativeExpansion
open FinitePrimeLikelihood FinitePrimeDerivativeProjection

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def subsetConductor (p : ι → ℝ) (A : Finset ι) : ℝ := ∏ i ∈ A, p i
def subsetMobius (A : Finset ι) : ℝ := ∏ _i ∈ A, (-1:ℝ)

def primitiveCoefficient (p : ι → ℝ) (q : ℝ) (A : Finset ι) : ℝ :=
  q*(baseRatio p*subsetConductor p A/(2:ℝ)^(Fintype.card ι) -
    subsetMobius A/zeroMass p)

theorem sum_subset_products (r : ι → ℝ) :
    (∑ A : Finset ι, ∏ i ∈ A, r i) = ∏ i, (1+r i) := by
  simpa using (Finset.prod_one_add (f := r) (Finset.univ : Finset ι)).symm

theorem monomial_eq_subset_prod (A : Finset ι) (x : ι → Bool) :
    finiteMonomial A x = ∏ i ∈ A, boolIndicator (x i) := by
  unfold finiteMonomial
  rw [Fintype.prod_extend_by_one]

theorem weighted_monomial_expansion (r : ι → ℝ) (x : ι → Bool) :
    (∑ A : Finset ι, (∏ i ∈ A, r i)*finiteMonomial A x) =
      ∏ i, (1+r i*boolIndicator (x i)) := by
  simp_rw [monomial_eq_subset_prod, ← Finset.prod_mul_distrib]
  exact sum_subset_products (fun i => r i*boolIndicator (x i))

theorem zeroIndicator_product (x : ι → Bool) :
    zeroIndicator x = ∏ i, (1-boolIndicator (x i)) := by
  by_cases hx : x = zeroConfiguration
  · subst x
    simp [zeroIndicator, zeroConfiguration, boolIndicator]
  · have he : ∃ i, x i ≠ false := by
      by_contra h
      push Not at h
      exact hx (funext h)
    obtain ⟨i, hi⟩ := he
    rw [zeroIndicator, if_neg hx]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    cases hxi : x i <;> simp [hxi, boolIndicator] at hi ⊢

theorem mobius_monomial_expansion (x : ι → Bool) :
    (∑ A : Finset ι, subsetMobius A*finiteMonomial A x) = zeroIndicator x := by
  rw [zeroIndicator_product]
  simpa [subsetMobius, sub_eq_add_neg] using
    weighted_monomial_expansion (fun _ : ι => (-1:ℝ)) x

theorem likelihood_monomial_expansion (p : ι → ℝ)
    (hp1 : ∀ i, p i+1 ≠ 0) (x : ι → Bool) :
    baseRatio p * (∑ A : Finset ι, subsetConductor p A*finiteMonomial A x) =
      finiteLikelihood p x := by
  rw [show (fun A => subsetConductor p A*finiteMonomial A x) =
      (fun A => (∏ i ∈ A, p i)*finiteMonomial A x) from rfl,
    weighted_monomial_expansion]
  unfold finiteLikelihood tensorFunction baseRatio
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact (primeLikelihood_factor (hp1 i) (x i)).symm

theorem mobius_reciprocal_sum (p : ι → ℝ) :
    (∑ A : Finset ι, subsetMobius A/subsetConductor p A) =
      ∏ i, (1-1/p i) := by
  simp only [subsetMobius, subsetConductor, ← Finset.prod_div_distrib]
  simpa [sub_eq_add_neg, div_eq_mul_inv] using sum_subset_products (fun i => (-1:ℝ)/p i)

theorem zeroMass_mul_baseRatio (p : ι → ℝ)
    (hp0 : ∀ i, p i ≠ 0) (hp1 : ∀ i, p i+1 ≠ 0) :
    zeroMass p*baseRatio p = ∏ i, (1-1/p i) := by
  unfold zeroMass baseRatio
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  unfold primeParameter
  field_simp [hp0 i, hp1 i]
  <;> ring

theorem coefficient_constant_sum (p : ι → ℝ) (q : ℝ)
    (hp0 : ∀ i, p i ≠ 0) (hp1 : ∀ i, p i+1 ≠ 0)
    (ha : zeroMass p ≠ 0) :
    (∑ A : Finset ι, primitiveCoefficient p q A*(1/subsetConductor p A)) = 0 := by
  have hM : (2:ℝ)^(Fintype.card ι) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hpoint (A : Finset ι) : primitiveCoefficient p q A*(1/subsetConductor p A) =
      q*baseRatio p/(2:ℝ)^(Fintype.card ι) -
        (q/zeroMass p)*(subsetMobius A/subsetConductor p A) := by
    have hd : subsetConductor p A ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp0 i)
    unfold primitiveCoefficient
    field_simp [hd, ha, hM]
    <;> ring
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, mobius_reciprocal_sum,
    ← zeroMass_mul_baseRatio p hp0 hp1]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_finset,
    Nat.cast_pow, Nat.cast_ofNat]
  field_simp [ha, hM]
  <;> ring

theorem derivativeProjection_expansion (p : ι → ℝ) (q : ℝ)
    (hp0 : ∀ i, p i ≠ 0) (hp1 : ∀ i, p i+1 ≠ 0)
    (ha : zeroMass p ≠ 0) (x : ι → Bool) :
    derivativeProjection p q x =
      ∑ A : Finset ι, primitiveCoefficient p q A*derivativeAtom p A x := by
  have hexpand : (∑ A : Finset ι, primitiveCoefficient p q A*derivativeAtom p A x) =
      (∑ A : Finset ι, primitiveCoefficient p q A*(1/subsetConductor p A)) -
      (q/(2:ℝ)^(Fintype.card ι)) *
        (baseRatio p*(∑ A : Finset ι, subsetConductor p A*finiteMonomial A x)) +
      (q/zeroMass p)*(∑ A : Finset ι, subsetMobius A*finiteMonomial A x) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro A _
    unfold primitiveCoefficient derivativeAtom subsetConductor
    ring
  rw [hexpand, coefficient_constant_sum p q hp0 hp1 ha,
    likelihood_monomial_expansion p hp1 x, mobius_monomial_expansion]
  unfold derivativeProjection
  ring

end RiemannResearch.RH.FinitePrimeDerivativeExpansion
