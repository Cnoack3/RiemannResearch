/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Prefix square mean of the coprime Möbius weight

Expand the product of local factors by prime subsets and count multiples of
their squarefree products exactly. Dividing by each modulus bounds the
average by a finite Euler product with summable local increments.
The analytic application is the coprime Möbius estimate on Ingham's moving
right boundary.
-/

noncomputable section
open Finset
open scoped BigOperators

namespace RiemannResearch.NumberTheory.PrimeNumberTheorem.FixedPrimeCylinder

def coprimeMobiusWeight (k : ℕ) : ℝ :=
  ∏ p ∈ k.primeFactors, (1 - (Real.sqrt (p : ℝ))⁻¹)⁻¹

def coprimeMobiusIncrement (p : ℕ) : ℝ :=
  max 0 (((1 - (Real.sqrt (p : ℝ))⁻¹)⁻¹)^2 - 1)

private theorem local_increment_bounds {p : ℕ} (hp : 2 ≤ p) :
    1 + coprimeMobiusIncrement p = ((1 - (Real.sqrt (p : ℝ))⁻¹)⁻¹)^2 ∧
    coprimeMobiusIncrement p / (p : ℝ) ≤ 32 * (p : ℝ) ^ (-(3/2 : ℝ)) := by
  have hp2 : 2 ≤ (p : ℝ) := by exact_mod_cast hp
  have hpos : 0 < (p : ℝ) := by linarith
  have hs : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hpos
  have hroot : (4/3 : ℝ) ≤ Real.sqrt (p : ℝ) := by
    by_contra! hh
    have h := mul_self_lt_mul_self hs.le hh
    nlinarith [Real.sq_sqrt hpos.le]
  let r := (Real.sqrt (p : ℝ))⁻¹
  have hr : 0 ≤ r := inv_nonneg.mpr hs.le
  have hsmall : r ≤ 3/4 := by
    dsimp [r]
    rw [← one_div, div_le_iff₀ hs]
    linarith
  have hg : 0 < 1-r := by linarith
  have hid : ((1-r)⁻¹)^2 - 1 = (2*r-r^2)/(1-r)^2 := by
    field_simp [hg.ne']
    ring
  have hnum : 0 ≤ 2*r-r^2 := by
    nlinarith only [mul_nonneg hr (show 0 ≤ 2-r by linarith)]
  have hinc : coprimeMobiusIncrement p = (2*r-r^2)/(1-r)^2 := by
    change max 0 (((1-r)⁻¹)^2-1) = _
    rw [hid, max_eq_right (div_nonneg hnum (sq_nonneg _))]
  constructor
  · rw [hinc, ← hid]
    dsimp [r]
    ring
  have hden : (1/16 : ℝ) ≤ (1-r)^2 := by nlinarith [sq_nonneg (3/4-r)]
  have hbound : coprimeMobiusIncrement p ≤ 32*r := by
    rw [hinc, div_le_iff₀ (sq_pos_of_pos hg)]
    nlinarith only [mul_le_mul_of_nonneg_right hden (show 0 ≤ 32*r by positivity),
      sq_nonneg r]
  have hpow : r / (p:ℝ) = (p : ℝ) ^ (-(3/2 : ℝ)) := by
    rw [show r = (p:ℝ)^(-(1/2 : ℝ)) by rw [Real.rpow_neg hpos.le, ← Real.sqrt_eq_rpow]]
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hpos]
    norm_num
  calc
    _ ≤ (32*r)/(p:ℝ) := div_le_div_of_nonneg_right hbound hpos.le
    _ = _ := by rw [← hpow]; ring

/-- Exact prefix formula; the multiplicity of a prime subset is the
integer quotient by its squarefree product. This includes Y=0. -/
theorem coprimeMobiusWeight_sq_prefix_eq (Y : ℕ) :
    ∑ k ∈ Icc 1 Y, coprimeMobiusWeight k ^ 2 =
      ∑ S ∈ ((Icc 2 Y).filter Nat.Prime).powerset,
        ((Y / (∏ p ∈ S, p) : ℕ) : ℝ) * ∏ p ∈ S, coprimeMobiusIncrement p := by
  classical
  let P := (Icc 2 Y).filter Nat.Prime
  let D := fun S : Finset ℕ => ∏ p ∈ S, p
  let W := fun S : Finset ℕ => ∏ p ∈ S, coprimeMobiusIncrement p
  have expand (k : ℕ) (hk : k ∈ Icc 1 Y) :
      coprimeMobiusWeight k ^ 2 = ∑ S ∈ P.powerset, if D S ∣ k then W S else 0 := by
    have hkn : k ≠ 0 := by have := (mem_Icc.mp hk).1; omega
    have hsub : k.primeFactors ⊆ P := by
      intro p hp
      have hpr := Nat.prime_of_mem_primeFactors hp
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hpr.two_le,
        (Nat.le_of_mem_primeFactors hp).trans (mem_Icc.mp hk).2⟩, hpr⟩
    have hfilt : P.powerset.filter (fun S => D S ∣ k) = k.primeFactors.powerset := by
      ext S
      simp only [mem_filter, mem_powerset]
      constructor
      · rintro ⟨hS, hd⟩ p hp
        apply Nat.mem_primeFactors.mpr
        exact ⟨(mem_filter.mp (hS hp)).2, (Finset.dvd_prod_of_mem (fun i => i) hp).trans hd,
          hkn⟩
      · intro hS
        exact ⟨hS.trans hsub,
          (Finset.prod_dvd_prod_of_subset S _ id hS).trans k.prod_primeFactors_dvd⟩
    rw [← Finset.sum_filter, hfilt]
    unfold W
    rw [← Finset.prod_one_add]
    unfold coprimeMobiusWeight
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro p hp
    exact (local_increment_bounds (Nat.prime_of_mem_primeFactors hp).two_le).1.symm
  have hI : Icc 1 Y = Ioc 0 Y := Finset.Icc_succ_left_eq_Ioc 0 Y
  calc
    _ = ∑ k ∈ Icc 1 Y, ∑ S ∈ P.powerset, if D S ∣ k then W S else 0 :=
      Finset.sum_congr rfl expand
    _ = ∑ S ∈ P.powerset, ∑ k ∈ Icc 1 Y, if D S ∣ k then W S else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hI,
        Nat.Ioc_filter_dvd_card_eq_div]

/-- The finite Euler-product upper bound following the exact integer count. -/
theorem coprimeMobiusWeight_sq_prefix_le_product (Y : ℕ) :
    ∑ k ∈ Icc 1 Y, coprimeMobiusWeight k ^ 2 ≤
      (Y : ℝ) * ∏ p ∈ (Icc 2 Y).filter Nat.Prime, (1 + coprimeMobiusIncrement p / p) := by
  classical
  rw [coprimeMobiusWeight_sq_prefix_eq, Finset.prod_one_add, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S hS
  have hW : 0 ≤ ∏ p ∈ S, coprimeMobiusIncrement p :=
    Finset.prod_nonneg (fun p _ => le_max_left _ _)
  calc
    _ ≤ ((Y : ℝ) / ((∏ p ∈ S, p : ℕ) : ℝ)) * ∏ p ∈ S, coprimeMobiusIncrement p :=
      mul_le_mul_of_nonneg_right Nat.cast_div_le hW
    _ = (Y : ℝ) * ∏ p ∈ S, (coprimeMobiusIncrement p / (p:ℝ)) := by
      rw [Finset.prod_div_distrib, Nat.cast_prod]
      ring

/-- Uniform square mean of the coprime Möbius weight over initial intervals. -/
theorem exists_coprimeMobiusWeight_sq_prefix_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℕ,
      ∑ k ∈ Icc 1 Y, coprimeMobiusWeight k ^ 2 ≤ C * Y := by
  classical
  let f := fun p : ℕ => (p : ℝ) ^ (-(3/2 : ℝ))
  have hs : Summable f := Real.summable_nat_rpow.mpr (by norm_num)
  refine ⟨Real.exp (32 * ∑' k, f k), Real.exp_pos _, ?_⟩
  intro Y
  let P := (Icc 2 Y).filter Nat.Prime
  have hsum : ∑ p ∈ P, coprimeMobiusIncrement p / (p : ℝ) ≤ 32 * ∑' k, f k := by
    calc
      _ ≤ ∑ p ∈ P, 32 * f p := Finset.sum_le_sum (fun p hp =>
        (local_increment_bounds (mem_Icc.mp (mem_filter.mp hp).1).1).2)
      _ = 32 * ∑ p ∈ P, f p := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hs.sum_le_tsum P (fun p _ => by dsimp [f]; positivity))
        (by norm_num)
  have heuler : ∏ p ∈ P, (1 + coprimeMobiusIncrement p / (p : ℝ)) ≤
      Real.exp (32 * ∑' k, f k) := by
    calc
      _ ≤ ∏ p ∈ P, Real.exp (coprimeMobiusIncrement p / p) :=
        Finset.prod_le_prod (f := fun p : ℕ => 1 + coprimeMobiusIncrement p / p)
          (fun p _ => add_nonneg zero_le_one
            (div_nonneg (show 0 ≤ coprimeMobiusIncrement p from le_max_left _ _) (Nat.cast_nonneg _)))
          (fun p _ => (add_comm 1 (coprimeMobiusIncrement p / p)).le.trans (Real.add_one_le_exp _))
      _ = Real.exp (∑ p ∈ P, coprimeMobiusIncrement p / (p : ℝ)) := (Real.exp_sum _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hsum
  exact (coprimeMobiusWeight_sq_prefix_le_product Y).trans
    ((mul_le_mul_of_nonneg_left heuler (Nat.cast_nonneg Y)).trans_eq (mul_comm _ _))

end RiemannResearch.NumberTheory.PrimeNumberTheorem.FixedPrimeCylinder
