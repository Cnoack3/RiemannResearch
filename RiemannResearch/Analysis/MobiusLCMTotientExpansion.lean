/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualInghamMobiusCoefficients
import RiemannResearch.NumberTheory.PrimeNumberTheorem.CoprimeMobiusHarmonicMean
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

/-!
# Totient expansion of the finite signed Möbius lcm form at exponent one

This is the finite divisor rearrangement behind the coprime-sum method of
Ramaré and Zúñiga Alterman, *On a Möbius double sum*, arXiv:2603.25961.
The cutoff is the ordinary interval of integers, including its upper endpoint.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.InghamMollifier
open RiemannResearch.NumberTheory.PrimeNumberTheorem.FixedPrimeCylinder

private theorem moebius_mul_eq_rough {k : ℕ} (hk : 0 < k) (m : ℕ) :
    (ArithmeticFunction.moebius (k*m) : ℝ) =
      (ArithmeticFunction.moebius k : ℝ) * coefficient k.primeFactors m := by
  classical
  by_cases h : ∀ p ∈ k.primeFactors, ¬ p ∣ m
  · have hc : k.Coprime m := by
      by_contra hn
      obtain ⟨p,hp,hpk,hpm⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
      exact h p (Nat.mem_primeFactors.mpr ⟨hp,hpk,hk.ne'⟩) hpm
    rw [coefficient, if_pos h, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc]
    push_cast
    rfl
  · have hbad := h
    push Not at hbad
    obtain ⟨p,hpk,hpm⟩ := hbad
    obtain ⟨hp,hpd,_⟩ := Nat.mem_primeFactors.mp hpk
    have hsq : ¬ Squarefree (k*m) := fun hsf =>
      (Nat.squarefree_iff_prime_squarefree.mp hsf) p hp (Nat.mul_dvd_mul hpd hpm)
    rw [coefficient, if_neg h, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    simp

/-- Factoring out a divisor gives the reciprocal Möbius sum on the numbers
coprime to it, with the exact integer quotient cutoff. -/
theorem moebius_multiple_coordinate_eq_rough (X : ℕ) {k : ℕ} (hk : 0 < k) :
    (∑ d ∈ Finset.Icc 1 X, if k ∣ d then (ArithmeticFunction.moebius d : ℝ) / d else 0) =
      (ArithmeticFunction.moebius k : ℝ) / k * roughReciprocal k.primeFactors (X/k) := by
  classical
  induction X with
  | zero => simp [roughReciprocal]
  | succ X ih =>
    have hi : Finset.Icc 1 (X+1) = insert (X+1) (Finset.Icc 1 X) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hi, Finset.sum_insert (by simp), ih]
    by_cases hd : k ∣ X+1
    · have hdiv := Nat.succ_div_of_dvd hd
      have hX : X+1 = k * (X/k+1) := by rw [← hdiv, Nat.mul_div_cancel' hd]
      have hr : roughReciprocal k.primeFactors (X/k + 1) =
          roughReciprocal k.primeFactors (X/k) +
            coefficient k.primeFactors (X/k+1) / ((X/k+1 : ℕ) : ℝ) :=
        Finset.sum_range_succ _ _
      rw [if_pos hd, hdiv, hr, hX, moebius_mul_eq_rough hk, Nat.cast_mul]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    · rw [if_neg hd, Nat.succ_div_of_not_dvd hd, zero_add]

private theorem gcd_eq_sum_cutoff_totient {d e X : ℕ}
    (hd : d ∈ Finset.Icc 1 X) :
    (Nat.gcd d e : ℝ) =
      ∑ k ∈ Finset.Icc 1 X, if k ∣ d ∧ k ∣ e then (Nat.totient k : ℝ) else 0 := by
  classical
  obtain ⟨hd0,hdX⟩ := Finset.mem_Icc.mp hd
  have hg : 0 < Nat.gcd d e := Nat.gcd_pos_of_pos_left e hd0
  have hs : (Nat.gcd d e).divisors =
      (Finset.Icc 1 X).filter (fun k => k ∣ d ∧ k ∣ e) := by
    ext k
    constructor
    · intro hk
      have hk1 := Nat.pos_of_mem_divisors hk
      have hkd := (Nat.dvd_of_mem_divisors hk).trans (Nat.gcd_dvd_left d e)
      have hke := (Nat.dvd_of_mem_divisors hk).trans (Nat.gcd_dvd_right d e)
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨hk1,(Nat.le_of_dvd hd0 hkd).trans hdX⟩,hkd,hke⟩
    · intro hk
      obtain ⟨_, hkd,hke⟩ := Finset.mem_filter.mp hk
      exact Nat.mem_divisors.mpr ⟨Nat.dvd_gcd hkd hke,hg.ne'⟩
  calc
    _ = ∑ k ∈ (Nat.gcd d e).divisors, (Nat.totient k : ℝ) := by
      exact_mod_cast (Nat.sum_totient (Nat.gcd d e)).symm
    _ = _ := by rw [hs, Finset.sum_filter]

/-- The cutoff version of the gcd-kernel diagonalization, for arbitrary
real weights on the interval. -/
theorem gcd_cutoff_energy (X : ℕ) (a : ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 X, ∑ e ∈ Finset.Icc 1 X, a d * a e * (Nat.gcd d e : ℝ)) =
    ∑ k ∈ Finset.Icc 1 X, (Nat.totient k : ℝ) *
      (∑ d ∈ Finset.Icc 1 X, if k ∣ d then a d else 0)^2 := by
  classical
  calc
    _ = ∑ d ∈ Finset.Icc 1 X, ∑ e ∈ Finset.Icc 1 X, ∑ k ∈ Finset.Icc 1 X,
        (Nat.totient k : ℝ) * (if k ∣ d then a d else 0) * (if k ∣ e then a e else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      rw [gcd_eq_sum_cutoff_totient hd, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hkd : k ∣ d <;> by_cases hke : k ∣ e <;> simp [hkd,hke]
      ring
    _ = ∑ d ∈ Finset.Icc 1 X, ∑ k ∈ Finset.Icc 1 X, ∑ e ∈ Finset.Icc 1 X,
        (Nat.totient k : ℝ) * (if k ∣ d then a d else 0) * (if k ∣ e then a e else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact Finset.sum_comm
    _ = ∑ k ∈ Finset.Icc 1 X, ∑ d ∈ Finset.Icc 1 X, ∑ e ∈ Finset.Icc 1 X,
        (Nat.totient k : ℝ) * (if k ∣ d then a d else 0) * (if k ∣ e then a e else 0) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      rw [← Finset.mul_sum]
      ring

/-- The finite lcm form at exponent one with all its signs, expressed as the
sum of coprime Möbius squares. -/
theorem truncatedMobiusLCMForm_one_eq_roughReciprocal (X : ℕ) :
    truncatedMobiusLCMForm X 1 =
      ∑ k ∈ Finset.Icc 1 X, (Nat.totient k : ℝ) *
        ((ArithmeticFunction.moebius k : ℝ) / k * roughReciprocal k.primeFactors (X/k))^2 := by
  unfold truncatedMobiusLCMForm
  let a := fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) / n
  calc
    _ = ∑ d ∈ Finset.Icc 1 X, ∑ e ∈ Finset.Icc 1 X, a d * a e * (Nat.gcd d e : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
      have he0 : 0 < e := (Finset.mem_Icc.mp he).1
      have hl0 : (Nat.lcm d e : ℝ) ≠ 0 := by exact_mod_cast (Nat.lcm_pos hd0 he0).ne'
      have hm : (Nat.gcd d e : ℝ) * (Nat.lcm d e : ℝ) = d * e := by
        exact_mod_cast Nat.gcd_mul_lcm d e
      have hker : (Nat.gcd d e : ℝ) / ((d:ℝ)*e) = (Nat.lcm d e : ℝ)⁻¹ := by
        apply (div_eq_iff (mul_ne_zero (by exact_mod_cast hd0.ne') (by exact_mod_cast he0.ne'))).mpr
        rw [← hm]
        field_simp
      rw [Real.rpow_neg_one, ← hker]
      simp only [a, div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by
      rw [gcd_cutoff_energy]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← moebius_multiple_coordinate_eq_rough X (Finset.mem_Icc.mp hk).1]

/-- Totient and Möbius factors give the uniform harmonic majorant needed
to pass from a coprime reciprocal estimate to the unsigned outer sum. -/
theorem totient_rough_energy_le_harmonic (X : ℕ) (v : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 X, (Nat.totient k : ℝ) *
      ((ArithmeticFunction.moebius k : ℝ) / k * v k)^2) ≤
      ∑ k ∈ Finset.Icc 1 X, (v k)^2 / k := by
  apply Finset.sum_le_sum
  intro k hk
  have hk0 : (0:ℝ) < k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
  have hm : (ArithmeticFunction.moebius k : ℝ)^2 ≤ 1 := by
    rcases ArithmeticFunction.moebius_eq_or k with h | h | h <;> norm_num [h]
  have hf : (Nat.totient k : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.totient_le k
  have hh : (Nat.totient k : ℝ) * (ArithmeticFunction.moebius k : ℝ)^2 ≤ (k : ℝ) :=
    (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)).trans (by simpa using hf)
  calc
    _ = ((Nat.totient k : ℝ) * (ArithmeticFunction.moebius k : ℝ)^2) *
        ((v k)^2 / (k:ℝ)^2) := by ring
    _ ≤ (k:ℝ) * ((v k)^2 / (k:ℝ)^2) :=
      mul_le_mul_of_nonneg_right hh (div_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = _ := by field_simp

/-- One absolute constant bounds the signed Möbius lcm form at exponent one,
uniformly over all integer cutoffs. -/
theorem exists_truncatedMobiusLCMForm_one_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ X : ℕ, truncatedMobiusLCMForm X 1 ≤ K := by
  obtain ⟨K, hK, hb⟩ := exists_roughReciprocal_harmonic_prefix_bound
  refine ⟨K, hK, fun X => ?_⟩
  rw [truncatedMobiusLCMForm_one_eq_roughReciprocal]
  exact (totient_rough_energy_le_harmonic X
    (fun k => roughReciprocal k.primeFactors (X/k))).trans (hb X)

end RiemannResearch.Analysis.InghamMollifier
