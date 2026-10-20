/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimePowerSieve
import RiemannResearch.RH.QMellinTransfer
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Exact Mellin Euler factors of actual squarefree prime-power sieves

Source: user-provided argument, TwoStageSieveObstructionResearch20261020.md,
Section 3. This module proves the finite transform for the actual complete-Q
vectors and retains every divisor coefficient. Infinite decay is developed
separately; no closure or RH assumption is used here.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QPrimePowerSieve
open ZetaTwoHilbert QMellinTransfer

/-- Reindex the actual incidence coefficients, retaining all divisors. -/
theorem sieveCoefficient_sum_reindex (L p : ℕ) (hp : p ∈ L.divisors)
    (f : ℕ → ℝ) :
    (∑ d ∈ L.divisors, sieveCoefficient L p d * f d) =
      ∑ e ∈ (L / p).divisors, (ArithmeticFunction.moebius e : ℝ) * f (p * e) := by
  classical
  have hp0 := Nat.pos_of_mem_divisors hp
  have hpL := Nat.dvd_of_mem_divisors hp
  have hL0 := (Nat.mem_divisors.mp hp).2
  have hs : (∑ d ∈ L.divisors, sieveCoefficient L p d * f d) =
      ∑ d ∈ L.divisors.filter (fun d => p ∣ d),
        (ArithmeticFunction.moebius (d / p) : ℝ) * f d := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    rw [sieveCoefficient_eq L p d hp]
    split_ifs <;> simp
  rw [hs]
  symm
  apply Finset.sum_bij (fun e _ => p * e)
  · intro e he
    have hed : p * e ∣ L := by
      rw [← Nat.mul_div_cancel' hpL]
      exact Nat.mul_dvd_mul_left p (Nat.dvd_of_mem_divisors he)
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨hed, hL0⟩, dvd_mul_right p e⟩
  · intro e he k hk hek
    exact Nat.eq_of_mul_eq_mul_left hp0 hek
  · intro d hd
    obtain ⟨hdL, hpd⟩ := Finset.mem_filter.mp hd
    refine ⟨d / p, Nat.mem_divisors.mpr ⟨?_, ?_⟩, Nat.mul_div_cancel' hpd⟩
    · exact Nat.div_dvd_div hpd (Nat.dvd_of_mem_divisors hdL)
    · exact Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hL0) hpL) hp0)
  · intro e he
    rw [Nat.mul_div_cancel_left e hp0]

def inversePowerArithmetic (σ : ℝ) (hσ : σ ≠ 0) : ArithmeticFunction ℝ where
  toFun n := (n : ℝ) ^ (-σ)
  map_zero' := by simp [Real.zero_rpow (neg_ne_zero.mpr hσ)]

theorem inversePowerArithmetic_multiplicative (σ : ℝ) (hσ : σ ≠ 0) :
    (inversePowerArithmetic σ hσ).IsMultiplicative := by
  constructor
  · simp [inversePowerArithmetic]
  · intro m n hcop
    change ((m * n : ℕ) : ℝ) ^ (-σ) = (m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ)
    rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]

/-- Exact finite Euler factor of the actual prime-power sieve. -/
theorem sieveCoefficient_rpow_sum (L p : ℕ) (hp : p ∈ L.divisors)
    (hsf : Squarefree L) (σ : ℝ) (hσ : σ ≠ 0) :
    (∑ d ∈ L.divisors, sieveCoefficient L p d * (d : ℝ) ^ (-σ)) =
      (p : ℝ) ^ (-σ) *
        ∏ q ∈ (L / p).primeFactors, (1 - (q : ℝ) ^ (-σ)) := by
  rw [sieveCoefficient_sum_reindex L p hp]
  have hsf' : Squarefree (L / p) :=
    hsf.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hp))
  have he := ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
    (inversePowerArithmetic σ hσ) (inversePowerArithmetic_multiplicative σ hσ) hsf'
  change (∏ q ∈ (L / p).primeFactors, (1 - (q : ℝ) ^ (-σ))) =
    ∑ e ∈ (L / p).divisors, (ArithmeticFunction.moebius e : ℝ) * (e : ℝ) ^ (-σ) at he
  rw [he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg p) (Nat.cast_nonneg e)]
  ring

/-- Normalized Mellin transform of the actual finite vector before any Euler simplification. -/
theorem sieveVector_mellin_divisor_exact (L p : ℕ) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) :
    s * qMellin (sieveVector L p) s = riemannZeta s *
      ((∑ d ∈ L.divisors, (sieveCoefficient L p d : ℂ) * (d : ℂ) ^ (-s)) -
        (sieveSlope L p : ℂ)) := by
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hd (d : ℕ) (hd : d ∈ L.divisors) :
      qMellin (qResidue d) s =
        riemannZeta s / s * ((1 / (d : ℂ)) - (d : ℂ) ^ (-s)) :=
    qMellin_residue_zeta d (Nat.pos_of_mem_divisors hd) s (by linarith) hs1
  have hm : qMellin (sieveVector L p) s =
      -(∑ d ∈ L.divisors, (sieveCoefficient L p d : ℂ) * qMellin (qResidue d) s) := by
    change qMellinContinuous s hs (-(∑ d ∈ L.divisors,
      sieveCoefficient L p d • qResidue d)) = _
    simp only [map_neg, map_sum, map_smul, qMellinContinuous_apply, Complex.real_smul]
  rw [hm]
  have hc : (sieveSlope L p : ℂ) =
      ∑ d ∈ L.divisors, (sieveCoefficient L p d : ℂ) / (d : ℂ) := by
    simp [sieveSlope]
  rw [hc, ← Finset.sum_sub_distrib, Finset.mul_sum, mul_neg, Finset.mul_sum,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro d hdm
  rw [hd d hdm]
  field_simp [hs0]
  ring

/-- Complete actual Euler-product Mellin formula for every squarefree period. -/
theorem sieveVector_mellin_euler_exact (L p : ℕ) (hp : p ∈ L.divisors)
    (hsf : Squarefree L) (σ : ℝ) (hσ : (1 / 2 : ℝ) < σ) (hσ1 : σ ≠ 1) :
    (σ : ℂ) * qMellin (sieveVector L p) σ = riemannZeta σ *
      (((p : ℝ) ^ (-σ) *
        ∏ q ∈ (L / p).primeFactors, (1 - (q : ℝ) ^ (-σ)) - sieveSlope L p : ℝ) : ℂ) := by
  rw [sieveVector_mellin_divisor_exact L p σ (by simpa using hσ)
    (by exact_mod_cast hσ1)]
  congr 1
  rw [Complex.ofReal_sub, ← sieveCoefficient_rpow_sum L p hp hsf σ (by linarith)]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  rw [Complex.ofReal_cpow (Nat.cast_nonneg d)]
  simp

end RiemannResearch.RH.QPrimePowerSieve
