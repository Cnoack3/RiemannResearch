/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact Euler correction from prime-phase discrepancies

This module proves the power discrepancy, the prime-power convolution and
its generating series, and a sharp local Euler-factor perturbation estimate.
The finite identity retains the full signed remainder. These are the local
inputs for comparing primewise zero-ordinate assignments with the constant
prime targets +1 (zeta) and -1 (Liouville).

Source: user-provided primewise-ordinate proposal; elementary algebra and
geometric-series derivations developed in this session. No novelty claim.
The global selection of actual zero ordinates and the normal convergence of
an infinite product over primes remain paper-level arguments in the companion
research note, not hypotheses silently discharged by these lemmas.
-/

open scoped BigOperators

namespace RiemannResearch.Analysis.PrimePhasePerturbation

theorem norm_pow_sub_pow_le (a b : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (k : ℕ) : ‖a ^ k - b ^ k‖ ≤ (k : ℝ) * ‖a - b‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      ‖a ^ (k + 1) - b ^ (k + 1)‖ =
          ‖a * (a ^ k - b ^ k) + (a - b) * b ^ k‖ := by
            congr 1
            simp only [pow_succ]
            ring
      _ ≤ ‖a ^ k - b ^ k‖ + ‖a - b‖ := by
        simpa only [norm_mul, norm_pow, ha, hb, one_pow, one_mul, mul_one] using
          norm_add_le (a * (a ^ k - b ^ k)) ((a - b) * b ^ k)
      _ ≤ (k : ℝ) * ‖a - b‖ + ‖a - b‖ := add_le_add ih le_rfl
      _ = ((k + 1 : ℕ) : ℝ) * ‖a - b‖ := by
        simp only [Nat.cast_add, Nat.cast_one]
        ring

/-- Prime-power logarithmic coefficients inherit the prime discrepancy,
without a loss depending on the harmonic number. -/
theorem norm_logPrimePowerDifference_le (a b : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (k : ℕ) :
    ‖(a ^ (k + 1) - b ^ (k + 1)) / ((k + 1 : ℕ) : ℂ)‖ ≤ ‖a - b‖ := by
  have hnorm : ‖((k + 1 : ℕ) : ℂ)‖ = ((k + 1 : ℕ) : ℝ) := by
    change ‖(((k + 1 : ℕ) : ℝ) : ℂ)‖ = ((k + 1 : ℕ) : ℝ)
    exact Complex.norm_of_nonneg (Nat.cast_nonneg _)
  have hpos : 0 < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
  rw [norm_div, hnorm, div_le_iff₀ hpos]
  simpa only [mul_comm] using norm_pow_sub_pow_le a b ha hb (k + 1)

def primePowerCorrection (a b : ℂ) : ℕ → ℂ
  | 0 => 1
  | k + 1 => (a - b) * a ^ k

@[simp] theorem primePowerCorrection_zero (a b : ℂ) :
    primePowerCorrection a b 0 = 1 := rfl

@[simp] theorem primePowerCorrection_succ (a b : ℂ) (k : ℕ) :
    primePowerCorrection a b (k + 1) = (a - b) * a ^ k := rfl

theorem primePowerCorrection_recurrence (a b : ℂ) (k : ℕ) :
    b * a ^ k + primePowerCorrection a b (k + 1) = a ^ (k + 1) := by
  rw [primePowerCorrection_succ, pow_succ]
  ring

theorem primePowerCorrection_convolution (a b : ℂ) (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), b ^ (k - j) * primePowerCorrection a b j) =
      a ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      (∑ j ∈ Finset.range (k + 1 + 1),
          b ^ (k + 1 - j) * primePowerCorrection a b j) =
          (∑ j ∈ Finset.range (k + 1),
            b ^ (k + 1 - j) * primePowerCorrection a b j) +
              primePowerCorrection a b (k + 1) := by
                rw [Finset.sum_range_succ]
                simp
      _ = b * (∑ j ∈ Finset.range (k + 1),
            b ^ (k - j) * primePowerCorrection a b j) +
              primePowerCorrection a b (k + 1) := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hsub : k + 1 - j = (k - j) + 1 := by omega
        rw [hsub, pow_succ]
        ring
      _ = a ^ (k + 1) := by
        rw [ih]
        exact primePowerCorrection_recurrence a b k

theorem norm_primePowerCorrection_succ (a b : ℂ) (ha : ‖a‖ = 1) (k : ℕ) :
    ‖primePowerCorrection a b (k + 1)‖ = ‖a - b‖ := by
  simp [primePowerCorrection, norm_pow, ha]

theorem localEulerCorrection_truncation (a b z : ℂ) (N : ℕ) :
    (1 - a * z) *
      (1 + ∑ k ∈ Finset.range N, (a - b) * a ^ k * z ^ (k + 1)) =
        1 - b * z - (a - b) * a ^ N * z ^ (N + 1) := by
  induction N with
  | zero => simp; ring
  | succ N ih =>
    rw [Finset.sum_range_succ]
    calc
      (1 - a * z) *
          (1 + ((∑ k ∈ Finset.range N, (a - b) * a ^ k * z ^ (k + 1)) +
            (a - b) * a ^ N * z ^ (N + 1))) =
          (1 - a * z) *
            (1 + ∑ k ∈ Finset.range N, (a - b) * a ^ k * z ^ (k + 1)) +
          (1 - a * z) * ((a - b) * a ^ N * z ^ (N + 1)) := by ring
      _ = _ := by
        rw [ih]
        simp only [pow_succ]
        ring

theorem localEulerCorrection_sub_one (a b z : ℂ) (hz : 1 - a * z ≠ 0) :
    (1 - b * z) / (1 - a * z) - 1 = (a - b) * z / (1 - a * z) := by
  rw [div_sub_one hz]
  congr 1
  ring

theorem localEulerDenominator_ne_zero (a z : ℂ) (ha : ‖a‖ = 1) (hz : ‖z‖ < 1) :
    1 - a * z ≠ 0 := by
  have hden : 1 - ‖z‖ ≤ ‖1 - a * z‖ := by
    simpa only [norm_one, norm_mul, ha, one_mul] using
      norm_sub_norm_le (1 : ℂ) (a * z)
  intro h
  rw [h, norm_zero] at hden
  linarith

theorem norm_localEulerCorrection_sub_one_le (a b z : ℂ)
    (ha : ‖a‖ = 1) (hz : ‖z‖ < 1) :
    ‖(1 - b * z) / (1 - a * z) - 1‖ ≤
      ‖a - b‖ * ‖z‖ / (1 - ‖z‖) := by
  have hden : 1 - ‖z‖ ≤ ‖1 - a * z‖ := by
    simpa only [norm_one, norm_mul, ha, one_mul] using
      norm_sub_norm_le (1 : ℂ) (a * z)
  rw [localEulerCorrection_sub_one a b z (localEulerDenominator_ne_zero a z ha hz),
    norm_div, norm_mul]
  exact div_le_div_of_nonneg_left
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (sub_pos.mpr hz) hden

theorem finiteEulerCorrection_eq_ratio {ι : Type*} (S : Finset ι)
    (a b z : ι → ℂ) :
    (∏ p ∈ S, (1 - b p * z p) / (1 - a p * z p)) =
      (∏ p ∈ S, (1 - b p * z p)) / (∏ p ∈ S, (1 - a p * z p)) := by
  simp only [Finset.prod_div_distrib]


theorem hasSum_localEulerCorrection_tail (a b z : ℂ)
    (ha : ‖a‖ = 1) (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => (a - b) * a ^ k * z ^ (k + 1))
      ((a - b) * z / (1 - a * z)) := by
  have haz : ‖a * z‖ < 1 := by
    simpa only [norm_mul, ha, one_mul] using hz
  have hs := (hasSum_geometric_of_norm_lt_one haz).mul_left ((a - b) * z)
  have hpoint : (fun k : ℕ => ((a - b) * z) * (a * z) ^ k) =
      (fun k : ℕ => (a - b) * a ^ k * z ^ (k + 1)) := by
    funext k
    rw [mul_pow, pow_succ]
    ring
  rw [hpoint] at hs
  simpa only [div_eq_mul_inv] using hs

theorem one_add_tsum_localEulerCorrection_tail (a b z : ℂ)
    (ha : ‖a‖ = 1) (hz : ‖z‖ < 1) :
    1 + (∑' k : ℕ, (a - b) * a ^ k * z ^ (k + 1)) =
      (1 - b * z) / (1 - a * z) := by
  rw [(hasSum_localEulerCorrection_tail a b z ha hz).tsum_eq]
  rw [← localEulerCorrection_sub_one a b z
    (localEulerDenominator_ne_zero a z ha hz)]
  ring

theorem hasSum_primePowerCorrection (a b z : ℂ)
    (ha : ‖a‖ = 1) (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => primePowerCorrection a b k * z ^ k)
      ((1 - b * z) / (1 - a * z)) := by
  have hs : HasSum
      (fun k : ℕ => primePowerCorrection a b (k + 1) * z ^ (k + 1))
      ((1 - b * z) / (1 - a * z) - 1) := by
    rw [localEulerCorrection_sub_one a b z
      (localEulerDenominator_ne_zero a z ha hz)]
    simpa only [primePowerCorrection_succ] using
      hasSum_localEulerCorrection_tail a b z ha hz
  have h := (hasSum_nat_add_iff
    (f := fun k : ℕ => primePowerCorrection a b k * z ^ k) 1).mp hs
  simpa using h

end RiemannResearch.Analysis.PrimePhasePerturbation
