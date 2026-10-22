/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QDivisorDilationCoefficients
import RiemannResearch.RH.QDivisorHilbertBasis
import RiemannResearch.RH.QDivisorWaveletFactorization
import RiemannResearch.RH.QDivisorWaveletOverlap
import RiemannResearch.RH.QDivisibilityHilbertMoments
import RiemannResearch.RH.QDilationMoments
import RiemannResearch.RH.QPrimePowerCofactorExpansion
import RiemannResearch.RH.QPrimePowerCofactorResidual
import RiemannResearch.RH.QPrimePowerHilbertFrame
import RiemannResearch.RH.QPrimePowerMixedCoefficients
import RiemannResearch.RH.QPrimePowerOrthogonal
import RiemannResearch.RH.QPrimePowerWaveletCoefficients
import RiemannResearch.RH.QResidueMoments
import RiemannResearch.RH.PrimePowerTargetMellin
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Arithmetic coprime-conductor coefficients of floor-log targets

Source: user-provided research action, 22 October 2026, following the
complete ambient expansion in QPrimePowerCofactorExpansion.
Finite Moebius differences of dilated logarithmic means give every
coefficient; prime-power conductors give adjacent mean differences.
Summability and exact head-tail identities retain all physical integers.
The elementary two-adjacent-value logarithm bounds yield coefficient bounds.

The concrete cofactor-energy bounds 1/8 for F_2 and 1/24 for F_3 improve
the previous two-coordinate ambient residual bounds. They are not lower
bounds for distance to the legal closure. Neither target membership,
legal Parseval saturation, nor RH is assumed or proved.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace RiemannResearch.RH.PrimePowerTarget
open ZetaTwoHilbert ZetaTwoProbability QDivisibilityDensity QDivisorHilbert

/-- Complete inverse-square expectation of the dilated floor logarithm. -/
def dilatedTargetMean (p d : ℕ) : ℝ :=
  inversePowerMean 0 (fun n => (Nat.log p (d * n) : ℝ))

theorem qTarget_scaled_divisor_mean (p d : ℕ) (hp : 1 < p) (hd : 0 < d) :
    (d : ℝ) ^ 2 * inner ℝ (qTarget p hp) (qDivisor d) = dilatedTargetMean p d := by
  rw [inner_qDivisor_eq_dilation _ d hd]
  simp only [qTarget_sequence, dilatedTargetMean]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  field_simp

/-- Every conductor coefficient is an exact finite signed Moebius difference. -/
theorem qTarget_inner_basis_moebius (p : ℕ) (hp : 1 < p) (t : ℕ+) :
    inner ℝ (qTarget p hp) (normalizedDivisorWavelet t) =
      (∑ d ∈ (t : ℕ).divisors, (ArithmeticFunction.moebius ((t : ℕ) / d) : ℝ) *
        dilatedTargetMean p d) / Real.sqrt (qJordanTwo (t : ℕ)) := by
  simpa only [qTarget_sequence, dilatedTargetMean] using
    normalizedDivisorWavelet_inner_dilation (qTarget p hp) t

theorem dilatedTargetMean_one (p : ℕ) (hp : 1 < p) :
    dilatedTargetMean p 1 = inner ℝ (qTarget p hp) qOne := by
  rw [qInner_eq_inversePowerMean, qTarget_sequence, qSequence_qOne]
  unfold dilatedTargetMean inversePowerMean
  apply tsum_congr
  intro n
  simp [qOneSequence]

theorem dilatedTargetMean_mul_power (p k d : ℕ) (hp : 1 < p) (hd : 0 < d) :
    dilatedTargetMean p (p ^ k * d) = dilatedTargetMean p d + k := by
  have h := qTarget_scaled_primePower_divisor p k d hp hd
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hleft := qTarget_scaled_divisor_mean p (p ^ k * d) hp
    (mul_pos (pow_pos (by omega) _) hd)
  have hright := qTarget_scaled_divisor_mean p d hp hd
  rw [Nat.cast_mul, Nat.cast_pow, mul_pow] at hleft
  rw [← hleft, ← hright]
  calc
    _ = (d : ℝ) ^ 2 * (((p : ℝ) ^ k) ^ 2 *
        inner ℝ (qTarget p hp) (qDivisor (p ^ k * d))) := by ring
    _ = _ := by rw [h]; field_simp

theorem qTarget_inner_primePower_mean_difference (p q k : ℕ)
    (hp : 1 < p) (hq : q.Prime) :
    inner ℝ (qTarget p hp)
      (normalizedDivisorWavelet ⟨q ^ (k + 1), pow_pos hq.pos _⟩) =
      (dilatedTargetMean p (q ^ (k + 1)) - dilatedTargetMean p (q ^ k)) /
        Real.sqrt (qJordanTwo (q ^ (k + 1))) := by
  change inner ℝ (qTarget p hp)
    ((Real.sqrt (qJordanTwo (q ^ (k + 1))))⁻¹ • divisorWavelet (q ^ (k + 1))) = _
  rw [real_inner_smul_right, divisorWavelet_prime_pow_succ q k hq,
    inner_sub_right, real_inner_smul_right, real_inner_smul_right]
  have h1 := qTarget_scaled_divisor_mean p (q ^ (k + 1)) hp (pow_pos hq.pos _)
  have h0 := qTarget_scaled_divisor_mean p (q ^ k) hp (pow_pos hq.pos _)
  simp only [Nat.cast_pow] at h1 h0
  rw [h1, h0]
  ring


theorem log_mul_bounds (p d n : ℕ) (hp : 1 < p) (hd : 0 < d) (hn : n ≠ 0) :
    Nat.log p d + Nat.log p n ≤ Nat.log p (d * n) ∧
      Nat.log p (d * n) ≤ Nat.log p d + Nat.log p n + 1 := by
  have hlo := Nat.log_mono_right (b := p) (Nat.mul_le_mul_right n
    (Nat.pow_log_le_self p (Nat.ne_of_gt hd)))
  have hhi := Nat.log_mono_right (b := p) (Nat.mul_le_mul_right n
    (Nat.lt_pow_succ_log_self hp d).le)
  rw [log_mul_power p (Nat.log p d) n hp hn] at hlo
  rw [log_mul_power p (Nat.log p d + 1) n hp hn] at hhi
  constructor <;> omega


theorem dilatedTargetMean_summable (p d : ℕ) (hp : 1 < p) (hd : 0 < d) :
    Summable (fun n : ℕ => positiveQWeight n * (Nat.log p (d * n) : ℝ)) := by
  have hi : Function.Injective (fun n : ℕ => d * n) :=
    fun _ _ h => Nat.mul_left_cancel hd h
  have hs := (qSequence_product_summable (qTarget p hp) qOne).comp_injective hi
  have hs' : Summable (fun n : ℕ =>
      positiveQWeight (d * n) * (Nat.log p (d * n) : ℝ)) := by
    apply hs.congr
    intro n
    change positiveQWeight (d * n) * qSequence (qTarget p hp) (d * n) *
      qSequence qOne (d * n) = _
    rw [qTarget_sequence, qSequence_qOne]
    by_cases hn : n = 0
    · simp [hn]
    · simp [qOneSequence, mul_ne_zero (Nat.ne_of_gt hd) hn]
  have hsm := hs'.mul_left ((d : ℝ) ^ 2)
  apply hsm.congr
  intro n
  rw [positiveQWeight_mul]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  field_simp

theorem dilatedTargetMean_weighted (p d : ℕ) (hp : 1 < p) (hd : 0 < d) :
    dilatedTargetMean p d =
      ∑' n : ℕ, positiveQWeight n * (Nat.log p (d * n) : ℝ) := by
  have hs := dilatedTargetMean_summable p d hp hd
  rw [hs.tsum_eq_zero_add]
  simp only [mul_zero, Nat.log_zero_right, Nat.cast_zero, mul_zero, zero_add]
  unfold dilatedTargetMean inversePowerMean
  apply tsum_congr
  intro n
  unfold positiveQWeight
  ring

/-- A finite physical head plus the literal infinite physical tail. -/
theorem dilatedTargetMean_head_tail (p d N : ℕ) (hp : 1 < p) (hd : 0 < d) :
    dilatedTargetMean p d =
      (∑ n ∈ Finset.range N, positiveQWeight n * (Nat.log p (d * n) : ℝ)) +
      ∑' k : ℕ, positiveQWeight (k + N) * (Nat.log p (d * (k + N)) : ℝ) := by
  rw [dilatedTargetMean_weighted p d hp hd]
  exact (Summable.sum_add_tsum_nat_add N (dilatedTargetMean_summable p d hp hd)).symm


theorem dilatedTargetMean_mul_bounds (p q d : ℕ) (hp : 1 < p)
    (hq : 0 < q) (hd : 0 < d) :
    (Nat.log p q : ℝ) ≤ dilatedTargetMean p (q * d) - dilatedTargetMean p d ∧
      dilatedTargetMean p (q * d) - dilatedTargetMean p d ≤ (Nat.log p q : ℝ) + 1 := by
  let delta := fun n : ℕ => (Nat.log p ((q * d) * n) : ℝ) - (Nat.log p (d * n) : ℝ)
  have hs0 := dilatedTargetMean_summable p d hp hd
  have hs1 := dilatedTargetMean_summable p (q * d) hp (mul_pos hq hd)
  have hs : Summable (fun n => positiveQWeight n * delta n) := by
    apply (hs1.sub hs0).congr
    intro n
    dsimp [delta]
    ring
  have he : dilatedTargetMean p (q * d) - dilatedTargetMean p d =
      ∑' n, positiveQWeight n * delta n := by
    rw [dilatedTargetMean_weighted p (q * d) hp (mul_pos hq hd),
      dilatedTargetMean_weighted p d hp hd, ← hs1.tsum_sub hs0]
    apply tsum_congr
    intro n
    dsimp [delta]
    ring
  have hlo (n : ℕ) : positiveQWeight n * (Nat.log p q : ℝ) ≤
      positiveQWeight n * delta n := by
    by_cases hn : n = 0
    · simp [hn, positiveQWeight]
    · have hb := (log_mul_bounds p q (d * n) hp hq
        (mul_ne_zero (Nat.ne_of_gt hd) hn)).1
      have hbR : (Nat.log p q : ℝ) ≤ delta n := by
        change (Nat.log p q : ℝ) ≤
          (Nat.log p ((q * d) * n) : ℝ) - (Nat.log p (d * n) : ℝ)
        rw [mul_assoc]
        have hb' : (Nat.log p q : ℝ) + (Nat.log p (d * n) : ℝ) ≤
            (Nat.log p (q * (d * n)) : ℝ) := by exact_mod_cast hb
        linarith
      exact mul_le_mul_of_nonneg_left hbR (positiveQWeight_nonneg n)
  have hhi (n : ℕ) : positiveQWeight n * delta n ≤
      positiveQWeight n * ((Nat.log p q : ℝ) + 1) := by
    by_cases hn : n = 0
    · simp [hn, positiveQWeight]
    · have hb := (log_mul_bounds p q (d * n) hp hq
        (mul_ne_zero (Nat.ne_of_gt hd) hn)).2
      have hbR : delta n ≤ (Nat.log p q : ℝ) + 1 := by
        change (Nat.log p ((q * d) * n) : ℝ) - (Nat.log p (d * n) : ℝ) ≤
          (Nat.log p q : ℝ) + 1
        rw [mul_assoc]
        have hb' : (Nat.log p (q * (d * n)) : ℝ) ≤
            (Nat.log p q : ℝ) + (Nat.log p (d * n) : ℝ) + 1 := by exact_mod_cast hb
        linarith
      exact mul_le_mul_of_nonneg_left hbR (positiveQWeight_nonneg n)
  rw [he]
  have hl := Summable.tsum_le_tsum hlo
    (positiveQWeight_summable.mul_right (Nat.log p q : ℝ)) hs
  have hh := Summable.tsum_le_tsum hhi hs
    (positiveQWeight_summable.mul_right ((Nat.log p q : ℝ) + 1))
  simp only [tsum_mul_right, positiveQWeight_tsum, one_mul] at hl hh
  exact ⟨hl, hh⟩

/-- Bounds from the two possible values of the multiplicative floor-log increment. -/
theorem qTarget_inner_primePower_bounds (p q k : ℕ) (hp : 1 < p) (hq : q.Prime) :
    (Nat.log p q : ℝ) / Real.sqrt (qJordanTwo (q ^ (k + 1))) ≤
      inner ℝ (qTarget p hp)
        (normalizedDivisorWavelet ⟨q ^ (k + 1), pow_pos hq.pos _⟩) ∧
      inner ℝ (qTarget p hp)
        (normalizedDivisorWavelet ⟨q ^ (k + 1), pow_pos hq.pos _⟩) ≤
      ((Nat.log p q : ℝ) + 1) / Real.sqrt (qJordanTwo (q ^ (k + 1))) := by
  rw [qTarget_inner_primePower_mean_difference p q k hp hq]
  have hb := dilatedTargetMean_mul_bounds p q (q ^ k) hp hq.pos (pow_pos hq.pos _)
  rw [← pow_succ'] at hb
  have hpos := Real.sqrt_pos.mpr (qJordanTwo_pos (q ^ (k + 1)) (pow_pos hq.pos _))
  exact ⟨(div_le_div_iff_of_pos_right hpos).2 hb.1,
    (div_le_div_iff_of_pos_right hpos).2 hb.2⟩


theorem qTarget_inner_three_explicit (p : ℕ) (hp : 1 < p) :
    inner ℝ (qTarget p hp) (normalizedDivisorWavelet (3 : ℕ+)) =
      (dilatedTargetMean p 3 - dilatedTargetMean p 1) / Real.sqrt 8 := by
  have h := qTarget_inner_primePower_mean_difference p 3 0 hp (by norm_num)
  have hj : qJordanTwo 3 = 8 := by norm_num [qJordanTwo, valuationWaveletWeight]
  simpa [hj] using h

theorem qTarget_inner_two_explicit (p : ℕ) (hp : 1 < p) :
    inner ℝ (qTarget p hp) (normalizedDivisorWavelet (2 : ℕ+)) =
      (dilatedTargetMean p 2 - dilatedTargetMean p 1) / Real.sqrt 3 := by
  have h := qTarget_inner_primePower_mean_difference p 2 0 hp (by norm_num)
  have hj : qJordanTwo 2 = 3 := by norm_num [qJordanTwo, valuationWaveletWeight]
  simpa [hj] using h

theorem qTarget_inner_five_explicit (p : ℕ) (hp : 1 < p) :
    inner ℝ (qTarget p hp) (normalizedDivisorWavelet (5 : ℕ+)) =
      (dilatedTargetMean p 5 - dilatedTargetMean p 1) / Real.sqrt 24 := by
  have h := qTarget_inner_primePower_mean_difference p 5 0 hp (by norm_num)
  have hj : qJordanTwo 5 = 24 := by norm_num [qJordanTwo, valuationWaveletWeight]
  simpa [hj] using h


theorem qTarget_inner_four_explicit (p : ℕ) (hp : 1 < p) :
    inner ℝ (qTarget p hp) (normalizedDivisorWavelet (4 : ℕ+)) =
      (dilatedTargetMean p 4 - dilatedTargetMean p 2) / Real.sqrt 12 := by
  have h := qTarget_inner_primePower_mean_difference p 2 1 hp (by norm_num)
  have hj : qJordanTwo 4 = 12 := by
    have hj' := qJordanTwo_prime_pow 2 2 (by norm_num)
    norm_num [valuationWaveletWeight] at hj'
    exact hj'
  simpa [hj] using h

theorem qTarget_inner_nine_explicit (p : ℕ) (hp : 1 < p) :
    inner ℝ (qTarget p hp) (normalizedDivisorWavelet (9 : ℕ+)) =
      (dilatedTargetMean p 9 - dilatedTargetMean p 3) / Real.sqrt 72 := by
  have h := qTarget_inner_primePower_mean_difference p 3 1 hp (by norm_num)
  have hj : qJordanTwo 9 = 72 := by
    have hj' := qJordanTwo_prime_pow 3 2 (by norm_num)
    norm_num [valuationWaveletWeight] at hj'
    exact hj'
  simpa [hj] using h

theorem primeCofactorResidual_two_energy_ge_eighth :
    (1 / 8 : ℝ) ≤ ‖primeCofactorResidual 2 (by norm_num)‖ ^ 2 := by
  have hc := primeCofactorResidual_inner_basis 2 (by norm_num) (3 : ℕ+)
  norm_num at hc
  have he := divisorBasis_error_finite_lower
    (primeCofactorResidual 2 (by norm_num)) (0 : QHilbert) {(3 : ℕ+)}
  simp only [Finset.sum_singleton, inner_zero_left, sub_zero] at he
  rw [hc, qTarget_inner_three_explicit] at he
  have hb := (dilatedTargetMean_mul_bounds 2 3 1 (by norm_num)
    (by norm_num) (by norm_num)).1
  norm_num at hb
  have hs : (Real.sqrt 8) ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
  have hd : 0 < (Real.sqrt 8) ^ 2 := sq_pos_of_pos hp
  rw [div_pow] at he
  have hh := (div_le_iff₀ hd).mp he
  nlinarith [sq_nonneg (dilatedTargetMean 2 3 - dilatedTargetMean 2 1 - 1)]

theorem primeCofactorResidual_three_energy_ge_twentyFourth :
    (1 / 24 : ℝ) ≤ ‖primeCofactorResidual 3 (by norm_num)‖ ^ 2 := by
  have hc := primeCofactorResidual_inner_basis 3 (by norm_num) (5 : ℕ+)
  norm_num at hc
  have he := divisorBasis_error_finite_lower
    (primeCofactorResidual 3 (by norm_num)) (0 : QHilbert) {(5 : ℕ+)}
  simp only [Finset.sum_singleton, inner_zero_left, sub_zero] at he
  rw [hc, qTarget_inner_five_explicit] at he
  have hb := (dilatedTargetMean_mul_bounds 3 5 1 (by norm_num)
    (by norm_num) (by norm_num)).1
  norm_num at hb
  have hs : (Real.sqrt 24) ^ 2 = 24 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt 24 := Real.sqrt_pos.mpr (by norm_num)
  have hd : 0 < (Real.sqrt 24) ^ 2 := sq_pos_of_pos hp
  rw [div_pow] at he
  have hh := (div_le_iff₀ hd).mp he
  nlinarith [sq_nonneg (dilatedTargetMean 3 5 - dilatedTargetMean 3 1 - 1)]

end RiemannResearch.RH.PrimePowerTarget
