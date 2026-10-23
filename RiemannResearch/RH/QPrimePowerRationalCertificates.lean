/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimePowerThresholdTail
import RiemannResearch.RH.QPrimePowerThresholdSeries
import RiemannResearch.RH.QPrimePowerOrthogonal
import RiemannResearch.RH.QDivisorWaveletOverlap
import RiemannResearch.RH.QDivisorWaveletFactorization
import RiemannResearch.RH.QDivisorHilbertBasis
import RiemannResearch.RH.PrimePowerTargetMellin
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.QFiniteEnergyBounds
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
/-!
# Rational certificates for prime-power floor-log coefficients

Source: user-provided coefficient and threshold research in
FpCoprimeCoefficientsResearch20261022.md, sections 3 and the checked geometric
tail section (22 October 2026). These support the threshold representation
and tail strategy. This module supplies exact rational evaluation and outward
rational endpoint certification.

The complete original level tail remains in the exact identity. Rational
bounds on zeta(2) and the square-root normalizer, together with finite rational
inequalities, certify intervals for actual integer-Zipf coefficients. The two
examples discharge every hypothesis using checked zeta bounds, squared rational
bounds, and kernel reduction of exact finite sums. No floating-point result,
native evaluation axiom, or unproved coefficient estimate is used.

F_p means Nat.log p n, not a valuation. The certified vectors are ambient
divisor modes; these intervals do not prove legal Parseval saturation or
membership in closureWithConstants. All full signed Parseval errors and norm
residuals from the preceding modules remain unchanged.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace RiemannResearch.RH.PrimePowerTarget
open ZetaTwoHilbert ZetaTwoProbability QDivisorHilbert

/-- Exact rational numerator of the finite threshold head. -/
def primePowerRationalHead (p q k K : ℕ) : ℚ :=
  ∑ j ∈ Finset.range K,
    ∑ n ∈ Finset.Ico (logThresholdCutoff p (q ^ (k + 1)) j)
      (logThresholdCutoff p (q ^ k) j), 1 / (n : ℚ) ^ 2

/-- Rational numerator of the proved geometric truncation bound. -/
def thresholdRationalTail (p d K : ℕ) : ℚ :=
  (d : ℚ) / (((p : ℚ) - 1) * (p : ℚ) ^ K) +
    (d : ℚ) ^ 2 / (((p : ℚ) ^ 2 - 1) * ((p : ℚ) ^ 2) ^ K)

theorem primePowerRationalHead_cast (p q k K : ℕ) :
    (primePowerRationalHead p q k K : ℝ) /
        (zetaTwo * Real.sqrt (qJordanTwo (q ^ (k + 1)))) =
      ∑ j ∈ Finset.range K, primePowerThresholdTerm p q k j := by
  unfold primePowerRationalHead primePowerThresholdTerm
  push_cast
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro n hn
  unfold positiveQWeight
  ring

theorem thresholdRationalTail_cast (p d K : ℕ) :
    (thresholdRationalTail p d K : ℝ) / zetaTwo = thresholdTailBound p d K := by
  unfold thresholdRationalTail thresholdTailBound
  push_cast
  rfl

/-- Rational finite head plus the complete original coefficient tail. -/
theorem qTarget_primePower_rational_head_tail (p q k K : ℕ)
    (hp : 1 < p) (hq : q.Prime) :
    inner ℝ (qTarget p hp)
        (normalizedDivisorWavelet ⟨q ^ (k + 1), pow_pos hq.pos _⟩) =
      (primePowerRationalHead p q k K : ℝ) /
        (zetaTwo * Real.sqrt (qJordanTwo (q ^ (k + 1)))) +
      ∑' j : ℕ, primePowerThresholdTerm p q k (j + K) := by
  rw [primePowerRationalHead_cast]
  exact qTarget_primePower_threshold_head_tail p q k K hp hq

/-- Outward rational rounding is checked by rational inequalities. The hypotheses
bound only the normalizer and explicit arithmetic; no coefficient estimate is assumed. -/
theorem qTarget_primePower_rational_certificate (p q k K : ℕ)
    (hp : 1 < p) (hq : q.Prime)
    (zL zU sL sU lo hi : ℚ)
    (hzL : 0 < zL) (hzlo : (zL : ℝ) ≤ zetaTwo) (hzhi : zetaTwo ≤ zU)
    (hsL : 0 < sL) (hsU : 0 ≤ sU)
    (hslo : (sL : ℝ) ^ 2 ≤ qJordanTwo (q ^ (k + 1)))
    (hshi : qJordanTwo (q ^ (k + 1)) ≤ (sU : ℝ) ^ 2)
    (hlo0 : 0 ≤ lo) (hhi0 : 0 ≤ hi)
    (hlo : lo * (zU * sU) ≤ primePowerRationalHead p q k K)
    (hhi : primePowerRationalHead p q k K + thresholdRationalTail p (q ^ (k + 1)) K ≤
      hi * (zL * sL)) :
    (lo : ℝ) ≤ inner ℝ (qTarget p hp)
        (normalizedDivisorWavelet ⟨q ^ (k + 1), pow_pos hq.pos _⟩) ∧
    inner ℝ (qTarget p hp)
        (normalizedDivisorWavelet ⟨q ^ (k + 1), pow_pos hq.pos _⟩) ≤ (hi : ℝ) := by
  have hzL' : (0 : ℝ) < zL := by exact_mod_cast hzL
  have hsL' : (0 : ℝ) < sL := by exact_mod_cast hsL
  have hsU' : (0 : ℝ) ≤ sU := by exact_mod_cast hsU
  have hlo0' : (0 : ℝ) ≤ lo := by exact_mod_cast hlo0
  have hhi0' : (0 : ℝ) ≤ hi := by exact_mod_cast hhi0
  have hJ := qJordanTwo_pos (q ^ (k + 1)) (pow_pos hq.pos _)
  have hSl : (sL : ℝ) ≤ Real.sqrt (qJordanTwo (q ^ (k + 1))) :=
    (Real.le_sqrt hsL'.le hJ.le).2 hslo
  have hSu : Real.sqrt (qJordanTwo (q ^ (k + 1))) ≤ (sU : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨hsU', hshi⟩
  have hD : 0 < zetaTwo * Real.sqrt (qJordanTwo (q ^ (k + 1))) :=
    mul_pos zetaTwo_pos (Real.sqrt_pos.2 hJ)
  have hDl : (zL : ℝ) * sL ≤ zetaTwo * Real.sqrt (qJordanTwo (q ^ (k + 1))) :=
    mul_le_mul hzlo hSl hsL'.le zetaTwo_pos.le
  have hDu : zetaTwo * Real.sqrt (qJordanTwo (q ^ (k + 1))) ≤ (zU : ℝ) * sU :=
    mul_le_mul hzhi hSu (Real.sqrt_nonneg _) (zetaTwo_pos.le.trans hzhi)
  have hlo' : (lo : ℝ) * ((zU : ℝ) * sU) ≤ (primePowerRationalHead p q k K : ℝ) := by
    exact_mod_cast hlo
  have hhi' : (primePowerRationalHead p q k K : ℝ) +
      (thresholdRationalTail p (q ^ (k + 1)) K : ℝ) ≤ (hi : ℝ) * ((zL : ℝ) * sL) := by
    exact_mod_cast hhi
  have hb := qTarget_primePower_threshold_error_bounds p q k K hp hq
  rw [← primePowerRationalHead_cast] at hb
  rw [← thresholdRationalTail_cast, div_div] at hb
  constructor
  · have h := (le_div_iff₀ hD).2
      ((mul_le_mul_of_nonneg_left hDu hlo0').trans hlo')
    linarith [hb.1]
  · have h := (div_le_iff₀ hD).2
      (hhi'.trans (mul_le_mul_of_nonneg_left hDl hhi0'))
    rw [add_div] at h
    linarith [hb.2]


set_option maxRecDepth 100000 in
/-- A checked outward decimal interval for the coprime conductor 3 of F_2. -/
theorem qTarget_two_conductor_three_interval :
    (397 : ℝ) / 1000 ≤ inner ℝ (qTarget 2 (by norm_num))
        (normalizedDivisorWavelet 3) ∧
    inner ℝ (qTarget 2 (by norm_num)) (normalizedDivisorWavelet 3) ≤ 403 / 1000 := by
  have hJ : qJordanTwo (3 ^ (0 + 1)) = 8 := by
    rw [qJordanTwo_prime_pow 3 (0 + 1) (by norm_num)]
    norm_num [valuationWaveletWeight]
  have h := qTarget_primePower_rational_certificate 2 3 0 7
    (by norm_num) (by norm_num)
    (1028 / 625) (329 / 200) (2828 / 1000) (2829 / 1000)
    (397 / 1000) (403 / 1000)
    (by norm_num)
    (by norm_num; exact QFiniteEnergyBounds.zetaTwo_rational_bounds.1.le)
    (by norm_num; exact QFiniteEnergyBounds.zetaTwo_rational_bounds.2.le)
    (by norm_num) (by norm_num)
    (by rw [hJ]; norm_num)
    (by rw [hJ]; norm_num)
    (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel)
  norm_num only [Nat.reduceAdd, pow_one, Rat.cast_div, Rat.cast_ofNat] at h
  convert h using 1 <;> norm_num

set_option maxRecDepth 100000 in
/-- A checked outward decimal interval for the coprime conductor 2 of F_3. -/
theorem qTarget_three_conductor_two_interval :
    (141 : ℝ) / 1000 ≤ inner ℝ (qTarget 3 (by norm_num))
        (normalizedDivisorWavelet 2) ∧
    inner ℝ (qTarget 3 (by norm_num)) (normalizedDivisorWavelet 2) ≤ 146 / 1000 := by
  have hJ : qJordanTwo (2 ^ (0 + 1)) = 3 := by
    rw [qJordanTwo_prime_pow 2 (0 + 1) (by norm_num)]
    norm_num [valuationWaveletWeight]
  have h := qTarget_primePower_rational_certificate 3 2 0 4
    (by norm_num) (by norm_num)
    (1028 / 625) (329 / 200) (1732 / 1000) (1733 / 1000)
    (141 / 1000) (146 / 1000)
    (by norm_num)
    (by norm_num; exact QFiniteEnergyBounds.zetaTwo_rational_bounds.1.le)
    (by norm_num; exact QFiniteEnergyBounds.zetaTwo_rational_bounds.2.le)
    (by norm_num) (by norm_num)
    (by rw [hJ]; norm_num)
    (by rw [hJ]; norm_num)
    (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel)
  norm_num only [Nat.reduceAdd, pow_one, Rat.cast_div, Rat.cast_ofNat] at h
  convert h using 1 <;> norm_num

end RiemannResearch.RH.PrimePowerTarget
