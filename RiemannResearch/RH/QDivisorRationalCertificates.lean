/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimePowerRationalCertificates
import RiemannResearch.RH.QPrimePowerThresholdSeries
import RiemannResearch.RH.QPrimePowerThresholdTail
import RiemannResearch.RH.QDivisorHilbertBasis
import RiemannResearch.RH.QDivisorWaveletFactorization
import RiemannResearch.RH.PrimePowerTargetMellin
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

import RiemannResearch.RH.QDivisorWaveletOverlap
import RiemannResearch.RH.QPrimePowerOrthogonal
import RiemannResearch.RH.QFiniteEnergyBounds

/-!
# Signed rational divisor-coefficient certificates

Exact rational heads and outward endpoint certificates for every nonconstant
ambient divisor conductor. Both concrete examples below discharge every
hypothesis by exact kernel-checked rational arithmetic.

Source: user-provided research in FpCoprimeCoefficientsResearch20261022.md,
sections on signed Moebius threshold remainders and rational certificates.
The construction subtracts the dilation-one threshold head and uses the
zero Moebius divisor sum for nonconstant conductors. It retains the complete
signed infinite remainder. Endpoint tests use both denominator endpoints,
without assuming any sign for the coefficient or the chosen endpoints.

F_p remains Nat.log p n. These are certified actual integer-Zipf
ambient divisor coefficients, not legal-closure membership providers.
All full Parseval residuals and signed terms remain unchanged.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace RiemannResearch.RH.PrimePowerTarget
open ZetaTwoHilbert ZetaTwoProbability QDivisorHilbert

def thresholdDifferenceRationalHead (p d K : ℕ) : ℚ :=
  ∑ j ∈ Finset.range K,
    ∑ n ∈ Finset.Ico (logThresholdCutoff p d j)
      (logThresholdCutoff p 1 j), 1 / (n : ℚ) ^ 2

def divisorRationalHead (p t K : ℕ) : ℚ :=
  ∑ d ∈ t.divisors, (ArithmeticFunction.moebius (t / d) : ℚ) *
    thresholdDifferenceRationalHead p d K

def divisorRationalTailLower (p t K : ℕ) : ℚ :=
  ∑ d ∈ t.divisors, min (ArithmeticFunction.moebius (t / d) : ℚ) 0 *
    thresholdRationalTail p d K

def divisorRationalTailUpper (p t K : ℕ) : ℚ :=
  ∑ d ∈ t.divisors, max (ArithmeticFunction.moebius (t / d) : ℚ) 0 *
    thresholdRationalTail p d K

theorem thresholdDifferenceRationalHead_cast (p d K : ℕ)
    (hp : 1 < p) (hd : 0 < d) :
    (thresholdDifferenceRationalHead p d K : ℝ) / zetaTwo =
      ∑ j ∈ Finset.range K, (logThresholdMass p d j - logThresholdMass p 1 j) := by
  unfold thresholdDifferenceRationalHead
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  rw [logThresholdMass_difference_interval p 1 d j hp (by decide) hd, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  unfold positiveQWeight
  ring

theorem divisorRationalHead_cast (p t K : ℕ) (hp : 1 < p) (ht : 1 < t) :
    (divisorRationalHead p t K : ℝ) / zetaTwo =
      ∑ d ∈ t.divisors, (ArithmeticFunction.moebius (t / d) : ℝ) *
        ∑ j ∈ Finset.range K, logThresholdMass p d j := by
  unfold divisorRationalHead
  push_cast
  rw [Finset.sum_div]
  simp_rw [mul_div_assoc]
  have he : (∑ d ∈ t.divisors, (ArithmeticFunction.moebius (t / d) : ℝ) *
      ((thresholdDifferenceRationalHead p d K : ℝ) / zetaTwo)) =
    ∑ d ∈ t.divisors, (ArithmeticFunction.moebius (t / d) : ℝ) *
      ∑ j ∈ Finset.range K, (logThresholdMass p d j - logThresholdMass p 1 j) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [thresholdDifferenceRationalHead_cast p d K hp (Nat.pos_of_mem_divisors hd)]
  have hzero : (∑ d ∈ t.divisors, (ArithmeticFunction.moebius (t / d) : ℝ)) = 0 := by
    have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
      (f := fun n => if n = 1 then (1 : ℝ) else 0) (g := fun _ => (1 : ℝ))).mp
      (by intro n hn; simp [Nat.mem_divisors, ne_of_gt hn]) t (lt_trans zero_lt_one ht)
    simp only [mul_one, if_neg (ne_of_gt ht)] at h
    rw [Nat.sum_divisorsAntidiagonal'
      (fun a _ => (ArithmeticFunction.moebius a : ℝ))] at h
    exact h
  rw [he]
  simp_rw [Finset.sum_sub_distrib, mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hzero,
    zero_mul, sub_zero]

theorem divisorRationalTailLower_cast (p t K : ℕ) :
    (divisorRationalTailLower p t K : ℝ) / zetaTwo =
      ∑ d ∈ t.divisors, min (ArithmeticFunction.moebius (t / d) : ℝ) 0 *
        thresholdTailBound p d K := by
  unfold divisorRationalTailLower
  push_cast
  simp only [Finset.sum_div, mul_div_assoc, thresholdRationalTail_cast]

theorem divisorRationalTailUpper_cast (p t K : ℕ) :
    (divisorRationalTailUpper p t K : ℝ) / zetaTwo =
      ∑ d ∈ t.divisors, max (ArithmeticFunction.moebius (t / d) : ℝ) 0 *
        thresholdTailBound p d K := by
  unfold divisorRationalTailUpper
  push_cast
  simp only [Finset.sum_div, mul_div_assoc, thresholdRationalTail_cast]

/-- Exact rational head and every signed infinite divisor tail. -/
theorem qTarget_divisor_rational_error_exact (p K : ℕ) (hp : 1 < p)
    (t : ℕ+) (ht : 1 < (t : ℕ)) :
    inner ℝ (qTarget p hp) (normalizedDivisorWavelet t) -
      (divisorRationalHead p t K : ℝ) / (zetaTwo * Real.sqrt (qJordanTwo t)) =
      (∑ d ∈ (t : ℕ).divisors, (ArithmeticFunction.moebius ((t : ℕ) / d) : ℝ) *
        ∑' j : ℕ, logThresholdMass p d (j + K)) / Real.sqrt (qJordanTwo t) := by
  rw [← div_div, divisorRationalHead_cast p t K hp ht]
  exact qTarget_basis_threshold_error_exact p K hp t

theorem qTarget_divisor_rational_error_bounds (p K : ℕ) (hp : 1 < p)
    (t : ℕ+) (ht : 1 < (t : ℕ)) :
    (divisorRationalTailLower p t K : ℝ) / (zetaTwo * Real.sqrt (qJordanTwo t)) ≤
      inner ℝ (qTarget p hp) (normalizedDivisorWavelet t) -
        (divisorRationalHead p t K : ℝ) / (zetaTwo * Real.sqrt (qJordanTwo t)) ∧
    inner ℝ (qTarget p hp) (normalizedDivisorWavelet t) -
        (divisorRationalHead p t K : ℝ) / (zetaTwo * Real.sqrt (qJordanTwo t)) ≤
      (divisorRationalTailUpper p t K : ℝ) / (zetaTwo * Real.sqrt (qJordanTwo t)) := by
  simp only [← div_div, divisorRationalHead_cast p t K hp ht,
    divisorRationalTailLower_cast, divisorRationalTailUpper_cast]
  exact qTarget_basis_threshold_error_interval p K hp t

/-- Sign-safe outward endpoints: no positivity of the coefficient or endpoints is assumed. -/
theorem qTarget_divisor_rational_certificate (p K : ℕ) (hp : 1 < p)
    (t : ℕ+) (ht : 1 < (t : ℕ)) (zL zU sL sU lo hi : ℚ)
    (hzL : 0 < zL) (hzlo : (zL : ℝ) ≤ zetaTwo) (hzhi : zetaTwo ≤ zU)
    (hsL : 0 < sL) (hsU : 0 ≤ sU)
    (hslo : (sL : ℝ) ^ 2 ≤ qJordanTwo t)
    (hshi : qJordanTwo t ≤ (sU : ℝ) ^ 2)
    (hlo : max (lo * (zL * sL)) (lo * (zU * sU)) ≤
      divisorRationalHead p t K + divisorRationalTailLower p t K)
    (hhi : divisorRationalHead p t K + divisorRationalTailUpper p t K ≤
      min (hi * (zL * sL)) (hi * (zU * sU))) :
    (lo : ℝ) ≤ inner ℝ (qTarget p hp) (normalizedDivisorWavelet t) ∧
    inner ℝ (qTarget p hp) (normalizedDivisorWavelet t) ≤ (hi : ℝ) := by
  have hzL' : (0 : ℝ) < zL := by exact_mod_cast hzL
  have hsL' : (0 : ℝ) < sL := by exact_mod_cast hsL
  have hsU' : (0 : ℝ) ≤ sU := by exact_mod_cast hsU
  have hJ := qJordanTwo_pos t t.pos
  have hSl : (sL : ℝ) ≤ Real.sqrt (qJordanTwo t) :=
    (Real.le_sqrt hsL'.le hJ.le).2 hslo
  have hSu : Real.sqrt (qJordanTwo t) ≤ (sU : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨hsU', hshi⟩
  have hD : 0 < zetaTwo * Real.sqrt (qJordanTwo t) :=
    mul_pos zetaTwo_pos (Real.sqrt_pos.2 hJ)
  have hDl : (zL : ℝ) * sL ≤ zetaTwo * Real.sqrt (qJordanTwo t) :=
    mul_le_mul hzlo hSl hsL'.le zetaTwo_pos.le
  have hDu : zetaTwo * Real.sqrt (qJordanTwo t) ≤ (zU : ℝ) * sU :=
    mul_le_mul hzhi hSu (Real.sqrt_nonneg _) (zetaTwo_pos.le.trans hzhi)
  have hlo' : max ((lo : ℝ) * ((zL : ℝ) * sL)) ((lo : ℝ) * ((zU : ℝ) * sU)) ≤
      (divisorRationalHead p t K : ℝ) + (divisorRationalTailLower p t K : ℝ) := by
    exact_mod_cast hlo
  have hhi' : (divisorRationalHead p t K : ℝ) + (divisorRationalTailUpper p t K : ℝ) ≤
      min ((hi : ℝ) * ((zL : ℝ) * sL)) ((hi : ℝ) * ((zU : ℝ) * sU)) := by
    exact_mod_cast hhi
  have hlow : (lo : ℝ) * (zetaTwo * Real.sqrt (qJordanTwo t)) ≤
      (divisorRationalHead p t K : ℝ) + (divisorRationalTailLower p t K : ℝ) := by
    by_cases h : 0 ≤ (lo : ℝ)
    · exact ((mul_le_mul_of_nonneg_left hDu h).trans (le_max_right _ _)).trans hlo'
    · exact ((mul_le_mul_of_nonpos_left hDl (not_le.mp h).le).trans
        (le_max_left _ _)).trans hlo'
  have hupp : (divisorRationalHead p t K : ℝ) + (divisorRationalTailUpper p t K : ℝ) ≤
      (hi : ℝ) * (zetaTwo * Real.sqrt (qJordanTwo t)) := by
    by_cases h : 0 ≤ (hi : ℝ)
    · exact (hhi'.trans (min_le_left _ _)).trans (mul_le_mul_of_nonneg_left hDl h)
    · exact (hhi'.trans (min_le_right _ _)).trans
        (mul_le_mul_of_nonpos_left hDu (not_le.mp h).le)
  have hb := qTarget_divisor_rational_error_bounds p K hp t ht
  have hl := (le_div_iff₀ hD).2 hlow
  have hu := (div_le_iff₀ hD).2 hupp
  rw [add_div] at hl hu
  constructor <;> linarith [hb.1, hb.2]


set_option maxRecDepth 100000 in
/-- Signed composite example; the certified interval crosses zero. -/
theorem qTarget_two_conductor_fifteen_interval :
    (-4 : ℝ) / 1000 ≤ inner ℝ (qTarget 2 (by norm_num))
        (normalizedDivisorWavelet 15) ∧
    inner ℝ (qTarget 2 (by norm_num)) (normalizedDivisorWavelet 15) ≤ 5 / 1000 := by
  have h3 := qJordanTwo_prime_pow 3 1 (by norm_num)
  have h5 := qJordanTwo_prime_pow 5 1 (by norm_num)
  norm_num [valuationWaveletWeight] at h3 h5
  have hJ : qJordanTwo 15 = 192 := by
    rw [show 15 = 3 * 5 by norm_num, qJordanTwo_mul_coprime 3 5 (by decide), h3, h5]
    norm_num
  have h := qTarget_divisor_rational_certificate 2 7 (by norm_num) 15 (by norm_num)
    (1028 / 625) (329 / 200) (13856 / 1000) (13857 / 1000) (-4 / 1000) (5 / 1000)
    (by norm_num)
    (by norm_num; exact QFiniteEnergyBounds.zetaTwo_rational_bounds.1.le)
    (by norm_num; exact QFiniteEnergyBounds.zetaTwo_rational_bounds.2.le)
    (by norm_num) (by norm_num)
    (by norm_num [hJ])
    (by norm_num [hJ])
    (by decide +kernel) (by decide +kernel)
  convert h using 1 <;> norm_num

set_option maxRecDepth 100000 in
/-- Checked certificate for a conductor with two distinct primes. -/
theorem qTarget_three_conductor_ten_interval :
    (59 : ℝ) / 1000 ≤ inner ℝ (qTarget 3 (by norm_num))
        (normalizedDivisorWavelet 10) ∧
    inner ℝ (qTarget 3 (by norm_num)) (normalizedDivisorWavelet 10) ≤ 68 / 1000 := by
  have h2 := qJordanTwo_prime_pow 2 1 (by norm_num)
  have h5 := qJordanTwo_prime_pow 5 1 (by norm_num)
  norm_num [valuationWaveletWeight] at h2 h5
  have hJ : qJordanTwo 10 = 72 := by
    rw [show 10 = 2 * 5 by norm_num, qJordanTwo_mul_coprime 2 5 (by decide), h2, h5]
    norm_num
  have h := qTarget_divisor_rational_certificate 3 4 (by norm_num) 10 (by norm_num)
    (1028 / 625) (329 / 200) (8485 / 1000) (8486 / 1000) (59 / 1000) (68 / 1000)
    (by norm_num)
    (by norm_num; exact QFiniteEnergyBounds.zetaTwo_rational_bounds.1.le)
    (by norm_num; exact QFiniteEnergyBounds.zetaTwo_rational_bounds.2.le)
    (by norm_num) (by norm_num)
    (by norm_num [hJ])
    (by norm_num [hJ])
    (by decide +kernel) (by decide +kernel)
  convert h using 1 <;> norm_num

end RiemannResearch.RH.PrimePowerTarget
