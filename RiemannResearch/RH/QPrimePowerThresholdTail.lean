/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimePowerThresholdSeries
import RiemannResearch.RH.QPrimePowerCoprimeCoefficients
import RiemannResearch.RH.QDivisorHilbertBasis
import RiemannResearch.RH.QDivisorWaveletDensity
import RiemannResearch.RH.PrimePowerTargetMellin
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Lean.Elab.Tactic.Omega
import RiemannResearch.Analysis.InverseSquareTailCertificates
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Certified geometric tails for floor-log coefficients

Source: the user-provided tail inequality in
FpCoprimeCoefficientsResearch20261022.md, section 3 (22 October 2026).
The proof reuses the checked inverse-square tail certificates, exact integer
cutoffs, and complete threshold-series identities. It then sums two geometric
majorants. The bounds are valid for every natural p > 1 and positive dilation.

The exact signed remainder in QPrimePowerThresholdSeries remains primary.
Its enclosure here keeps negative and positive Moebius contributions separate.
Prime-power coefficients have finite interval heads and an explicit nonnegative
remainder bound. These are actual Zipf statements for F_p(n) = Nat.log p n,
not valuation identities. Analytic error certification does not by itself
certify floating-point rounding, legal Parseval saturation, or target membership.
All complete Parseval residuals remain unchanged.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace RiemannResearch.RH.PrimePowerTarget
open ZetaTwoHilbert ZetaTwoProbability QDivisibilityDensity QDivisorHilbert
open RiemannResearch.Analysis.InverseSquareTailCertificates

theorem logThresholdMass_le (p d j : ℕ) (hp : 1 < p) (hd : 0 < d) :
    logThresholdMass p d j ≤
      ((d : ℝ) / (p : ℝ) ^ (j + 1) +
        ((d : ℝ) / (p : ℝ) ^ (j + 1)) ^ 2) / zetaTwo := by
  let m := logThresholdCutoff p d j
  have hm : 0 < m := Nat.zero_lt_succ _
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : Summable (fun n : ℕ => if m ≤ n then positiveQWeight n else 0) := by
    apply Summable.of_nonneg_of_le _ _ positiveQWeight_summable
    · intro n
      split_ifs
      · exact positiveQWeight_nonneg n
      · exact le_rfl
    · intro n
      split_ifs
      · exact le_rfl
      · exact positiveQWeight_nonneg n
  have hhead : (∑ n ∈ Finset.range m, if m ≤ n then positiveQWeight n else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp [Nat.not_le_of_lt (Finset.mem_range.mp hn)]
  have he : logThresholdMass p d j =
      (∑' n : ℕ, 1 / ((m : ℝ) + n) ^ 2) / zetaTwo := by
    rw [logThresholdMass_cutoff p d j hp hd]
    change (∑' n : ℕ, if m ≤ n then positiveQWeight n else 0) = _
    rw [← hs.sum_add_tsum_nat_add m, hhead, zero_add, ← tsum_div_const]
    apply tsum_congr
    intro n
    simp only [Nat.le_add_left, ite_true, positiveQWeight, Nat.cast_add]
    simp [div_eq_mul_inv, mul_inv_rev, add_comm]
  have hb := (complete_tail_bounds (m : ℝ) hmR).2
  have hi0 : 0 ≤ 1 / (m : ℝ) := by positivity
  have hi1 : 1 / (m : ℝ) ≤ 1 := (div_le_one hmpos).2 hmR
  have hi3 : (1 / (m : ℝ)) ^ 3 ≤ (1 / (m : ℝ)) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hi1 (sq_nonneg (1 / (m : ℝ)))]
  have hb' : (∑' n : ℕ, 1 / ((m : ℝ) + n) ^ 2) ≤
      1 / (m : ℝ) + (1 / (m : ℝ)) ^ 2 := by
    unfold upper at hb
    nlinarith [sq_nonneg (1 / (m : ℝ))]
  have hpow : 0 < (p : ℝ) ^ (j + 1) := pow_pos (by exact_mod_cast (by omega : 0 < p)) _
  have hcut := (logThresholdCutoff_le_iff p d j m hp hd).mp (le_refl m)
  have hcutR : (p : ℝ) ^ (j + 1) ≤ (d : ℝ) * m := by exact_mod_cast hcut
  have hratio : 1 / (m : ℝ) ≤ (d : ℝ) / (p : ℝ) ^ (j + 1) := by
    apply (div_le_div_iff₀ hmpos hpow).2
    simpa only [one_mul] using hcutR
  rw [he]
  apply div_le_div_of_nonneg_right _ zetaTwo_pos.le
  calc
    _ ≤ 1 / (m : ℝ) + (1 / (m : ℝ)) ^ 2 := hb'
    _ ≤ _ := by gcongr

private theorem geometric_dilation_hasSum (a d : ℝ) (K : ℕ) (ha : 1 < a) :
    HasSum (fun j : ℕ => d / a ^ (j + K + 1)) (d / ((a - 1) * a ^ K)) := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hr0 : 0 ≤ a⁻¹ := inv_nonneg.mpr ha0.le
  have hr1 : a⁻¹ < 1 := (inv_lt_one₀ ha0).2 ha
  have hs := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (d / a ^ (K + 1))
  have hf : (fun j : ℕ => d / a ^ (j + K + 1)) =
      (fun j : ℕ => d / a ^ (K + 1) * a⁻¹ ^ j) := by
    funext j
    rw [show j + K + 1 = (K + 1) + j by omega, pow_add]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
    ring
  have hv : d / ((a - 1) * a ^ K) = d / a ^ (K + 1) * (1 - a⁻¹)⁻¹ := by
    have haN : a ≠ 0 := ne_of_gt ha0
    have ha1 : a - 1 ≠ 0 := by linarith
    rw [pow_succ]
    field_simp
  rw [hf, hv]
  exact hs

def thresholdTailBound (p d K : ℕ) : ℝ :=
  ((d : ℝ) / (((p : ℝ) - 1) * (p : ℝ) ^ K) +
    (d : ℝ) ^ 2 / (((p : ℝ) ^ 2 - 1) * ((p : ℝ) ^ 2) ^ K)) / zetaTwo

theorem thresholdTailBound_hasSum (p d K : ℕ) (hp : 1 < p) :
    HasSum (fun j : ℕ =>
      ((d : ℝ) / (p : ℝ) ^ (j + K + 1) +
        ((d : ℝ) / (p : ℝ) ^ (j + K + 1)) ^ 2) / zetaTwo)
      (thresholdTailBound p d K) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hp2 : (1 : ℝ) < (p : ℝ) ^ 2 := by nlinarith
  have hs := ((geometric_dilation_hasSum (p : ℝ) (d : ℝ) K hpR).add
    (geometric_dilation_hasSum ((p : ℝ) ^ 2) ((d : ℝ) ^ 2) K hp2)).div_const zetaTwo
  have hf : (fun j : ℕ =>
      ((d : ℝ) / (p : ℝ) ^ (j + K + 1) +
        ((d : ℝ) / (p : ℝ) ^ (j + K + 1)) ^ 2) / zetaTwo) =
      (fun j : ℕ => ((d : ℝ) / (p : ℝ) ^ (j + K + 1) +
        (d : ℝ) ^ 2 / ((p : ℝ) ^ 2) ^ (j + K + 1)) / zetaTwo) := by
    funext j
    simp only [div_pow, ← pow_mul]
    rw [Nat.mul_comm (j + K + 1) 2]
  rw [hf]
  exact hs

/-- The full exact level tail is bounded by two explicit geometric tails. -/
theorem threshold_tail_le (p d K : ℕ) (hp : 1 < p) (hd : 0 < d) :
    (∑' j : ℕ, logThresholdMass p d (j + K)) ≤ thresholdTailBound p d K := by
  rw [← (thresholdTailBound_hasSum p d K hp).tsum_eq]
  exact Summable.tsum_le_tsum (fun j => logThresholdMass_le p d (j + K) hp hd)
    ((summable_nat_add_iff K).2 (logThresholdMass_summable p d hp hd))
    (thresholdTailBound_hasSum p d K hp).summable

theorem dilatedTargetMean_threshold_error_bounds (p d K : ℕ)
    (hp : 1 < p) (hd : 0 < d) :
    0 ≤ dilatedTargetMean p d - ∑ j ∈ Finset.range K, logThresholdMass p d j ∧
      dilatedTargetMean p d - ∑ j ∈ Finset.range K, logThresholdMass p d j ≤
        thresholdTailBound p d K := by
  constructor
  · exact dilatedTargetMean_threshold_remainder_nonneg p d K hp hd
  · rw [dilatedTargetMean_threshold_head_tail p d K hp hd, add_sub_cancel_left]
    exact threshold_tail_le p d K hp hd

/-- Sign-sensitive enclosure of the exact coefficient remainder. -/
theorem qTarget_basis_threshold_error_interval (p K : ℕ) (hp : 1 < p) (t : ℕ+) :
    (∑ d ∈ (t : ℕ).divisors, min (ArithmeticFunction.moebius ((t : ℕ) / d) : ℝ) 0 *
        thresholdTailBound p d K) / Real.sqrt (qJordanTwo t) ≤
      inner ℝ (qTarget p hp) (normalizedDivisorWavelet t) -
        (∑ d ∈ (t : ℕ).divisors, (ArithmeticFunction.moebius ((t : ℕ) / d) : ℝ) *
          ∑ j ∈ Finset.range K, logThresholdMass p d j) / Real.sqrt (qJordanTwo t) ∧
    inner ℝ (qTarget p hp) (normalizedDivisorWavelet t) -
        (∑ d ∈ (t : ℕ).divisors, (ArithmeticFunction.moebius ((t : ℕ) / d) : ℝ) *
          ∑ j ∈ Finset.range K, logThresholdMass p d j) / Real.sqrt (qJordanTwo t) ≤
      (∑ d ∈ (t : ℕ).divisors, max (ArithmeticFunction.moebius ((t : ℕ) / d) : ℝ) 0 *
        thresholdTailBound p d K) / Real.sqrt (qJordanTwo t) := by
  have hterm (d : ℕ) (hd : d ∈ (t : ℕ).divisors) :
      min (ArithmeticFunction.moebius ((t : ℕ) / d) : ℝ) 0 * thresholdTailBound p d K ≤
        (ArithmeticFunction.moebius ((t : ℕ) / d) : ℝ) *
          ∑' j : ℕ, logThresholdMass p d (j + K) ∧
      (ArithmeticFunction.moebius ((t : ℕ) / d) : ℝ) *
          (∑' j : ℕ, logThresholdMass p d (j + K)) ≤
        max (ArithmeticFunction.moebius ((t : ℕ) / d) : ℝ) 0 * thresholdTailBound p d K := by
    have h0 : 0 ≤ ∑' j : ℕ, logThresholdMass p d (j + K) :=
      tsum_nonneg (fun j => logThresholdMass_nonneg p d (j + K))
    have hle := threshold_tail_le p d K hp (Nat.pos_of_mem_divisors hd)
    by_cases hc : 0 ≤ (ArithmeticFunction.moebius ((t : ℕ) / d) : ℝ)
    · rw [min_eq_right hc, max_eq_left hc, zero_mul]
      exact ⟨mul_nonneg hc h0, mul_le_mul_of_nonneg_left hle hc⟩
    · have hc' := (not_le.mp hc).le
      rw [min_eq_left hc', max_eq_right hc', zero_mul]
      exact ⟨mul_le_mul_of_nonpos_left hle hc', mul_nonpos_of_nonpos_of_nonneg hc' h0⟩
  simp only [qTarget_basis_threshold_error_exact p K hp t]
  constructor
  · exact div_le_div_of_nonneg_right
      (Finset.sum_le_sum (fun d hd => (hterm d hd).1)) (Real.sqrt_nonneg _)
  · exact div_le_div_of_nonneg_right
      (Finset.sum_le_sum (fun d hd => (hterm d hd).2)) (Real.sqrt_nonneg _)

/-- Finite interval sums give certified lower bounds with an explicit upper error. -/
theorem qTarget_primePower_threshold_error_bounds (p q k K : ℕ)
    (hp : 1 < p) (hq : q.Prime) :
    0 ≤ inner ℝ (qTarget p hp)
        (normalizedDivisorWavelet ⟨q ^ (k + 1), pow_pos hq.pos _⟩) -
      ∑ j ∈ Finset.range K, primePowerThresholdTerm p q k j ∧
    inner ℝ (qTarget p hp)
        (normalizedDivisorWavelet ⟨q ^ (k + 1), pow_pos hq.pos _⟩) -
      (∑ j ∈ Finset.range K, primePowerThresholdTerm p q k j) ≤
        thresholdTailBound p (q ^ (k + 1)) K /
          Real.sqrt (qJordanTwo (q ^ (k + 1))) := by
  rw [qTarget_primePower_threshold_head_tail p q k K hp hq, add_sub_cancel_left]
  constructor
  · exact tsum_nonneg (fun j => primePowerThresholdTerm_nonneg p q k (j + K))
  · have hs := (summable_nat_add_iff K).2
      (qTarget_primePower_threshold_hasSum p q k hp hq).summable
    have hs' := ((summable_nat_add_iff K).2
      (logThresholdMass_summable p (q ^ (k + 1)) hp (pow_pos hq.pos _))).div_const
        (Real.sqrt (qJordanTwo (q ^ (k + 1))))
    have hterm (j : ℕ) : primePowerThresholdTerm p q k (j + K) ≤
        logThresholdMass p (q ^ (k + 1)) (j + K) /
          Real.sqrt (qJordanTwo (q ^ (k + 1))) := by
      unfold primePowerThresholdTerm
      rw [← logThresholdMass_difference_interval p (q ^ k) (q ^ (k + 1)) (j + K)
        hp (pow_pos hq.pos _) (Nat.pow_le_pow_right hq.pos (Nat.le_succ k))]
      exact div_le_div_of_nonneg_right
        (sub_le_self _ (logThresholdMass_nonneg p (q ^ k) (j + K))) (Real.sqrt_nonneg _)
    calc
      _ ≤ ∑' j : ℕ, logThresholdMass p (q ^ (k + 1)) (j + K) /
          Real.sqrt (qJordanTwo (q ^ (k + 1))) := Summable.tsum_le_tsum hterm hs hs'
      _ = _ := tsum_div_const
      _ ≤ _ := div_le_div_of_nonneg_right
        (threshold_tail_le p (q ^ (k + 1)) K hp (pow_pos hq.pos _)) (Real.sqrt_nonneg _)

end RiemannResearch.RH.PrimePowerTarget
