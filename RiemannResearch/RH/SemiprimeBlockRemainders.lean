/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.LogPowerSummability
import RiemannResearch.NumberTheory.PrimeNumberTheorem.Consequences
import RiemannResearch.RH.SemiprimeFekete
import RiemannResearch.RH.AdjacentDigitCovariance
import RiemannResearch.RH.CenteredMeanQuotients
import RiemannResearch.RH.QDensityAugmentedSpan
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.ResidueDivisorZeroExclusion
import RiemannResearch.RH.ResidueProjectionL1
import RiemannResearch.RH.ThresholdHilbertMean
import RiemannResearch.RH.ZetaTwoParetoTransfer
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Multiplicative defects of the reciprocal residue pairing

We use the coordinate formula for the reciprocal approximants and the exact
Pareto tail mass. All conductors here may be composite or equal.
The overlap Gram bounds imply absolute summability at consecutive prime products.
Ordinary and corrected block signs give finite upper certificates for the residual energy.
-/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.SemiprimeFekete
open CoefficientStabilization CenteredMeanSnake
open RiemannResearch.RH.QParetoEquivalence RiemannResearch.RH.QDensityMetric
open RiemannResearch.RH.ZetaTwoParetoTransfer

/-- Error of the conductor-a reciprocal approximant to the constant. -/
def residueGap (a : ℕ) : ThresholdHilbert := hilbertOne - toPareto (approximation a)

/-- The carry in the physical coordinates of the multiplicative defect. -/
def residueCarry (a b : ℕ) : ThresholdHilbert :=
  residueGap a + residueGap b - residueGap (a * b)

/-- Signed failure of multiplicative additivity, for arbitrary conductors. -/
def residueDefect (a b : ℕ) : ℝ :=
  reciprocalResiduePairing (a * b) - reciprocalResiduePairing a - reciprocalResiduePairing b

/-- A nonnegative physical vector supported above n has a constant envelope C. -/
def HasTailBound (v : ThresholdHilbert) (n : ℕ) (C : ℝ) : Prop :=
  ∀ m, 0 ≤ hilbertSequence v m ∧ hilbertSequence v m ≤ if n ≤ m then C else 0

theorem residueGap_coords {a m : ℕ} (ha : 0 < a) (hm : 0 < m) :
    hilbertSequence (residueGap a) m = 1 - ((m % a : ℕ) : ℝ) / m := by
  simp [residueGap, hilbertSequence_sub, hilbertOne_sequence, zeroAnchor, hm.ne',
    toPareto_sequence, approximation_sequence a m ha]

theorem residueGap_tailBound {a : ℕ} (ha : 0 < a) : HasTailBound (residueGap a) a 1 := by
  intro m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [ha.ne']
  rw [residueGap_coords ha hm]
  have hp : 0 < (m : ℝ) := by exact_mod_cast hm
  by_cases hc : a ≤ m
  · rw [if_pos hc]
    have hh : ((m % a : ℕ) : ℝ) / m ≤ 1 :=
      (div_le_one hp).2 (by exact_mod_cast Nat.mod_le m a)
    exact ⟨sub_nonneg.mpr hh, sub_le_self _ (by positivity)⟩
  · rw [if_neg hc, Nat.mod_eq_of_lt (lt_of_not_ge hc), div_self hp.ne', sub_self]
    simp

theorem residueGap_antitone_of_dvd {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ∣ b) (m : ℕ) :
    hilbertSequence (residueGap b) m ≤ hilbertSequence (residueGap a) m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  rw [residueGap_coords ha hm, residueGap_coords hb hm]
  apply sub_le_sub_left
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast (show m % a ≤ m % b by
    calc m % a = (m % b) % a := (Nat.mod_mod_of_dvd m hab).symm
         _ ≤ m % b := Nat.mod_le _ _)

theorem residueCarry_sandwich {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (m : ℕ) :
    hilbertSequence (residueGap a) m ≤ hilbertSequence (residueCarry a b) m ∧
    hilbertSequence (residueCarry a b) m ≤
      (if a ≤ m then (1 : ℝ) else 0) + (if b ≤ m then (1 : ℝ) else 0) := by
  have h := residueGap_antitone_of_dvd hb (Nat.mul_pos ha hb) (dvd_mul_left b a) m
  have hzero := (residueGap_tailBound (Nat.mul_pos ha hb) m).1
  have hx := (residueGap_tailBound ha m).2
  have hy := (residueGap_tailBound hb m).2
  simp only [residueCarry, hilbertSequence_sub, hilbertSequence_add, Pi.sub_apply, Pi.add_apply]
  constructor <;> linarith

theorem residueCarry_tailBound {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) :
    HasTailBound (residueCarry a b) a 2 := by
  intro m
  obtain ⟨h₁, h₂⟩ := residueCarry_sandwich ha hb m
  refine ⟨((residueGap_tailBound ha m).1).trans h₁, h₂.trans ?_⟩
  by_cases h : b ≤ m
  · norm_num [h, hab.trans h]
  · simp only [if_neg h, add_zero]
    split_ifs <;> norm_num

theorem residueCarry_norm_sq_le {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    ‖residueCarry a b‖ ^ 2 ≤ 1 / (a : ℝ) + 3 / (b : ℝ) := by
  have hb := ha.trans_le hab
  let W (j m : ℕ) := if j ≤ m then positiveWeight m else 0
  have h (m : ℕ) : positiveWeight m * hilbertSequence (residueCarry a b) m ^ 2 ≤
      W a m + 3 * W b m := by
    obtain ⟨hl, hh⟩ := residueCarry_sandwich ha hb m
    have hz := ((residueGap_tailBound ha m).1).trans hl
    have hw := positiveWeight_nonneg m
    by_cases hbm : b ≤ m
    · have ham := hab.trans hbm
      simp only [if_pos ham, if_pos hbm, W] at hh ⊢
      have hs : hilbertSequence (residueCarry a b) m ^ 2 ≤ 4 := by
        nlinarith only [mul_nonneg hz (sub_nonneg.mpr hh), hh]
      nlinarith only [mul_le_mul_of_nonneg_left hs hw]
    · by_cases ham : a ≤ m
      · simp only [if_pos ham, if_neg hbm, W, mul_zero, add_zero] at hh ⊢
        exact mul_le_of_le_one_right hw (by nlinarith only [mul_nonneg hz (sub_nonneg.mpr hh), hh])
      · simp only [if_neg ham, if_neg hbm, W, mul_zero, add_zero] at hh ⊢
        simp [le_antisymm hh hz]
  rw [hilbert_norm_weighted_sq]
  have hc := Summable.tsum_le_tsum h (hilbertSequence_square_summable _)
    ((AdjacentDigit.tailWeight_summable a).add ((AdjacentDigit.tailWeight_summable b).mul_left 3))
  simpa only [W, Summable.tsum_add (AdjacentDigit.tailWeight_summable a)
    ((AdjacentDigit.tailWeight_summable b).mul_left 3), tsum_mul_left,
    AdjacentDigit.tailWeight_tsum a ha, AdjacentDigit.tailWeight_tsum b hb,
    mul_one_div] using hc

theorem residueGap_pairing (a : ℕ) :
    inner ℝ limitResidual (residueGap a) = ‖limitResidual‖ ^ 2 - reciprocalResiduePairing a := by
  rw [residueGap, inner_sub_right, limitResidual_mean_and_screened_norm.1, reciprocalResiduePairing]

theorem residueDefect_centered (a b : ℕ) :
    residueDefect a b + ‖limitResidual‖ ^ 2 = inner ℝ limitResidual (residueCarry a b) := by
  rw [residueCarry, inner_sub_right, inner_add_right, residueGap_pairing, residueGap_pairing,
    residueGap_pairing, residueDefect]
  ring

theorem residueDefect_error_sq_le {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    (residueDefect a b + ‖limitResidual‖ ^ 2) ^ 2 ≤
      ‖limitResidual‖ ^ 2 * (1 / (a : ℝ) + 3 / (b : ℝ)) := by
  rw [residueDefect_centered]
  calc
    _ ≤ (‖limitResidual‖ * ‖residueCarry a b‖) ^ 2 := by
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 (abs_real_inner_le_norm _ _)
    _ ≤ _ := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (residueCarry_norm_sq_le ha hab) (sq_nonneg _)

theorem residueDefect_upper {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    residueDefect a b ≤ (1 / (a : ℝ) + 3 / (b : ℝ)) / 4 := by
  have h := (le_abs_self _).trans (abs_real_inner_le_norm limitResidual (residueCarry a b))
  rw [← residueDefect_centered] at h
  nlinarith only [h, sq_nonneg (‖limitResidual‖-‖residueCarry a b‖ / 2),
    residueCarry_norm_sq_le ha hab]

theorem energy_le_of_residueDefect_nonneg {a b : ℕ} (ha : 0 < a) (hab : a ≤ b)
    (h : 0 ≤ residueDefect a b) :
    ‖limitResidual‖ ^ 2 ≤ 1 / (a : ℝ) + 3 / (b : ℝ) := by
  have he := residueDefect_error_sq_le ha hab
  by_cases hz : ‖limitResidual‖ = 0
  · simpa only [hz, zero_pow (by decide : 2 ≠ 0)] using
      (show (0 : ℝ) ≤ 1 / (a : ℝ) + 3 / (b : ℝ) by positivity)
  have hp := sq_pos_of_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz))
  apply le_of_not_gt
  intro hbad
  nlinarith only [he, h, sq_nonneg (residueDefect a b), mul_nonneg h hp.le,
    mul_pos hp (sub_pos.mpr hbad)]

/-- A single favorable defect excludes right zeta zeros with a larger Mellin obstruction. -/
theorem rightZero_bound_of_residueDefect_nonneg {a b : ℕ} (ha : 0 < a) (hab : a ≤ b)
    (h : 0 ≤ residueDefect a b) (ρ : ℂ) (hhalf : (1 / 2 : ℝ) < ρ.re) (hρ : ρ ≠ 1)
    (hz : riemannZeta ρ = 0) :
    (2 * ρ.re-1) / ‖ρ‖ ^ 2 ≤ 1 / (a : ℝ) + 3 / (b : ℝ) := by
  exact (CorrectionTail.limitEnergy_lower_of_zeta_zero ρ hhalf hρ hz).trans
    (ProjectionSchur.limitResidual_norm_sq ▸ energy_le_of_residueDefect_nonneg ha hab h)

/-! ## Gram bounds for overlapping tail supports -/

private theorem tailBound_inner_le {x y : ThresholdHilbert} {i j : ℕ} {C D : ℝ}
    (hx : HasTailBound x i C) (hy : HasTailBound y j D) (hC : 0 ≤ C)
    (hj : 0 < j) : inner ℝ x y ≤ C * D / (j : ℝ) := by
  have h (m : ℕ) : positiveWeight m * (hilbertSequence x m * hilbertSequence y m) ≤
      (C * D) * (if j ≤ m then positiveWeight m else 0) := by
    obtain ⟨hx₀, hxm⟩ := hx m
    obtain ⟨hy₀, hym⟩ := hy m
    have hu : hilbertSequence x m ≤ C := hxm.trans (by split_ifs <;> simp [hC])
    by_cases hh : j ≤ m
    · rw [if_pos hh] at hym ⊢
      rw [mul_comm (C * D)]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hu hym hy₀ hC) (positiveWeight_nonneg m)
    · rw [if_neg hh] at hym ⊢
      simp [le_antisymm hym hy₀]
  rw [hilbert_inner_weighted]
  unfold paretoInner
  have hs := weighted_product_summable_of_square
    (hilbertSequence_square_summable x) (hilbertSequence_square_summable y)
  simpa only [tsum_mul_left, AdjacentDigit.tailWeight_tsum j hj, mul_one_div] using
    (hs.tsum_le_tsum h ((AdjacentDigit.tailWeight_summable j).mul_left (C * D)))

/-- Summing an upper triangular Gram bound counts each earlier cross term twice. -/
theorem norm_sum_sq_le_odd_weights (x : ℕ → ThresholdHilbert) (t : ℕ → ℝ)
    (h : ∀ i j, i ≤ j → inner ℝ (x i) (x j) ≤ t j) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, x i‖ ^ 2 ≤
      ∑ i ∈ Finset.range n, (2 * (i : ℝ) + 1) * t i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, norm_add_sq_real]
    have hcross : inner ℝ (∑ i ∈ Finset.range n, x i) (x n) ≤ (n : ℝ) * t n := by
      rw [sum_inner]
      simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
        (Finset.sum_le_sum (s := Finset.range n)
          fun i hi => h i n (Finset.mem_range.mp hi).le)
    have hself := h n n le_rfl
    rw [real_inner_self_eq_norm_sq] at hself
    linarith

private theorem inner_sum_sq_bound (v : ThresholdHilbert) (x : ℕ → ThresholdHilbert)
    (t : ℕ → ℝ) (h : ∀ i j, i ≤ j → inner ℝ (x i) (x j) ≤ t j) (n : ℕ) :
    (inner ℝ v (∑ i ∈ Finset.range n, x i)) ^ 2 ≤
      ‖v‖ ^ 2 * ∑ i ∈ Finset.range n, (2 * (i : ℝ) + 1) * t i := by
  calc
    _ ≤ (‖v‖ * ‖∑ i ∈ Finset.range n, x i‖) ^ 2 := by
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 (abs_real_inner_le_norm _ _)
    _ ≤ _ := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (norm_sum_sq_le_odd_weights x t h n) (sq_nonneg _)

local notation "P" => Nat.nth Nat.Prime

theorem signedPairing_eq_adjacent_defect (j : ℕ) :
    signedPairing j = residueDefect (P j) (P (j + 1)) :=
  semiprime_pairing_eq_residue_defect
    (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime j)
    (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (j + 1))
    ((Nat.nth_strictMono Nat.infinite_setOfPred_prime) (Nat.lt_succ_self j)).ne

/-- The support-overlap constant for an ordinary signed block. -/
def blockWeight (k n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, (2 * (j : ℝ) + 1) * (1 / (P (k + j) : ℝ))

/-- The smaller overlap constant for a block with both singleton residues restored. -/
def productBlockWeight (k n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, (2 * (j : ℝ) + 1) * (1 / ((P (k + j) * P (k + j + 1) : ℕ) : ℝ))

def correctedBlock (k n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, reciprocalResiduePairing (P (k + j) * P (k + j + 1))

theorem correctedBlock_eq_restored (k n : ℕ) :
    correctedBlock k n = ∑ j ∈ Finset.range n,
      (signedPairing (k + j) + reciprocalResiduePairing (P (k + j)) +
        reciprocalResiduePairing (P (k + j + 1))) := by
  apply Finset.sum_congr rfl
  intro j _
  rw [signedPairing_eq_adjacent_defect, residueDefect]
  ring

theorem block_error_sq_le_odd_weights (k n : ℕ) :
    (cumulative (k + n) - cumulative k + (n : ℝ) * ‖limitResidual‖ ^ 2) ^ 2 ≤
      ‖limitResidual‖ ^ 2 * (4 * blockWeight k n) := by
  let x j := residueCarry (P (k + j)) (P (k + j + 1))
  have hx j : HasTailBound (x j) (P (k + j)) 2 := residueCarry_tailBound
    (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _).pos
    (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _).pos
    ((Nat.nth_strictMono Nat.infinite_setOfPred_prime) (Nat.lt_succ_self _)).le
  have h i j (_ : i ≤ j) : inner ℝ (x i) (x j) ≤ 4 / (P (k + j) : ℝ) := by
    simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using
      tailBound_inner_le (hx i) (hx j) (by norm_num)
        (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _).pos
  have hid : inner ℝ limitResidual (∑ i ∈ Finset.range n, x i) =
      cumulative (k + n) - cumulative k + (n : ℝ) * ‖limitResidual‖ ^ 2 := by
    rw [inner_sum, cumulative_increment]
    simp only [x, ← residueDefect_centered, ← signedPairing_eq_adjacent_defect,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← hid]
  refine (inner_sum_sq_bound limitResidual x _ h n).trans_eq ?_
  congr 1
  rw [blockWeight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem correctedBlock_error_sq_le (k n : ℕ) :
    ((n : ℝ) * ‖limitResidual‖ ^ 2 - correctedBlock k n) ^ 2 ≤
      ‖limitResidual‖ ^ 2 * productBlockWeight k n := by
  let q j := P (k + j) * P (k + j + 1)
  have hq j : 0 < q j := Nat.mul_pos
    (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _).pos
    (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _).pos
  have h i j (_ : i ≤ j) :
      inner ℝ (residueGap (q i)) (residueGap (q j)) ≤ 1 / (q j : ℝ) := by
    simpa only [one_mul] using tailBound_inner_le (residueGap_tailBound (hq i))
      (residueGap_tailBound (hq j)) zero_le_one (hq j)
  have hid : inner ℝ limitResidual (∑ i ∈ Finset.range n, residueGap (q i)) =
      (n : ℝ) * ‖limitResidual‖ ^ 2 - correctedBlock k n := by
    rw [inner_sum]
    simp only [residueGap_pairing, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, correctedBlock, q]
  rw [← hid]
  exact inner_sum_sq_bound limitResidual (fun i => residueGap (q i)) _ h n

/-! ## Absolute summability at adjacent products -/

/-- The PNT logarithm makes the overlap weights at product conductors summable. -/
theorem adjacent_product_weights_summable :
    Summable (fun j : ℕ => (2 * (j : ℝ) + 1) * (1 / ((P j * P (j + 1) : ℕ) : ℝ))) := by
  let f (j : ℕ) := (2 * (j : ℝ) + 1) * (1 / ((P j * P (j + 1) : ℕ) : ℝ))
  let g (j : ℕ) := 1 / ((j : ℝ) * (Real.log (2 * j)) ^ 2)
  have hg : Summable g := by
    simpa only [g, Real.rpow_two] using
      (RiemannResearch.Analysis.summable_log_power_majorant (p := 2) (by norm_num))
  obtain ⟨c, hc, hb⟩ :=
    RiemannResearch.NumberTheory.PrimeNumberTheorem.nth_prime_asymp.symm.isBigO.exists_pos
  have he : ∀ᶠ j : ℕ in atTop, f j ≤ (12 * c ^ 2) * g j := by
    filter_upwards [hb.bound, eventually_ge_atTop 2] with j h j2
    have hj : (2 : ℝ) ≤ j := by exact_mod_cast j2
    have hjp : 0 < (j : ℝ) := by linarith
    have hl : 0 ≤ Real.log j := Real.log_nonneg (by linarith)
    have hp : 0 < (P j : ℝ) := by
      exact_mod_cast (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime j).pos
    have hx : 0 < (P (j + 1) : ℝ) := by
      exact_mod_cast (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _).pos
    have hpq : (P j : ℝ) ≤ P (j + 1) := by
      exact_mod_cast ((Nat.nth_strictMono Nat.infinite_setOfPred_prime) (Nat.lt_succ_self j)).le
    change ‖(j : ℝ) * Real.log j‖ ≤ c * ‖(P j : ℝ)‖ at h
    rw [Real.norm_of_nonneg (mul_nonneg hjp.le hl), Real.norm_of_nonneg hp.le] at h
    have hlog : Real.log (2 * (j : ℝ)) ≤ 2 * Real.log j := by
      rw [Real.log_mul (by norm_num) hjp.ne']
      linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hj]
    have hL : 0 < Real.log (2 * (j : ℝ)) := Real.log_pos (by linarith)
    have hprod : (j : ℝ) * Real.log (2 * j) ≤ 2 * c * P j := by
      nlinarith only [mul_le_mul_of_nonneg_left hlog hjp.le, h]
    have hsq := (sq_le_sq₀ (mul_nonneg hjp.le hL.le) (by positivity)).2 hprod
    dsimp [f, g]
    rw [Nat.cast_mul, mul_one_div, mul_one_div,
      div_le_div_iff₀ (mul_pos hp hx) (mul_pos hjp (sq_pos_of_pos hL))]
    calc
      _ ≤ (3 * (j : ℝ)) * ((j : ℝ) * Real.log (2 * j) ^ 2) := by
        apply mul_le_mul_of_nonneg_right (by linarith)
        positivity
      _ = 3 * ((j : ℝ) * Real.log (2 * j)) ^ 2 := by ring
      _ ≤ 3 * (2 * c * P j) ^ 2 := by linarith only [hsq]
      _ = (12 * c ^ 2) * ((P j : ℝ) * P j) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpq hp.le) (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1 he
  change Summable f
  apply (summable_nat_add_iff N).mp
  exact Summable.of_nonneg_of_le (fun j => by dsimp [f]; positivity)
    (fun j => hN (j + N) (Nat.le_add_left N j))
    ((summable_nat_add_iff N).mpr (hg.mul_left (12 * c ^ 2)))

private def physicalAbs (v : ThresholdHilbert) : ThresholdHilbert :=
  sequenceHilbert (fun m => |hilbertSequence v m|)
    (by simpa only [sq_abs] using hilbertSequence_square_summable v)

private theorem physicalAbs_coords (v : ThresholdHilbert) (m : ℕ) :
    hilbertSequence (physicalAbs v) m = |hilbertSequence v m| := by
  unfold physicalAbs
  rw [hilbertSequence_sequenceHilbert _ _ (by simp)]

private theorem norm_physicalAbs (v : ThresholdHilbert) : ‖physicalAbs v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [hilbert_norm_weighted_sq, physicalAbs_coords, sq_abs]

private theorem abs_inner_le_inner_physicalAbs (v x : ThresholdHilbert)
    (hx : ∀ m, 0 ≤ hilbertSequence x m) : |inner ℝ v x| ≤ inner ℝ (physicalAbs v) x := by
  let f (m : ℕ) := positiveWeight m * (hilbertSequence v m * hilbertSequence x m)
  let g (m : ℕ) := positiveWeight m * (hilbertSequence (physicalAbs v) m * hilbertSequence x m)
  have hf : Summable f := weighted_product_summable_of_square
    (hilbertSequence_square_summable _) (hilbertSequence_square_summable _)
  have hg : Summable g := weighted_product_summable_of_square
    (hilbertSequence_square_summable _) (hilbertSequence_square_summable _)
  have hab (m) : |f m| = g m := by
    simp only [f, g, physicalAbs_coords, abs_mul, abs_of_nonneg (positiveWeight_nonneg m),
      abs_of_nonneg (hx m)]
  rw [hilbert_inner_weighted, hilbert_inner_weighted]
  change |∑' m, f m| ≤ ∑' m, g m
  apply abs_le.mpr
  constructor
  · apply neg_le.mp
    rw [← tsum_neg]
    exact hf.neg.tsum_le_tsum (fun m => (neg_le_abs (f m)).trans_eq (hab m)) hg
  · exact hf.tsum_le_tsum (fun m => (le_abs_self _).trans_eq (hab m)) hg

/-- Absolute errors, with no cancellation among product conductors. -/
theorem productBlock_abs_error_sq_le (k n : ℕ) :
    (∑ j ∈ Finset.range n,
      |‖limitResidual‖ ^ 2 - reciprocalResiduePairing (P (k + j) * P (k + j + 1))|) ^ 2 ≤
      ‖limitResidual‖ ^ 2 * productBlockWeight k n := by
  let q j := P (k + j) * P (k + j + 1)
  have hq j : 0 < q j := Nat.mul_pos
    (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _).pos
    (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _).pos
  have hs := Finset.sum_le_sum (s := Finset.range n) (fun i _ =>
    abs_inner_le_inner_physicalAbs limitResidual (residueGap (q i))
      (fun m => (residueGap_tailBound (hq i) m).1))
  rw [← inner_sum] at hs
  simp only [residueGap_pairing] at hs
  have hz : 0 ≤ ∑ i ∈ Finset.range n, |‖limitResidual‖ ^ 2 - reciprocalResiduePairing (q i)| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ((sq_le_sq₀ hz (hz.trans hs)).2 hs).trans ?_
  have h i j (_ : i ≤ j) :
      inner ℝ (residueGap (q i)) (residueGap (q j)) ≤ 1 / (q j : ℝ) := by
    simpa only [one_mul] using tailBound_inner_le (residueGap_tailBound (hq i))
      (residueGap_tailBound (hq j)) zero_le_one (hq j)
  simpa only [norm_physicalAbs, productBlockWeight, q] using
    inner_sum_sq_bound (physicalAbs limitResidual) (fun i => residueGap (q i)) _ h n

/-- Squared envelope for the entire family of consecutive prime products. -/
def productWeightTotal : ℝ :=
  ∑' j : ℕ, (2 * (j : ℝ) + 1) * (1 / ((P j * P (j + 1) : ℕ) : ℝ))

theorem productBlockWeight_le_total (k n : ℕ) : productBlockWeight k n ≤ productWeightTotal := by
  unfold productBlockWeight productWeightTotal
  refine (Finset.sum_le_sum (fun j (_ : j ∈ Finset.range n) => ?_)).trans
    (adjacent_product_weights_summable.sum_le_tsum (Finset.range n) (fun j _ => by positivity))
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hp : 0 < P j * P (j + 1) := Nat.mul_pos
    (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime j).pos
    (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (j + 1)).pos
  apply one_div_le_one_div_of_le (by exact_mod_cast hp)
  exact_mod_cast (Nat.mul_le_mul
    ((Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone (Nat.le_add_left j k))
    ((Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone (by omega : j + 1 ≤ k + j + 1)))

theorem adjacent_product_errors_summable :
    Summable (fun j : ℕ => |‖limitResidual‖ ^ 2 - reciprocalResiduePairing (P j * P (j + 1))|) := by
  apply summable_of_sum_range_le (fun _ => abs_nonneg _)
    (c := Real.sqrt (‖limitResidual‖ ^ 2 * productWeightTotal))
  intro n
  have h := (productBlock_abs_error_sq_le 0 n).trans
    (mul_le_mul_of_nonneg_left (productBlockWeight_le_total 0 n) (sq_nonneg _))
  simpa only [zero_add, Real.sqrt_sq (Finset.sum_nonneg (fun _ _ => abs_nonneg _))] using
    Real.sqrt_le_sqrt h

/-! ## Sign certificates for the residual energy -/

private theorem energy_times_sq_le_of_sign {n W z : ℝ} (hn : 0 ≤ n) (hW : 0 ≤ W) (hz : 0 ≤ z)
    (h : (z + n * ‖limitResidual‖ ^ 2) ^ 2 ≤ ‖limitResidual‖ ^ 2 * W) :
    n ^ 2 * ‖limitResidual‖ ^ 2 ≤ W := by
  by_cases hd : ‖limitResidual‖ = 0
  · simpa [hd] using hW
  have he := sq_pos_of_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd))
  have hsq := (sq_le_sq₀ (mul_nonneg hn he.le) (add_nonneg hz (mul_nonneg hn he.le))).2
    (le_add_of_nonneg_left hz)
  by_contra! hbad
  nlinarith only [hsq.trans h, mul_pos he (sub_pos.mpr hbad)]

theorem energy_le_of_nonnegative_signed_block {k n : ℕ} (hn : 0 < n)
    (hs : 0 ≤ cumulative (k + n) - cumulative k) :
    ‖limitResidual‖ ^ 2 ≤ (4 * blockWeight k n) / (n : ℝ) ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos (Nat.cast_pos.mpr hn))).2
  rw [mul_comm]
  apply energy_times_sq_le_of_sign (Nat.cast_nonneg n) _ hs (block_error_sq_le_odd_weights k n)
  unfold blockWeight
  positivity

theorem energy_le_of_correctedBlock_nonpos {k n : ℕ} (hn : 0 < n) (hs : correctedBlock k n ≤ 0) :
    ‖limitResidual‖ ^ 2 ≤ productBlockWeight k n / (n : ℝ) ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos (Nat.cast_pos.mpr hn))).2
  rw [mul_comm]
  have hW : 0 ≤ productBlockWeight k n := by unfold productBlockWeight; positivity
  apply energy_times_sq_le_of_sign (Nat.cast_nonneg n) hW (neg_nonneg.mpr hs)
  simpa only [sub_eq_add_neg, add_comm] using correctedBlock_error_sq_le k n

theorem riemannHypothesis_iff_frequently_correctedBlock_nonpos :
    RiemannHypothesis ↔ ∃ᶠ n : ℕ in atTop, ∃ k : ℕ, correctedBlock k n ≤ 0 := by
  have heq : RiemannHypothesis ↔ limitResidual = 0 :=
    (riemannHypothesis_iff_naturalApproximation.trans
      BaezDuarte.naturalApproximation_iff_one_mem).trans
      (limitResidual_zero_iff_energy_zero.trans limitEnergy_zero_iff_mem).symm
  rw [heq]
  constructor
  · intro hd
    exact (Eventually.of_forall (fun n : ℕ => (show ∃ k : ℕ, correctedBlock k n ≤ 0 from
      ⟨0, by simp [correctedBlock, reciprocalResiduePairing, hd]⟩))).frequently
  · intro h
    by_contra hd
    have hE := sq_pos_of_pos (norm_pos_iff.mpr hd)
    have ht : Tendsto (fun n : ℕ => productWeightTotal / (n : ℝ) ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        ((tendsto_pow_atTop (by decide : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop)
    obtain ⟨n, ⟨k, hk⟩, hn, hc⟩ := (h.and_eventually
      ((eventually_ge_atTop 1).and (ht.eventually (Iio_mem_nhds hE)))).exists
    have hbound := (energy_le_of_correctedBlock_nonpos (by omega : 0 < n) hk).trans
      (div_le_div_of_nonneg_right (productBlockWeight_le_total k n) (sq_nonneg _))
    exact (not_lt_of_ge hbound) hc

theorem doubling_sign_energy_le {a : ℕ} (ha : 0 < a) (k : ℕ)
    (h : 2 * reciprocalResiduePairing (a ^ k) ≤ reciprocalResiduePairing (a ^ (2 * k))) :
    ‖limitResidual‖ ^ 2 ≤ 4 / ((a ^ k : ℕ) : ℝ) := by
  have hd : 0 ≤ residueDefect (a ^ k) (a ^ k) := by
    rw [residueDefect, ← pow_add]
    rw [two_mul] at h
    simp only [two_mul] at h
    linarith
  refine (energy_le_of_residueDefect_nonneg (pow_pos ha k) le_rfl hd).trans_eq ?_
  ring

/-- Total variation along a divisibility chain is controlled by its first remaining tail. -/
theorem power_residue_variation_sq_le {a : ℕ} (ha : 0 < a) (k n : ℕ) :
    (∑ i ∈ Finset.range n, |reciprocalResiduePairing (a ^ (k + i + 1)) -
      reciprocalResiduePairing (a ^ (k + i))|) ^ 2 ≤
      ‖limitResidual‖ ^ 2 / ((a ^ k : ℕ) : ℝ) := by
  let H (i : ℕ) := residueGap (a ^ (k + i))
  let v := physicalAbs limitResidual
  have hH (i m : ℕ) : 0 ≤ hilbertSequence (H i - H (i + 1)) m := by
    simp only [hilbertSequence_sub, Pi.sub_apply]
    apply sub_nonneg.mpr
    apply residueGap_antitone_of_dvd (pow_pos ha _) (pow_pos ha _)
    exact pow_dvd_pow a (by omega)
  have hstep (i : ℕ) : |reciprocalResiduePairing (a ^ (k + i + 1)) -
      reciprocalResiduePairing (a ^ (k + i))| ≤ inner ℝ v (H i) - inner ℝ v (H (i + 1)) := by
    have h := abs_inner_le_inner_physicalAbs limitResidual (H i - H (i + 1)) (hH i)
    rw [inner_sub_right, inner_sub_right] at h
    simpa only [H, residueGap_pairing, Nat.add_assoc, sub_sub_sub_cancel_left, v] using h
  have hs := Finset.sum_le_sum (s := Finset.range n) (fun i _ => hstep i)
  have htel : (∑ i ∈ Finset.range n, (inner ℝ v (H i) - inner ℝ v (H (i + 1)))) =
      inner ℝ v (H 0) - inner ℝ v (H n) := by
    clear hs
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; ring
  rw [htel] at hs
  have hpos : 0 ≤ inner ℝ v (H n) := (abs_nonneg _).trans
    (abs_inner_le_inner_physicalAbs limitResidual (H n)
      (fun m => (residueGap_tailBound (pow_pos ha _) m).1))
  have hnorm := (le_abs_self _).trans (abs_real_inner_le_norm v (H 0))
  have hb := (hs.trans (sub_le_self _ hpos)).trans hnorm
  refine ((sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by positivity)).2 hb).trans ?_
  simp only [mul_pow, v, norm_physicalAbs]
  have hh := tailBound_inner_le (residueGap_tailBound (pow_pos ha k))
    (residueGap_tailBound (pow_pos ha k)) zero_le_one (pow_pos ha k)
  rw [real_inner_self_eq_norm_sq, one_mul] at hh
  simpa only [v, H, add_zero, mul_one_div] using
    mul_le_mul_of_nonneg_left hh (sq_nonneg ‖limitResidual‖)

/-- info:
'RiemannResearch.RH.Pareto.PrimePowerSchur.SemiprimeFekete.residueDefect_centered'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms residueDefect_centered

/-- info:
'RiemannResearch.RH.Pareto.PrimePowerSchur.SemiprimeFekete.rightZero_bound_of_residueDefect_nonneg'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rightZero_bound_of_residueDefect_nonneg

/-- info:
'RiemannResearch.RH.Pareto.PrimePowerSchur.SemiprimeFekete.block_error_sq_le_odd_weights'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms block_error_sq_le_odd_weights

/-- info:
'RiemannResearch.RH.Pareto.PrimePowerSchur.SemiprimeFekete.productBlock_abs_error_sq_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms productBlock_abs_error_sq_le

/-- info:
'RiemannResearch.RH.Pareto.PrimePowerSchur.SemiprimeFekete.adjacent_product_errors_summable'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms adjacent_product_errors_summable

/-- info:
'RiemannResearch.RH.Pareto.PrimePowerSchur.SemiprimeFekete.energy_le_of_nonnegative_signed_block'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms energy_le_of_nonnegative_signed_block

/-- info:
'RiemannResearch.RH.Pareto.PrimePowerSchur.SemiprimeFekete.energy_le_of_correctedBlock_nonpos'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms energy_le_of_correctedBlock_nonpos

/-- info:
'RiemannResearch.RH.Pareto.PrimePowerSchur.SemiprimeFekete.riemannHypothesis_iff_frequently_correctedBlock_nonpos'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms riemannHypothesis_iff_frequently_correctedBlock_nonpos

/-- info:
'RiemannResearch.RH.Pareto.PrimePowerSchur.SemiprimeFekete.doubling_sign_energy_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms doubling_sign_energy_le

/-- info:
'RiemannResearch.RH.Pareto.PrimePowerSchur.SemiprimeFekete.power_residue_variation_sq_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms power_residue_variation_sq_le


end RiemannResearch.RH.Pareto.PrimePowerSchur.SemiprimeFekete
