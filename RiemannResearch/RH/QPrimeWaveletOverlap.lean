/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.RH.QDivisorWaveletFactorization
import RiemannResearch.RH.QPrimePowerOrthogonal
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact local spectral masses and absolute overlap

Source: user-provided QDPP_Finite_Rank_and_Moving_Window_Analysis_2026-10-14,
Sections 4 and 7. This module verifies the local prime-exponent calculation,
its normalization, signed support, and absolute overlap. The global infinite
prime-product construction is a separate obligation.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.ZetaTwoProbability
theorem geometricWavelet_eq_weight (p a v : ℕ) (ha : a ≤ v) :
    geometricWavelet p a v = valuationWaveletWeight p a := by
  cases a with
  | zero => rfl
  | succ a =>
    simp [geometricWavelet, valuationWaveletWeight, ha, show a ≤ v by omega]
theorem geometricWavelet_last (p v : ℕ) :
    geometricWavelet p (v + 1) v = -((p : ℝ) ^ v) ^ 2 := by
  simp [geometricWavelet]
theorem geometricWavelet_above (p a v : ℕ) (ha : v + 1 < a) :
    geometricWavelet p a v = 0 := by
  cases a with
  | zero => omega
  | succ a =>
    simp [geometricWavelet, show ¬a + 1 ≤ v by omega, show ¬a ≤ v by omega]
theorem sum_valuationWaveletWeight (p v : ℕ) :
    (∑ a ∈ Finset.range (v + 1), valuationWaveletWeight p a) = ((p : ℝ) ^ v) ^ 2 := by
  induction v with
  | zero => simp [valuationWaveletWeight]
  | succ v ih =>
    rw [Finset.sum_range_succ, ih]
    simp [valuationWaveletWeight]
theorem abs_geometricWavelet_le_weight (p a v : ℕ) (hp : p.Prime) :
    |geometricWavelet p a v| ≤ valuationWaveletWeight p a := by
  have hw := RiemannResearch.RH.ZetaTwoHilbert.qValuationWaveletWeight_pos p a hp
  by_cases ha : a ≤ v
  · rw [geometricWavelet_eq_weight p a v ha, abs_of_pos hw]
  · by_cases hb : a = v + 1
    · subst a
      rw [geometricWavelet_last, abs_neg, abs_of_nonneg (sq_nonneg _), valuationWaveletWeight_succ]
      have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      have hfac : (1 : ℝ) ≤ (p : ℝ) ^ 2 - 1 := by nlinarith
      exact le_mul_of_one_le_right (sq_nonneg _) hfac
    · rw [geometricWavelet_above p a v (by omega), abs_zero]
      exact hw.le
def reversePrimeMass (p v a : ℕ) : ℝ :=
  (1 - 1 / (p : ℝ) ^ 2) / ((p : ℝ) ^ v) ^ 2 *
    (geometricWavelet p a v ^ 2 / valuationWaveletWeight p a)
theorem reversePrimeMass_last (p v : ℕ) (hp : p.Prime) :
    reversePrimeMass p v (v + 1) = 1 / (p : ℝ) ^ 2 := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hden : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  rw [reversePrimeMass, geometricWavelet_last, valuationWaveletWeight_succ]
  field_simp [hp0, hden]
theorem reversePrimeMass_below (p v a : ℕ) (hp : p.Prime) (ha : a ≤ v) :
    reversePrimeMass p v a =
      (1 - 1 / (p : ℝ) ^ 2) / ((p : ℝ) ^ v) ^ 2 * valuationWaveletWeight p a := by
  rw [reversePrimeMass, geometricWavelet_eq_weight p a v ha]
  have hw : valuationWaveletWeight p a ≠ 0 :=
    ne_of_gt (RiemannResearch.RH.ZetaTwoHilbert.qValuationWaveletWeight_pos p a hp)
  field_simp
theorem reversePrimeMass_sum (p v : ℕ) (hp : p.Prime) :
    (∑ a ∈ Finset.range (v + 2), reversePrimeMass p v a) = 1 := by
  rw [show v + 2 = (v + 1) + 1 by omega, Finset.sum_range_succ, reversePrimeMass_last p v hp]
  have he : (∑ a ∈ Finset.range (v + 1), reversePrimeMass p v a) =
      (1 - 1 / (p : ℝ) ^ 2) / ((p : ℝ) ^ v) ^ 2 *
      ((p : ℝ) ^ v) ^ 2 := by
    calc
      _ = (1 - 1 / (p : ℝ) ^ 2) / ((p : ℝ) ^ v) ^ 2 *
          ∑ a ∈ Finset.range (v + 1), valuationWaveletWeight p a := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        exact reversePrimeMass_below p v a hp (by have := Finset.mem_range.mp ha; omega)
      _ = _ := by rw [sum_valuationWaveletWeight]
  rw [he]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  field_simp [hp0]
  ring

theorem valuationWaveletWeight_le_pow (p a : ℕ) :
    valuationWaveletWeight p a ≤ ((p : ℝ) ^ a) ^ 2 := by
  cases a with
  | zero => simp [valuationWaveletWeight]
  | succ a => exact sub_le_self _ (sq_nonneg _)
def localAbsoluteOverlap (p v w : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (min v w + 2),
    |geometricWavelet p a v * geometricWavelet p a w| / valuationWaveletWeight p a
theorem localAbsoluteOverlap_lt (p v w : ℕ) (hp : p.Prime) (hvw : v < w) :
    localAbsoluteOverlap p v w = 2 * ((p : ℝ) ^ v) ^ 2 := by
  unfold localAbsoluteOverlap
  rw [min_eq_left hvw.le, show v + 2 = (v + 1) + 1 by omega, Finset.sum_range_succ]
  have he : (∑ a ∈ Finset.range (v + 1),
      |geometricWavelet p a v * geometricWavelet p a w| / valuationWaveletWeight p a) =
      ((p : ℝ) ^ v) ^ 2 := by
    rw [← sum_valuationWaveletWeight p v]
    apply Finset.sum_congr rfl
    intro a ha
    have hav : a ≤ v := by have := Finset.mem_range.mp ha; omega
    rw [geometricWavelet_eq_weight p a v hav,
      geometricWavelet_eq_weight p a w (hav.trans hvw.le)]
    have hw := RiemannResearch.RH.ZetaTwoHilbert.qValuationWaveletWeight_pos p a hp
    rw [abs_of_nonneg (mul_nonneg hw.le hw.le), mul_div_cancel_right₀ _ (ne_of_gt hw)]
  rw [he, geometricWavelet_last,
    geometricWavelet_eq_weight p (v + 1) w (by omega), abs_mul, abs_neg,
    abs_of_nonneg (sq_nonneg _),
    abs_of_pos (RiemannResearch.RH.ZetaTwoHilbert.qValuationWaveletWeight_pos p (v+1) hp),
    mul_div_cancel_right₀ _ (ne_of_gt
      (RiemannResearch.RH.ZetaTwoHilbert.qValuationWaveletWeight_pos p (v+1) hp))]
  ring
theorem localAbsoluteOverlap_self (p v : ℕ) (hp : p.Prime) :
    localAbsoluteOverlap p v v =
      ((p : ℝ) ^ v) ^ 2 * (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1) := by
  unfold localAbsoluteOverlap
  rw [min_self, show v + 2 = (v + 1) + 1 by omega, Finset.sum_range_succ]
  have he : (∑ a ∈ Finset.range (v + 1),
      |geometricWavelet p a v * geometricWavelet p a v| / valuationWaveletWeight p a) =
      ((p : ℝ) ^ v) ^ 2 := by
    rw [← sum_valuationWaveletWeight p v]
    apply Finset.sum_congr rfl
    intro a ha
    rw [geometricWavelet_eq_weight p a v (by have := Finset.mem_range.mp ha; omega)]
    have hw := RiemannResearch.RH.ZetaTwoHilbert.qValuationWaveletWeight_pos p a hp
    rw [abs_of_nonneg (mul_nonneg hw.le hw.le), mul_div_cancel_right₀ _ (ne_of_gt hw)]
  rw [he, geometricWavelet_last, neg_mul_neg, abs_of_nonneg (mul_self_nonneg _),
    valuationWaveletWeight_succ]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hden : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  field_simp [hp0, hden]
  ring
theorem geometricWavelet_product_above (p a v w : ℕ) (ha : min v w + 1 < a) :
    geometricWavelet p a v * geometricWavelet p a w = 0 := by
  rcases le_total v w with h | h
  · rw [geometricWavelet_above p a v (by simpa [min_eq_left h] using ha), zero_mul]
  · rw [geometricWavelet_above p a w (by simpa [min_eq_right h] using ha), mul_zero]

theorem reversePrimeMass_nonneg (p v a : ℕ) (hp : p.Prime) :
    0 ≤ reversePrimeMass p v a := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hh : 0 ≤ 1 - 1 / (p : ℝ)^2 := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ (sq_pos_of_pos (by linarith : (0 : ℝ) < p))).mpr
    nlinarith
  exact mul_nonneg (div_nonneg hh (sq_nonneg _))
    (div_nonneg (sq_nonneg _)
      (RiemannResearch.RH.ZetaTwoHilbert.qValuationWaveletWeight_pos p a hp).le)
theorem reversePrimeMass_above (p v a : ℕ) (ha : v + 1 < a) :
    reversePrimeMass p v a = 0 := by
  simp only [reversePrimeMass, geometricWavelet_above p a v ha, zero_pow (by norm_num : 2 ≠ 0),
    zero_div, mul_zero]
theorem reversePrimeMass_tsum (p v : ℕ) (hp : p.Prime) :
    (∑' a, reversePrimeMass p v a) = 1 := by
  calc
    _ = ∑ a ∈ Finset.range (v+2), reversePrimeMass p v a :=
      tsum_eq_sum (fun a ha => reversePrimeMass_above p v a
        (by simp only [Finset.mem_range] at ha; omega))
    _ = 1 := reversePrimeMass_sum p v hp
theorem localAbsoluteOverlap_symm (p v w : ℕ) :
    localAbsoluteOverlap p v w = localAbsoluteOverlap p w v := by
  simp only [localAbsoluteOverlap, min_comm, mul_comm]
theorem geometricWavelet_absolute_overlap_tsum (p v w : ℕ) :
    (∑' a, |geometricWavelet p a v * geometricWavelet p a w| /
      valuationWaveletWeight p a) = localAbsoluteOverlap p v w := by
  apply tsum_eq_sum
  intro a ha
  rw [geometricWavelet_product_above p a v w
    (by simp only [Finset.mem_range] at ha; omega), abs_zero, zero_div]

end RiemannResearch.RH.ZetaTwoProbability
