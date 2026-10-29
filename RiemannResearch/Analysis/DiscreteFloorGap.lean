/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Inverse - square energy of a difference of integer quotients

Source: the user - provided minimum - energy remaining - obligations handoff,
29 October 2026. The elementary interval - counting argument was developed
in this continuation. Intervals may overlap: their multiplicities are
retained in the exact floor - gap identity before any upper estimate.
The RH application is QCompensatedResidueGap.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.DiscreteFloorGap

theorem floor_gap_count (n r k J : ℕ) (hn : 0 < n) (hnr : n ≤ r)
    (hk : k < J * n) :
    (((k / n : ℕ) : ℝ) - ((k / r : ℕ) : ℝ)) =
      ∑ j ∈ Finset.range J, if 0 < j ∧ j * n ≤ k ∧ k < j * r then (1 : ℝ) else 0 := by
  have hr : 0 < r := lt_of_lt_of_le hn hnr
  have hle : k / r ≤ k / n := Nat.div_le_div_left hnr hn
  have ha : k / n < J := (Nat.div_lt_iff_lt_mul hn).mpr hk
  rw [Finset.sum_boole]
  have he : {j ∈ Finset.range J | 0 < j ∧ j * n ≤ k ∧ k < j * r} =
      Finset.Icc (k / r + 1) (k / n) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    rw [← Nat.le_div_iff_mul_le hn, ← Nat.div_lt_iff_lt_mul hr]
    have hb0 := Nat.zero_le (k / r)
    omega
  rw [he, Nat.card_Icc]
  have hc : k / n + 1 - (k / r + 1) = k / n - k / r := by omega
  rw [hc, Nat.cast_sub hle]

theorem band_energy_le (n r j K : ℕ) (hn : 0 < n) (hnr : n ≤ r)
    (hj : 0 < j) :
    (∑ k ∈ Finset.range K,
      if j * n ≤ k ∧ k < j * r then (1 : ℝ) / (k : ℝ) ^ 2 else 0) ≤
        ((r : ℝ) - n) / ((j : ℝ) * (n : ℝ) ^ 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hle : j * n ≤ j * r := Nat.mul_le_mul_left j hnr
  have hsum : (∑ k ∈ Finset.range K,
      if j * n ≤ k ∧ k < j * r then (1 : ℝ) / (k : ℝ) ^ 2 else 0) ≤
      ∑ k ∈ Finset.Ico (j * n) (j * r), (1 : ℝ) / (k : ℝ) ^ 2 := by
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      exact Finset.mem_Ico.mpr (Finset.mem_filter.mp hk).2
    · intro k hk _
      positivity
  refine hsum.trans ?_
  calc
    (∑ k ∈ Finset.Ico (j * n) (j * r), (1 : ℝ) / (k : ℝ) ^ 2) ≤
        ∑ k ∈ Finset.Ico (j * n) (j * r), (1 : ℝ) / ((j : ℝ) * n) ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      have hkR : (j : ℝ) * n ≤ k := by exact_mod_cast (Finset.mem_Ico.mp hk).1
      exact one_div_le_one_div_of_le (sq_pos_of_pos (mul_pos hjR hnR))
        ((sq_le_sq₀ (by positivity) (by positivity)).mpr hkR)
    _ = ((r : ℝ) - n) / ((j : ℝ) * (n : ℝ) ^ 2) := by
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico, Nat.cast_sub hle,
        Nat.cast_mul]
      field_simp


theorem floor_gap_sum_le (n r J K : ℕ) (hn : 0 < n) (hnr : n ≤ r)
    (hK : K ≤ J * n) :
    (∑ k ∈ Finset.range K,
      (((k / n : ℕ) : ℝ) - ((k / r : ℕ) : ℝ)) / (k : ℝ) ^ 2) ≤
      ∑ j ∈ Finset.range J, ((r : ℝ) - n) / ((j : ℝ) * (n : ℝ) ^ 2) := by
  calc
    _ = ∑ k ∈ Finset.range K, ∑ j ∈ Finset.range J,
        if 0 < j ∧ j * n ≤ k ∧ k < j * r then (1 : ℝ) / (k : ℝ) ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [floor_gap_count n r k J hn hnr (lt_of_lt_of_le (Finset.mem_range.mp hk) hK),
        Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs <;> simp
    _ = ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range K,
        if 0 < j ∧ j * n ≤ k ∧ k < j * r then (1 : ℝ) / (k : ℝ) ^ 2 else 0 :=
      Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hj0 : 0 < j
      · simpa only [hj0, true_and] using band_energy_le n r j K hn hnr hj0
      · have hjz : j = 0 := by omega
        subst j
        simp

/-- Sharper complete-tail majorant using the integer cutoff's lower bound two. -/
theorem gap_tail_sharp (n r j : ℝ) (hn : 1 ≤ n) (hnr : n < r)
    (hr2 : r ≤ 2 * n) (hj : 2 ≤ j)
    (hl : n ≤ j * (r - n)) :
    (r / n) ^ 2 / (j * n) ≤ (9 / 4 : ℝ) * ((r - n) / n ^ 2) := by
  have hn0 : 0 < n := by linarith
  have hj0 : 0 < j := by linarith
  have hd : 0 ≤ r - n := by linarith
  have hp : r ^ 2 ≤ (9 / 4 : ℝ) * n * (j * (r - n)) := by
    by_cases hsmall : r ≤ 3 / 2 * n
    · have hm := mul_le_mul_of_nonneg_left hl hn0.le
      nlinarith [sq_nonneg (3 / 2 * n - r)]
    · have hm := mul_le_mul_of_nonneg_right hj hd
      have hm2 := mul_le_mul_of_nonneg_left hm hn0.le
      have hx := mul_nonneg (show 0 ≤ (r - n) - n / 2 by linarith)
        (show 0 ≤ n - (r - n) by linarith)
      nlinarith
  apply (div_le_iff₀ (mul_pos hj0 hn0)).mpr
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hn0)).mpr
  field_simp
  nlinarith

theorem gap_majorant_log (n r j : ℝ) (hn : 1 ≤ n) (hnr : n < r)
    (hr2 : r ≤ 2 * n) (hj : 0 < j) (hj2 : 2 ≤ j)
    (hl : n ≤ j * (r - n)) (hu : j * (r - n) ≤ r) :
    (r - n) / n ^ 2 * (1 + Real.log j) + (j * n + 1) * ((r - n) / (n * r)) ^ 2 + (r / n) ^ 2 / (j * n) ≤
        (r - n) / n ^ 2 * ((21 / 4 : ℝ) + Real.log (n / (r - n))) := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hr0 : 0 < r := hn0.trans hnr
  have hd : 0 < r - n := sub_pos.mpr hnr
  have hw : 0 ≤ (r - n) / n ^ 2 := by positivity
  have hlog : Real.log j ≤ 1 + Real.log (n / (r - n)) := by
    have hjle : j ≤ 2 * (n / (r - n)) := by
      calc
        j ≤ (2 * n) / (r - n) := (le_div_iff₀ hd).mpr (hu.trans hr2)
        _ = 2 * (n / (r - n)) := by ring
    have he := Real.log_le_log hj hjle
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt (div_pos hn0 hd))] at he
    have htwo : Real.log (2 : ℝ) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    linarith
  have hs : (j * n + 1) * ((r - n) / (n * r)) ^ 2 ≤ (r - n) / n ^ 2 := by
    have hp : (j * n + 1) * (r - n) ≤ r ^ 2 := by
      have := mul_le_mul_of_nonneg_right hu hn0.le
      nlinarith
    have hratio : (j * n + 1) * (r - n) / r ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos hr0)).mpr hp
    have h := mul_le_mul_of_nonneg_left hratio hw
    calc
      (j * n + 1) * ((r - n) / (n * r)) ^ 2 =
          ((r - n) / n ^ 2) * ((j * n + 1) * (r - n) / r ^ 2) := by
        simp only [div_pow, mul_pow, div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ ((r - n) / n ^ 2) * 1 := h
      _ = (r - n) / n ^ 2 := mul_one _
  have ht := gap_tail_sharp n r j hn hnr hr2 hj2 hl
  have hh := mul_le_mul_of_nonneg_left hlog hw
  nlinarith


end RiemannResearch.Analysis.DiscreteFloorGap
