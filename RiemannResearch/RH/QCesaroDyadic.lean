/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.DyadicBlockDecomposition
import RiemannResearch.RH.QCesaroEnergy
import RiemannResearch.RH.CesaroResidueMean
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega
/-!
# Complete dyadic Cesàro cumulative energy

Source: user-provided RH Cesàro P/Q squarefree research agenda, 1 November 2026,
Priority 3. The two-sided lower estimate is an elementary strengthening of
the proposed upper estimate. Every dyadic block and the exact finite head
remain in the primary equality. No arithmetic growth hypothesis is proved here.
-/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace RiemannResearch.RH.QCesaroDyadic
open QUniformMixture ZetaTwoProbability QCesaroEnergy ArithmeticCumulative
open Probability.ConditionalIID Analysis.DyadicBlockDecomposition

def qCumulativeWeight (n : ℕ) : ℝ :=
  (2 * (n : ℝ) + 1) / (zetaTwo * (n : ℝ)^3 * ((n : ℝ) + 1)^2)

theorem q_weight_cumulative (F : ℕ → ℝ) (n : ℕ) :
    qMixtureWeight n * cesaro F n ^ 2 =
      qCumulativeWeight n * cumulative F n ^ 2 := by
  rw [CesaroResidue.cesaro_eq_cumulative]
  by_cases hn : n = 0
  · simp [hn, qMixtureWeight, qCumulativeWeight]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  unfold qMixtureWeight qCumulativeWeight
  field_simp

theorem q_kernel_upper (n : ℕ) (hn : 0 < n) :
    qCumulativeWeight n ≤ 2 / (zetaTwo * (n : ℝ)^4) := by
  have h : 0 < (n : ℝ) := by exact_mod_cast hn
  have hz := zetaTwo_pos
  unfold qCumulativeWeight
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have hnz : 0 ≤ zetaTwo * (n : ℝ)^3 * (3*(n : ℝ)+2) := by positivity
  nlinarith only [hnz]

theorem q_kernel_lower (n : ℕ) (hn : 0 < n) :
    2 / (zetaTwo * ((n : ℝ)+1)^4) ≤ qCumulativeWeight n := by
  have h : 0 < (n : ℝ) := by exact_mod_cast hn
  have hz := zetaTwo_pos
  unfold qCumulativeWeight
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have hnz : 0 ≤ zetaTwo * ((n : ℝ)+1)^2 * (5*(n : ℝ)^2+4*(n : ℝ)+1) := by positivity
  nlinarith only [hnz]

theorem q_kernel_block (L n : ℕ) (hL : 0 < L) (hLn : L ≤ n) (hn : n < 2 * L) :
    1 / (8*zetaTwo*(L : ℝ)^4) ≤ qCumulativeWeight n ∧
      qCumulativeWeight n ≤ 2 / (zetaTwo*(L : ℝ)^4) := by
  have hLr : 0 < (L : ℝ) := by exact_mod_cast hL
  have hnr : 0 < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le hL hLn
  have hnl : (n : ℝ)+1 ≤ 2*(L : ℝ) := by exact_mod_cast hn
  have hln : (L : ℝ) ≤ n := by exact_mod_cast hLn
  have hz := zetaTwo_pos
  constructor
  · calc
      _ = 2/(zetaTwo*(2*(L : ℝ))^4) := by ring
      _ ≤ 2/(zetaTwo*((n : ℝ)+1)^4) := by gcongr
      _ ≤ _ := q_kernel_lower n (lt_of_lt_of_le hL hLn)
  · exact (q_kernel_upper n (lt_of_lt_of_le hL hLn)).trans (by gcongr)

theorem qCumulativeWeight_nonneg (n : ℕ) : 0 ≤ qCumulativeWeight n := by
  have hz := zetaTwo_pos
  unfold qCumulativeWeight
  positivity

/-- The exact normalized cumulative-square contribution of a full block. -/
def dyadicCumulativeBlock (F : ℕ → ℝ) (N k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (N * 2 ^ k),
    cumulative F (N * 2 ^ k + i) ^ 2 / ((N * 2 ^ k : ℕ) : ℝ) ^ 4

/-- Complete budget: all dyadic blocks are retained. -/
def dyadicCumulativeBudget (F : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑' k, dyadicCumulativeBlock F N k

theorem dyadicCumulativeBlock_nonneg (F : ℕ → ℝ) (N k : ℕ) :
    0 ≤ dyadicCumulativeBlock F N k :=
  Finset.sum_nonneg (fun _ _ => div_nonneg (sq_nonneg _) (by positivity))

theorem dyadicCumulativeBudget_nonneg (F : ℕ → ℝ) (N : ℕ) :
    0 ≤ dyadicCumulativeBudget F N :=
  tsum_nonneg (fun k => dyadicCumulativeBlock_nonneg F N k)

theorem cumulative_energy_summable (F : ℕ → ℝ)
    (hs : Summable (fun k => qMixtureWeight (k + 1) * cesaro F (k + 1) ^ 2)) :
    Summable (fun n => qCumulativeWeight n * cumulative F n ^ 2) := by
  apply (summable_nat_add_iff 1).mp
  exact hs.congr (fun k => q_weight_cumulative F (k + 1))

theorem qConditionalMeanSquare_eq_cumulative (F : ℕ → ℝ)
    (hs : Summable (fun k => qMixtureWeight (k + 1) * cesaro F (k + 1) ^ 2)) :
    qConditionalMeanSquare F = ∑' n, qCumulativeWeight n * cumulative F n ^ 2 := by
  have ht := (cumulative_energy_summable F hs).tsum_eq_zero_add
  simp only [cumulative_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add] at ht
  rw [ht]
  exact tsum_congr (fun k => q_weight_cumulative F (k + 1))

theorem dyadic_cumulative_block_bounds (F : ℕ → ℝ) (N k : ℕ) (hN : 0 < N) :
    (1 / (8 * zetaTwo)) * dyadicCumulativeBlock F N k ≤
      scaledDyadicBlock (fun n => qCumulativeWeight n * cumulative F n ^ 2) N k ∧
    scaledDyadicBlock (fun n => qCumulativeWeight n * cumulative F n ^ 2) N k ≤
      (2 / zetaTwo) * dyadicCumulativeBlock F N k := by
  have hL : 0 < N * 2 ^ k := Nat.mul_pos hN (pow_pos (by decide) _)
  have hLr : 0 < ((N * 2 ^ k : ℕ) : ℝ) := by exact_mod_cast hL
  have hz := zetaTwo_pos
  unfold dyadicCumulativeBlock scaledDyadicBlock
  constructor
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have h := (q_kernel_block (N * 2 ^ k) (N * 2 ^ k + i) hL
      (by omega) (by have := Finset.mem_range.mp hi; omega)).1
    have he : 1 / (8 * zetaTwo) *
        (cumulative F (N * 2 ^ k + i) ^ 2 / ((N * 2 ^ k : ℕ) : ℝ) ^ 4) =
        (1 / (8 * zetaTwo * ((N * 2 ^ k : ℕ) : ℝ) ^ 4)) *
          cumulative F (N * 2 ^ k + i) ^ 2 := by field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_right h (sq_nonneg _)
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have h := (q_kernel_block (N * 2 ^ k) (N * 2 ^ k + i) hL
      (by omega) (by have := Finset.mem_range.mp hi; omega)).2
    have he : (2 / zetaTwo) *
        (cumulative F (N * 2 ^ k + i) ^ 2 / ((N * 2 ^ k : ℕ) : ℝ) ^ 4) =
        (2 / (zetaTwo * ((N * 2 ^ k : ℕ) : ℝ) ^ 4)) *
          cumulative F (N * 2 ^ k + i) ^ 2 := by field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_right h (sq_nonneg _)

theorem dyadicCumulativeBlock_summable (F : ℕ → ℝ) (N : ℕ) (hN : 0 < N)
    (hs : Summable (fun k => qMixtureWeight (k + 1) * cesaro F (k + 1) ^ 2)) :
    Summable (dyadicCumulativeBlock F N) := by
  have hs0 := cumulative_energy_summable F hs
  have hn (n : ℕ) : 0 ≤ qCumulativeWeight n * cumulative F n ^ 2 :=
    mul_nonneg (qCumulativeWeight_nonneg n) (sq_nonneg _)
  have hb := summable_scaledDyadicBlock _ N hn hs0
  apply (hb.mul_left (8 * zetaTwo)).of_nonneg_of_le
    (fun k => dyadicCumulativeBlock_nonneg F N k)
  intro k
  have h := (dyadic_cumulative_block_bounds F N k hN).1
  have hz := zetaTwo_pos
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ 8 * zetaTwo by positivity)
  have he : (8 * zetaTwo) * ((1 / (8 * zetaTwo)) * dyadicCumulativeBlock F N k) =
      dyadicCumulativeBlock F N k := by field_simp
  rwa [he] at hm

theorem dyadic_cumulative_tail_bounds (F : ℕ → ℝ) (N : ℕ) (hN : 0 < N)
    (hs : Summable (fun k => qMixtureWeight (k + 1) * cesaro F (k + 1) ^ 2)) :
    (1 / (8 * zetaTwo)) * dyadicCumulativeBudget F N ≤
      ∑' k, scaledDyadicBlock (fun n => qCumulativeWeight n * cumulative F n ^ 2) N k ∧
    (∑' k, scaledDyadicBlock (fun n => qCumulativeWeight n * cumulative F n ^ 2) N k) ≤
      (2 / zetaTwo) * dyadicCumulativeBudget F N := by
  have hs0 := cumulative_energy_summable F hs
  have hb := summable_scaledDyadicBlock _ N
    (fun n => mul_nonneg (qCumulativeWeight_nonneg n) (sq_nonneg _)) hs0
  have hB := dyadicCumulativeBlock_summable F N hN hs
  constructor
  · have h := (hB.mul_left (1 / (8 * zetaTwo))).tsum_le_tsum
      (fun k => (dyadic_cumulative_block_bounds F N k hN).1) hb
    simpa only [tsum_mul_left, dyadicCumulativeBudget] using h
  · have h := hb.tsum_le_tsum
      (fun k => (dyadic_cumulative_block_bounds F N k hN).2) (hB.mul_left (2 / zetaTwo))
    simpa only [tsum_mul_left, dyadicCumulativeBudget] using h

def qHeadMass (H : ℕ) : ℝ := ∑ k ∈ Finset.range H, qMixtureWeight (k + 1)

theorem qHeadMass_nonneg (H : ℕ) : 0 ≤ qHeadMass H :=
  Finset.sum_nonneg (fun k _ => qMixtureWeight_nonneg (k + 1))

theorem qHeadMass_le_one (H : ℕ) : qHeadMass H ≤ 1 := by
  have h := hasSum_qMixtureWeight.summable.sum_le_tsum (Finset.range H)
    (fun k _ => qMixtureWeight_nonneg (k + 1))
  simpa only [hasSum_qMixtureWeight.tsum_eq, qHeadMass] using h

theorem cesaro_eq_of_constant_head (F : ℕ → ℝ) (c : ℝ) (n : ℕ) (hn : 0 < n)
    (hhead : ∀ m, 0 < m → m ≤ n → F m = c) : cesaro F n = c := by
  have he : cumulative F n = (n : ℝ) * c := by
    unfold cumulative
    calc
      _ = ∑ k ∈ Finset.range n, c := Finset.sum_congr rfl
        (fun k hk => hhead (k + 1) (by omega) (by have := Finset.mem_range.mp hk; omega))
      _ = _ := by simp
  rw [CesaroResidue.cesaro_eq_cumulative, he]
  exact mul_div_cancel_left₀ c (by positivity)

theorem cumulative_energy_head (F : ℕ → ℝ) (c : ℝ) (H : ℕ)
    (hhead : ∀ n, 0 < n → n ≤ H → F n = c) :
    (∑ n ∈ Finset.range (H + 1), qCumulativeWeight n * cumulative F n ^ 2) =
      c ^ 2 * qHeadMass H := by
  rw [Finset.sum_range_succ']
  simp only [cumulative_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
  unfold qHeadMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← q_weight_cumulative]
  have hm := cesaro_eq_of_constant_head F c (k + 1) (by omega)
    (fun m hm hmk => hhead m hm (by have := Finset.mem_range.mp hk; omega))
  rw [hm]
  ring

/-- Exact head plus every signed-input cumulative-square block. -/
theorem q_energy_head_dyadic_identity (F : ℕ → ℝ) (c : ℝ) (H : ℕ)
    (hs : Summable (fun k => qMixtureWeight (k + 1) * cesaro F (k + 1) ^ 2))
    (hhead : ∀ n, 0 < n → n ≤ H → F n = c) :
    qConditionalMeanSquare F = c ^ 2 * qHeadMass H +
      ∑' k, scaledDyadicBlock (fun n => qCumulativeWeight n * cumulative F n ^ 2)
        (H + 1) k := by
  have h := tsum_scaledDyadicBlock
    (fun n => qCumulativeWeight n * cumulative F n ^ 2) (H + 1) (by omega)
    (fun n => mul_nonneg (qCumulativeWeight_nonneg n) (sq_nonneg _))
    (cumulative_energy_summable F hs)
  rw [← qConditionalMeanSquare_eq_cumulative F hs, cumulative_energy_head F c H hhead] at h
  linarith

/-- Two-sided comparison with the complete budget; neither side omits a tail. -/
theorem q_energy_sub_head_dyadic_bounds (F : ℕ → ℝ) (c : ℝ) (H : ℕ)
    (hs : Summable (fun k => qMixtureWeight (k + 1) * cesaro F (k + 1) ^ 2))
    (hhead : ∀ n, 0 < n → n ≤ H → F n = c) :
    (1 / (8 * zetaTwo)) * dyadicCumulativeBudget F (H + 1) ≤
        qConditionalMeanSquare F - c ^ 2 * qHeadMass H ∧
    qConditionalMeanSquare F - c ^ 2 * qHeadMass H ≤
        (2 / zetaTwo) * dyadicCumulativeBudget F (H + 1) := by
  rw [q_energy_head_dyadic_identity F c H hs hhead, add_sub_cancel_left]
  exact dyadic_cumulative_tail_bounds F (H + 1) (by omega) hs

/-- The block constants survive normalization by any nonzero head,
without a lower bound on its amplitude. -/
theorem normalized_q_energy_sub_head_dyadic_bounds
    (F : ℕ → ℝ) (c : ℝ) (H : ℕ) (hc : c ≠ 0)
    (hs : Summable (fun k => qMixtureWeight (k + 1) * cesaro F (k + 1) ^ 2))
    (hhead : ∀ n, 0 < n → n ≤ H → F n = c) :
    (1 / (8 * zetaTwo)) * (dyadicCumulativeBudget F (H + 1) / |c| ^ 2) ≤
        qConditionalMeanSquare F / |c| ^ 2 - qHeadMass H ∧
    qConditionalMeanSquare F / |c| ^ 2 - qHeadMass H ≤
        (2 / zetaTwo) * (dyadicCumulativeBudget F (H + 1) / |c| ^ 2) := by
  have hc2 : 0 < |c| ^ 2 := sq_pos_of_ne_zero (abs_ne_zero.mpr hc)
  have h := q_energy_sub_head_dyadic_bounds F c H hs hhead
  have he : (qConditionalMeanSquare F - c ^ 2 * qHeadMass H) / |c| ^ 2 =
      qConditionalMeanSquare F / |c| ^ 2 - qHeadMass H := by
    rw [sq_abs]
    field_simp
  constructor
  · have hd := div_le_div_of_nonneg_right h.1 hc2.le
    rw [he] at hd
    simpa only [mul_div_assoc] using hd
  · have hd := div_le_div_of_nonneg_right h.2 hc2.le
    rw [he] at hd
    simpa only [mul_div_assoc] using hd

/-- Affine comparison of the normalized complete energy and block budget. -/
theorem normalized_dyadic_energy_bounds
    (F : ℕ → ℝ) (c : ℝ) (H : ℕ) (hc : c ≠ 0)
    (hs : Summable (fun k => qMixtureWeight (k + 1) * cesaro F (k + 1) ^ 2))
    (hhead : ∀ n, 0 < n → n ≤ H → F n = c) :
    dyadicCumulativeBudget F (H + 1) / |c| ^ 2 ≤
        (8 * zetaTwo) * (qConditionalMeanSquare F / |c| ^ 2) ∧
    qConditionalMeanSquare F / |c| ^ 2 ≤
        1 + (2 / zetaTwo) * (dyadicCumulativeBudget F (H + 1) / |c| ^ 2) := by
  have h := normalized_q_energy_sub_head_dyadic_bounds F c H hc hs hhead
  have hz := zetaTwo_pos
  constructor
  · have hm := mul_le_mul_of_nonneg_left h.1 (show 0 ≤ 8 * zetaTwo by positivity)
    have he : (8 * zetaTwo) * ((1 / (8 * zetaTwo)) *
        (dyadicCumulativeBudget F (H + 1) / |c| ^ 2)) =
        dyadicCumulativeBudget F (H + 1) / |c| ^ 2 := by field_simp
    rw [he] at hm
    have hp := mul_nonneg (show 0 ≤ 8 * zetaTwo by positivity) (qHeadMass_nonneg H)
    nlinarith
  · linarith [qHeadMass_le_one H]

end RiemannResearch.RH.QCesaroDyadic
