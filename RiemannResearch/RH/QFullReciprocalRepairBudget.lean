/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFullDilatedMobiusRepair
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Complete reciprocal repair energy and its exact dilation defect

Source: user-provided `Reciprocal_Head_Investigation_2026-11-07.md`, Section 3.
The physical reciprocal multiplier is denoted R in the paper convention; its
existing implementation is `QShiftedReciprocal.B`. It is not the density dQ/dP.
The complete infinite norm is retained. These bounds do not supply decay of
the product with the actual residual tail.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QFullDilatedMobiusRepair
open ZetaTwoHilbert ZetaTwoProbability QFloorDilation QMobiusExactHead

/-- Every reciprocal physical coordinate is controlled by its weighted source coordinate. -/
theorem reciprocal_sequence_square_le_weighted (f : QHilbert) (k : ℕ) :
    (qSequence (QShiftedReciprocal.B f) k) ^ 2 ≤
      zetaTwo * (positiveQWeight k * (qSequence f k) ^ 2) := by
  by_cases hk : k = 0
  · simp [hk]
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  rw [QShiftedReciprocal.qSequence_B, div_pow]
  calc
    (qSequence f k) ^ 2 / ((k : ℝ) + 1) ^ 2 ≤
        (qSequence f k) ^ 2 / (k : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hkR)
        (by nlinarith)
    _ = zetaTwo * (positiveQWeight k * (qSequence f k) ^ 2) := by
      unfold positiveQWeight
      field_simp [ne_of_gt zetaTwo_pos, ne_of_gt hkR]
      <;> ring

/-- The unweighted reciprocal physical sequence is square summable. -/
theorem reciprocal_sequence_square_summable (f : QHilbert) :
    Summable (fun k => (qSequence (QShiftedReciprocal.B f) k) ^ 2) :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (reciprocal_sequence_square_le_weighted f)
    ((qSequence_square_summable f).mul_left zetaTwo)

/-- Complete unweighted ℓ² control, with no head cutoff. -/
theorem reciprocal_sequence_square_tsum_le (f : QHilbert) :
    (∑' k, (qSequence (QShiftedReciprocal.B f) k) ^ 2) ≤
      zetaTwo * ‖f‖ ^ 2 := by
  rw [qNorm_weighted_sq, ← tsum_mul_left]
  exact Summable.tsum_le_tsum (reciprocal_sequence_square_le_weighted f)
    (reciprocal_sequence_square_summable f)
    ((qSequence_square_summable f).mul_left zetaTwo)

/-- Each finite physical subset inherits the complete bound. -/
theorem reciprocal_sequence_square_sum_le (f : QHilbert) (s : Finset ℕ) :
    (∑ k ∈ s, (qSequence (QShiftedReciprocal.B f) k) ^ 2) ≤
      zetaTwo * ‖f‖ ^ 2 :=
  ((reciprocal_sequence_square_summable f).sum_le_tsum s
    (fun k _ => sq_nonneg _)).trans (reciprocal_sequence_square_tsum_le f)

/-- The exact physical forward difference has finite energy at most four times
the complete reciprocal sequence energy. -/
theorem reciprocal_forward_difference_square_sum_le (f : QHilbert) (N : ℕ) :
    (∑ k ∈ Finset.range N,
      (qSequence (QShiftedReciprocal.B f) (k + 1) -
        qSequence (QShiftedReciprocal.B f) k) ^ 2) ≤
      4 * zetaTwo * ‖f‖ ^ 2 := by
  let u := qSequence (QShiftedReciprocal.B f)
  have hu : u 0 = 0 := qSequence_zero _
  have h0 : (∑ k ∈ Finset.range N, (u k) ^ 2) ≤ zetaTwo * ‖f‖ ^ 2 :=
    reciprocal_sequence_square_sum_le f _
  have h1 : (∑ k ∈ Finset.range N, (u (k + 1)) ^ 2) ≤ zetaTwo * ‖f‖ ^ 2 := by
    have h := reciprocal_sequence_square_sum_le f (Finset.range (N + 1))
    change (∑ k ∈ Finset.range (N + 1), (u k) ^ 2) ≤ _ at h
    simpa only [Finset.sum_range_succ', hu, zero_pow (by norm_num : 2 ≠ 0),
      add_zero] using h
  calc
    (∑ k ∈ Finset.range N, (u (k + 1) - u k) ^ 2) ≤
        ∑ k ∈ Finset.range N, (2 * (u (k + 1)) ^ 2 + 2 * (u k) ^ 2) := by
      apply Finset.sum_le_sum
      intro k hk
      nlinarith [sq_nonneg (u (k + 1) + u k)]
    _ = 2 * (∑ k ∈ Finset.range N, (u (k + 1)) ^ 2) +
        2 * (∑ k ∈ Finset.range N, (u k) ^ 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 4 * zetaTwo * ‖f‖ ^ 2 := by nlinarith

/-- Complete Gram trace of the explicit dilated steps. -/
def gramTrace (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, ‖dilatedMobiusStep N k‖ ^ 2

/-- Upper energy budget expressed in complete Möbius-head energies. -/
def dilationBudget (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N,
    ‖exactHead (N / (k + 1))‖ ^ 2 / ((k + 1 : ℕ) : ℝ)

theorem gramTrace_nonneg (N : ℕ) : 0 ≤ gramTrace N :=
  Finset.sum_nonneg fun k _ => sq_nonneg _

theorem dilationBudget_nonneg (N : ℕ) : 0 ≤ dilationBudget N :=
  Finset.sum_nonneg fun k _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-- The budget has an exact complete infinite remainder, not just an inequality. -/
theorem dilationBudget_sub_gramTrace (N : ℕ) :
    dilationBudget N - gramTrace N =
      ∑ k ∈ Finset.range N, ∑' j,
        qBlockDefect (k + 1) j *
          (qSequence (exactHead (N / (k + 1))) j) ^ 2 := by
  unfold dilationBudget gramTrace
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => dilatedMobiusStep_norm_sq_defect N k

theorem gramTrace_le_dilationBudget (N : ℕ) : gramTrace N ≤ dilationBudget N :=
  Finset.sum_le_sum fun k _ => dilatedMobiusStep_norm_sq_le N k

/-- Explicit reciprocal target specialization with the exact complete Gram trace. -/
theorem reciprocalRepair_norm_sq_le_trace (N : ℕ) (f : QHilbert) :
    ‖reciprocalRepair N f‖ ^ 2 ≤ 4 * zetaTwo * ‖f‖ ^ 2 * gramTrace N := by
  apply (repair_norm_sq_le_trace N (qSequence (QShiftedReciprocal.B f))).trans
  exact mul_le_mul_of_nonneg_right
    (reciprocal_forward_difference_square_sum_le f N) (gramTrace_nonneg N)

/-- Explicit complete reciprocal repair budget, with no assumption on the residual. -/
theorem reciprocalRepair_norm_sq_le_dilationBudget (N : ℕ) (f : QHilbert) :
    ‖reciprocalRepair N f‖ ^ 2 ≤
      4 * zetaTwo * ‖f‖ ^ 2 * dilationBudget N :=
  (reciprocalRepair_norm_sq_le_trace N f).trans
    (mul_le_mul_of_nonneg_left (gramTrace_le_dilationBudget N) (by have hZ := zetaTwo_pos; positivity))

end RiemannResearch.RH.QFullDilatedMobiusRepair
