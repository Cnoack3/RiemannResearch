/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Covariance stability under small Hilbert-column corrections

Source: the two-three resonance-cell continuation, 15 September 2026.
Weighted Young estimates give a fixed error when the small column has squared
norm of order 1/k and the other column has squared norm of order k.
-/

namespace RiemannResearch.Analysis.SmallColumnCovariance
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Weighted Young inequality at the actual common scale. -/
theorem weighted_inner_bound (B A : H) {k C L : ℝ} (hk : 0 < k)
    (hB : k*‖B‖^2 ≤ C) (hA : ‖A‖^2 ≤ k*L) :
    2*|inner ℝ B A| ≤ C+L := by
  have hi : |inner ℝ B A| ≤ ‖B‖*‖A‖ := by
    simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜:=ℝ) B A
  have hy : 2*‖B‖*‖A‖ ≤ C+L := by
    refine le_of_mul_le_mul_left (a:=k) ?_ hk
    have hBk := mul_le_mul_of_nonneg_left hB (le_of_lt hk)
    nlinarith [sq_nonneg (k*‖B‖-‖A‖)]
  linarith

/-- Exact correction formula for two signed columns. -/
theorem correction_identity (A A' B B' : H) :
    inner ℝ A A' - inner ℝ (B-A) (B'-A') =
      inner ℝ B A' + inner ℝ A B' - inner ℝ B B' := by
  simp only [inner_sub_left, inner_sub_right]
  ring

/-- Uniform covariance transfer retaining all three correction terms. -/
theorem covariance_error (A A' B B' : H) {k C L : ℝ} (hk : 1 ≤ k)
    (hB : k*‖B‖^2 ≤ C) (hB' : k*‖B'‖^2 ≤ C)
    (hA : ‖A‖^2 ≤ k*L) (hA' : ‖A'‖^2 ≤ k*L) :
    |inner ℝ A A' - inner ℝ (B-A) (B'-A')| ≤ 2*C+L := by
  have hk0 : 0 < k := by linarith
  have hBA := weighted_inner_bound B A' hk0 hB hA'
  have hAB := weighted_inner_bound B' A hk0 hB' hA
  have hsym : inner ℝ B' A = inner ℝ A B' := real_inner_comm _ _
  rw [hsym] at hAB
  have hBs : ‖B‖^2 ≤ C := by
    have hm := mul_le_mul_of_nonneg_right hk (sq_nonneg ‖B‖)
    simp only [one_mul] at hm
    exact hm.trans hB
  have hB's : ‖B'‖^2 ≤ C := by
    have hm := mul_le_mul_of_nonneg_right hk (sq_nonneg ‖B'‖)
    simp only [one_mul] at hm
    exact hm.trans hB'
  have hi : |inner ℝ B B'| ≤ ‖B‖*‖B'‖ := by
    simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜:=ℝ) B B'
  have hBB : |inner ℝ B B'| ≤ C := by
    nlinarith [sq_nonneg (‖B‖-‖B'‖)]
  rw [correction_identity]
  have hsum := abs_add_le (inner ℝ B A') (inner ℝ A B')
  have hsub : |inner ℝ B A'+inner ℝ A B'-inner ℝ B B'| ≤
      |inner ℝ B A'+inner ℝ A B'|+|inner ℝ B B'| := by
    simpa only [sub_eq_add_neg, abs_neg] using
      abs_add_le (inner ℝ B A'+inner ℝ A B') (-inner ℝ B B')
  linarith

end
end RiemannResearch.Analysis.SmallColumnCovariance
