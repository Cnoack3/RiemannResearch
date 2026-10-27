/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QShiftedReciprocal
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Exact quarter-contraction for a reciprocal operator compressed against
an orthogonal residual. Source: LegalSubspaceProjectionObstruction.md. -/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QShiftedReciprocal
open ZetaTwoHilbert

theorem B_sub_quarter_norm_le (f : QHilbert) :
    ‖B f - (1 / 4 : ℝ) • f‖ ≤ (1 / 4 : ℝ) * ‖f‖ := by
  have hpoint (n : ℕ) : ((B f - (1 / 4 : ℝ) • f) n) ^ 2 ≤
      (1 / 16 : ℝ) * (f n) ^ 2 := by
    change (B f n - (1 / 4 : ℝ) * f n) ^ 2 ≤ _
    rw [B_apply]
    have hn : (0 : ℝ) < n + 2 := by positivity
    have h0 : 0 ≤ 1 / ((n : ℝ) + 2) := by positivity
    have h1 : 1 / ((n : ℝ) + 2) ≤ 1 / 2 :=
      (div_le_iff₀ hn).mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
    have hs : (1 / ((n : ℝ) + 2) - 1 / 4) ^ 2 ≤ (1 / 16 : ℝ) := by
      nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]
    have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg (f n))
    calc
      _ = (1 / ((n : ℝ) + 2) - 1 / 4) ^ 2 * (f n) ^ 2 := by ring
      _ ≤ _ := hm
  have he := (qCoordinate_square_summable (B f - (1 / 4 : ℝ) • f)).tsum_le_tsum
    hpoint ((qCoordinate_square_summable f).mul_left (1 / 16 : ℝ))
  rw [← qNorm_sq, tsum_mul_left, ← qNorm_sq] at he
  nlinarith [norm_nonneg (B f - (1 / 4 : ℝ) • f), norm_nonneg f]

theorem projected_B_quarter_norm_le (S : Submodule ℝ QHilbert)
    [S.HasOrthogonalProjection] {r : QHilbert} (hr : r ∈ Sᗮ) :
    ‖S.starProjection (B r)‖ ≤ (1 / 4 : ℝ) * ‖r‖ := by
  have hz : S.starProjection r = 0 := by
    have h1 := Submodule.inner_right_of_mem_orthogonal (S.starProjection_apply_mem r) hr
    have h2 := Submodule.inner_right_of_mem_orthogonal (S.starProjection_apply_mem r)
      (Submodule.sub_starProjection_mem_orthogonal (K := S) r)
    rw [inner_sub_right, h1, real_inner_self_eq_norm_sq] at h2
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (S.starProjection r)]
  have he : S.starProjection (B r - (1 / 4 : ℝ) • r) = S.starProjection (B r) := by
    simp only [map_sub, map_smul, hz, smul_zero, sub_zero]
  rw [← he]
  calc
    _ ≤ ‖S.starProjection‖ * ‖B r - (1 / 4 : ℝ) • r‖ := S.starProjection.le_opNorm _
    _ ≤ ‖B r - (1 / 4 : ℝ) • r‖ := by
      simpa using mul_le_mul_of_nonneg_right (Submodule.starProjection_norm_le S)
        (norm_nonneg _)
    _ ≤ _ := B_sub_quarter_norm_le r

end RiemannResearch.RH.QShiftedReciprocal
