/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.DenseProjectionTesting
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Exact residualized projection kernels

Source: user-provided RH_Measure_Change_Regularity_Research_Handoff_2026-10-25,
Section A2. This is general real Hilbert-space projection geometry. It proves
identities and a Cauchy--Schwarz estimate, not the arithmetic uniform bound.
-/

noncomputable section
namespace RiemannResearch.Analysis.ResidualizedProjectionKernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (S : Submodule ℝ E) [S.HasOrthogonalProjection]

theorem projection_inner (x y : E) :
    inner ℝ (S.starProjection x) y = inner ℝ x (S.starProjection y) := by
  calc
    _ = inner ℝ (S.starProjection x) (S.starProjection y) :=
      DenseProjectionTesting.inner_eq_projected_test S
        (S.starProjection_apply_mem x) y
    _ = inner ℝ (S.starProjection y) (S.starProjection x) := real_inner_comm _ _
    _ = inner ℝ (S.starProjection y) x :=
      (DenseProjectionTesting.inner_eq_projected_test S
        (S.starProjection_apply_mem y) x).symm
    _ = inner ℝ x (S.starProjection y) := real_inner_comm _ _

theorem orthogonal_inner_projection {r : E} (hr : r ∈ Sᗮ) (u : E) :
    inner ℝ r (S.starProjection u) = 0 := by
  rw [real_inner_comm]
  exact Submodule.inner_right_of_mem_orthogonal
    (S.starProjection_apply_mem u) hr

/-- Residualize the smoothed evaluation kernel before estimating. -/
theorem pairing_eq_residualized
    (B : E →L[ℝ] E)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    {r : E} (hr : r ∈ Sᗮ) (e : E) :
    inner ℝ (S.starProjection (B r)) e =
      inner ℝ r (B (S.starProjection e) -
        S.starProjection (B (S.starProjection e))) := by
  rw [projection_inner, hB, inner_sub_right,
    orthogonal_inner_projection S hr, sub_zero]

/-- The subtraction is retained exactly, with no discarded positive square. -/
theorem residual_norm_sq (u : E) :
    ‖u - S.starProjection u‖ ^ 2 =
      ‖u‖ ^ 2 - ‖S.starProjection u‖ ^ 2 := by
  have ho := Submodule.inner_right_of_mem_orthogonal
    (S.starProjection_apply_mem u)
    (Submodule.sub_starProjection_mem_orthogonal (K := S) u)
  rw [inner_sub_right, real_inner_self_eq_norm_sq] at ho
  rw [real_inner_comm] at ho
  rw [norm_sub_sq_real]
  linarith

theorem residualized_energy_nonneg (u : E) :
    0 ≤ ‖u‖ ^ 2 - ‖S.starProjection u‖ ^ 2 := by
  rw [← residual_norm_sq S u]
  exact sq_nonneg _

theorem pairing_sq_le_residualized
    (B : E →L[ℝ] E)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    {r : E} (hr : r ∈ Sᗮ) (e : E) :
    (inner ℝ (S.starProjection (B r)) e) ^ 2 ≤
      ‖r‖ ^ 2 * (‖B (S.starProjection e)‖ ^ 2 -
        ‖S.starProjection (B (S.starProjection e))‖ ^ 2) := by
  rw [pairing_eq_residualized S B hB hr e,
    ← residual_norm_sq S (B (S.starProjection e))]
  have h := abs_real_inner_le_norm r
    (B (S.starProjection e) - S.starProjection (B (S.starProjection e)))
  have hh := mul_le_mul h h (abs_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  simpa only [← pow_two, sq_abs, mul_pow] using hh

/-- Scalar shifts of the multiplier leave the residualized kernel unchanged. -/
theorem residualized_shift (B : E →L[ℝ] E) (e : E) (a : ℝ) :
    (B (S.starProjection e) - a • S.starProjection e) -
        S.starProjection (B (S.starProjection e) - a • S.starProjection e) =
      B (S.starProjection e) - S.starProjection (B (S.starProjection e)) := by
  rw [map_sub, map_smul,
    (Submodule.starProjection_eq_self_iff.mpr (S.starProjection_apply_mem e))]
  abel

/-- A multiplier eigenvector yields a complementary centered-kernel formula. -/
theorem residualized_of_eigenvector
    (B : E →L[ℝ] E) (e : E) (a : ℝ) (he : B e = a • e) :
    B (S.starProjection e) - S.starProjection (B (S.starProjection e)) =
      (a • (e - S.starProjection e) - B (e - S.starProjection e)) -
        S.starProjection
          (a • (e - S.starProjection e) - B (e - S.starProjection e)) := by
  have hp : S.starProjection (S.starProjection e) = S.starProjection e :=
    Submodule.starProjection_eq_self_iff.mpr (S.starProjection_apply_mem e)
  simp only [map_sub, map_smul, smul_sub, he, hp]
  abel

/-- A complementary-kernel estimate retaining diagonal cancellation. -/
theorem residualized_sq_le_centered_complement
    (B : E →L[ℝ] E) (e : E) (a : ℝ) (he : B e = a • e) :
    ‖B (S.starProjection e) - S.starProjection (B (S.starProjection e))‖ ^ 2 ≤
      ‖a • (e - S.starProjection e) - B (e - S.starProjection e)‖ ^ 2 := by
  rw [residualized_of_eigenvector S B e a he, residual_norm_sq]
  exact sub_le_self _ (sq_nonneg _)

end RiemannResearch.Analysis.ResidualizedProjectionKernel
