/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Part of the RiemannResearch project.
Authors: Christian Noack
-/

import RiemannResearch.Analysis.CoordinateSquareVariation
import RiemannResearch.Analysis.ProjectionResidualSampling
import Mathlib.Tactic.FieldSimp

-- The Apache-specific header convention does not determine project licensing.
set_option linter.style.header false

/-!
# Sharp coordinate variation of actual nested projection residuals

Source: the user's DPP residual-law continuation, equation (5), October
2026. Normalization, covariance, and the complete coordinate sum are proved
from the genuine Hilbert residuals. No target-membership or RH input occurs.

-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.ProjectionResidualSampling
open CoordinateSquareVariation

variable {ι : Type*}

def normalized (x : RealL2 ι) : RealL2 ι := ‖x‖⁻¹ • x

theorem normalized_norm (x : RealL2 ι) (hx : x ≠ 0) : ‖normalized x‖ = 1 := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  rw [normalized, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
  exact inv_mul_cancel₀ hn

theorem normalized_norm_sq (x : RealL2 ι) (hx : x ≠ 0) :
    ‖normalized x‖ ^ 2 = 1 := by
  rw [normalized_norm x hx]
  norm_num

variable (S T : Submodule ℝ (RealL2 ι))
  [S.HasOrthogonalProjection] [T.HasOrthogonalProjection]
  (hST : S ≤ T)

include hST

theorem normalized_nested_residual_inner (x : RealL2 ι)
    (hS : x - S.starProjection x ≠ 0) (hT : x - T.starProjection x ≠ 0) :
    inner ℝ (normalized (x - S.starProjection x)) (normalized (x - T.starProjection x)) =
      ‖x - T.starProjection x‖ / ‖x - S.starProjection x‖ := by
  have hSn : ‖x - S.starProjection x‖ ≠ 0 := norm_ne_zero_iff.mpr hS
  have hTn : ‖x - T.starProjection x‖ ≠ 0 := norm_ne_zero_iff.mpr hT
  rw [normalized, normalized, real_inner_smul_left, real_inner_smul_right,
    nested_residual_inner S T hST x]
  field_simp [hSn, hTn]

/-- The squared total variation of the complete unit-coordinate laws is
bounded by the relative drop of the actual nested residual energy. -/
theorem nested_residual_coordinateTV_sq_le (x : RealL2 ι)
    (hS : x - S.starProjection x ≠ 0) (hT : x - T.starProjection x ≠ 0) :
    (coordinateTV (normalized (x - S.starProjection x))
      (normalized (x - T.starProjection x))) ^ 2 ≤
      (‖x - S.starProjection x‖ ^ 2-‖x - T.starProjection x‖ ^ 2) /
        ‖x - S.starProjection x‖ ^ 2 := by
  have hSn : ‖x - S.starProjection x‖ ≠ 0 := norm_ne_zero_iff.mpr hS
  have h := coordinateTV_sq_le
    (normalized (x - S.starProjection x)) (normalized (x - T.starProjection x))
    (normalized_norm_sq _ hS) (normalized_norm_sq _ hT)
  rw [normalized_nested_residual_inner S T hST x hS hT] at h
  calc
    _ ≤ 1-(‖x - T.starProjection x‖/‖x - S.starProjection x‖) ^ 2 := h
    _ = _ := by
      field_simp [hSn]

end RiemannResearch.Analysis.ProjectionResidualSampling
