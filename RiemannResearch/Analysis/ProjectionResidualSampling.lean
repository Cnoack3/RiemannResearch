/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Part of the RiemannResearch project.
Authors: Christian Noack
-/

import RiemannResearch.Analysis.ProjectionDPPKernel

-- The Apache-specific header convention does not determine project licensing.
set_option linter.style.header false

/-!
# Residual energies and finite-head insertion bounds

Source: user-requested continuation of the residual insertion law, October
2026. These are deterministic real Hilbert-space identities. The squared
pairing bound needs no orthonormality assumption. Choosing normalized weighted
coordinate vectors identifies its left side with insertion-law head mass.

In a nested exhausting family, apply the finite-head theorem with T equal to
the closed union and x in T. Strong convergence of the projections sends its
finite trace bound to zero. Membership of an arithmetic target in that closed
union is not supplied here, and no RH conclusion is claimed.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.ProjectionResidualSampling

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (S T : Submodule ℝ H)
  [S.HasOrthogonalProjection] [T.HasOrthogonalProjection]
  (hST : S ≤ T)

include hST

/-- Exact residual covariance; this supplies the normalized angle in the
total-variation bound for insertion laws. -/
theorem nested_residual_inner (x : H) :
    inner ℝ (x - S.starProjection x) (x - T.starProjection x) =
      ‖x - T.starProjection x‖ ^ 2 := by
  have hp : T.starProjection x - S.starProjection x ∈ T :=
    T.sub_mem (T.starProjection_apply_mem x)
      (hST (S.starProjection_apply_mem x))
  have ho : inner ℝ (T.starProjection x - S.starProjection x)
      (x - T.starProjection x) = 0 :=
    (T.mem_orthogonal _).mp
      (Submodule.sub_starProjection_mem_orthogonal x) _ hp
  have he : x - S.starProjection x =
      (x - T.starProjection x) +
        (T.starProjection x - S.starProjection x) := by
    abel
  rw [he, inner_add_left, real_inner_self_eq_norm_sq, ho, add_zero]

/-- If the target belongs to the larger space, residual coordinate pairings
are exactly pairings with the remaining projection-enlargement vector. -/
theorem residual_pairing_eq_projection_difference (x b : H) (hx : x ∈ T) :
    inner ℝ (x - S.starProjection x) b =
      inner ℝ (x - S.starProjection x)
        (T.starProjection b - S.starProjection b) := by
  have hrT : x - S.starProjection x ∈ T :=
    T.sub_mem hx (hST (S.starProjection_apply_mem x))
  have hT : inner ℝ (x - S.starProjection x)
      (b - T.starProjection b) = 0 :=
    (T.mem_orthogonal _).mp
      (Submodule.sub_starProjection_mem_orthogonal b) _ hrT
  have hS : inner ℝ (x - S.starProjection x) (S.starProjection b) = 0 := by
    rw [real_inner_comm]
    exact (S.mem_orthogonal _).mp
      (Submodule.sub_starProjection_mem_orthogonal x) _
      (S.starProjection_apply_mem b)
  simp only [inner_sub_right] at hT ⊢
  linarith

theorem residual_pairing_sq_le_projection_difference (x b : H) (hx : x ∈ T) :
    (inner ℝ (x - S.starProjection x) b) ^ 2 ≤
      ‖x - S.starProjection x‖ ^ 2 *
        ‖T.starProjection b - S.starProjection b‖ ^ 2 := by
  rw [residual_pairing_eq_projection_difference S T hST x b hx]
  have hs := (sq_le_sq₀
    (abs_nonneg (inner ℝ (x - S.starProjection x)
      (T.starProjection b - S.starProjection b)))
    (mul_nonneg (norm_nonneg (x - S.starProjection x))
      (norm_nonneg (T.starProjection b - S.starProjection b)))).mpr
    (abs_real_inner_le_norm (x - S.starProjection x)
      (T.starProjection b - S.starProjection b))
  simpa only [sq_abs, mul_pow] using hs

/-- A rigorous finite-head mass certificate. The denominator is positive
because an insertion law is defined only for a nonzero residual. -/
theorem residual_head_pairing_sq_le_projection_trace
    (x : H) (hx : x ∈ T) (hR : x - S.starProjection x ≠ 0)
    (b : ι → H) (A : Finset ι) :
    (∑ i ∈ A, (inner ℝ (x - S.starProjection x) (b i)) ^ 2) /
        ‖x - S.starProjection x‖ ^ 2 ≤
      ∑ i ∈ A, ‖T.starProjection (b i) - S.starProjection (b i)‖ ^ 2 := by
  have hs : (∑ i ∈ A, (inner ℝ (x - S.starProjection x) (b i)) ^ 2) ≤
      ∑ i ∈ A, ‖x - S.starProjection x‖ ^ 2 *
        ‖T.starProjection (b i) - S.starProjection (b i)‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    exact residual_pairing_sq_le_projection_difference S T hST x (b i) hx
  rw [← Finset.mul_sum] at hs
  have hp : 0 < ‖x - S.starProjection x‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hR)
  apply (div_le_iff₀ hp).mpr
  simpa only [mul_comm] using hs

end RiemannResearch.Analysis.ProjectionResidualSampling
