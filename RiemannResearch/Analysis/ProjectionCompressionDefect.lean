/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import RiemannResearch.LinearAlgebra.TwoChannelCancellation

/-!
# Source defect and the boundary of a compressed orthogonal projection

Source: independently developed continuation of the user-provided two-seed
spectral-mass problem, 15 September 2026. The RH consumer takes `P` to be a
finite legal subspace and `Q` to be the first physical coordinates. These
identities retain the full signed boundary term. No spectral gap, arithmetic
approximation estimate, or convergence of an inverse moment is assumed.
-/

namespace RiemannResearch.Analysis.ProjectionCompression

noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (P Q : Submodule ℝ H) [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]

private theorem inner_projection_self (x : H) :
    inner ℝ x (P.starProjection x) = ‖P.starProjection x‖ ^ 2 := by
  have h := Submodule.starProjection_inner_eq_zero x (P.starProjection x)
    (Submodule.starProjection_apply_mem P x)
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at h
  linarith

/-- The full projection defect retains the cross pairing with the original vector. -/
theorem defect_inner (x y : H) :
    inner ℝ (x - P.starProjection x) (y - P.starProjection y) =
      inner ℝ x y - inner ℝ (P.starProjection x) y := by
  have h := Submodule.starProjection_inner_eq_zero x (P.starProjection y)
    (Submodule.starProjection_apply_mem P y)
  rw [inner_sub_right, h, sub_zero, inner_sub_left]

theorem projection_pythagoras (x : H) :
    ‖x‖ ^ 2 = ‖P.starProjection x‖ ^ 2 + ‖x - P.starProjection x‖ ^ 2 := by
  have h := defect_inner P x x
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  have hp := inner_projection_self P x
  have hc := real_inner_comm x (P.starProjection x)
  linarith

theorem defect_norm_le (x : H) : ‖x - P.starProjection x‖ ≤ ‖x‖ := by
  nlinarith [projection_pythagoras P x, sq_nonneg ‖P.starProjection x‖,
    norm_nonneg x, norm_nonneg (x - P.starProjection x)]

/-- The compression's first moment is the full retained projection energy. -/
theorem compression_first_moment (x : H) (hx : x ∈ Q) :
    inner ℝ x (Q.starProjection (P.starProjection x)) = ‖P.starProjection x‖ ^ 2 := by
  have h := Submodule.starProjection_inner_eq_zero (P.starProjection x) x hx
  rw [inner_sub_left] at h
  have hp := inner_projection_self P x
  have hc := real_inner_comm x (P.starProjection x)
  have hc' := real_inner_comm x (Q.starProjection (P.starProjection x))
  linarith

/-- The first centered spectral moment is the ordinary truncated-source defect. -/
theorem compression_defect_moment (x : H) (hx : x ∈ Q) :
    ‖x‖ ^ 2 - inner ℝ x (Q.starProjection (P.starProjection x)) =
      ‖x - P.starProjection x‖ ^ 2 := by
  rw [compression_first_moment P Q x hx]
  linarith [projection_pythagoras P x]

/-- The spectral quantity lambda*(1-lambda) is exactly the omitted full tail. -/
theorem compression_polarization (x : H) (hx : x ∈ Q) :
    inner ℝ x (Q.starProjection (P.starProjection x)) -
        ‖Q.starProjection (P.starProjection x)‖ ^ 2 =
      ‖P.starProjection x - Q.starProjection (P.starProjection x)‖ ^ 2 := by
  rw [compression_first_moment P Q x hx]
  linarith [projection_pythagoras Q (P.starProjection x)]

/-- Orthogonal head and tail leave a signed pairing with the projected tail. -/
theorem defect_inner_head_tail (x t : H) (hx : x ∈ Q) (ht : t ∈ Qᗮ) :
    inner ℝ (x - P.starProjection x) (t - P.starProjection t) =
      -inner ℝ (P.starProjection x - Q.starProjection (P.starProjection x)) t := by
  have hxt := (Submodule.mem_orthogonal Q t).mp ht x hx
  have hqt := (Submodule.mem_orthogonal Q t).mp ht
    (Q.starProjection (P.starProjection x))
    (Submodule.starProjection_apply_mem Q (P.starProjection x))
  rw [defect_inner, hxt, inner_sub_left, hqt]
  ring

/-- Exact correction from the truncated source to the full source. -/
theorem full_source_defect_exact (x t : H) (hx : x ∈ Q) (ht : t ∈ Qᗮ) :
    ‖(x + t) - P.starProjection (x + t)‖ ^ 2 =
      ‖x - P.starProjection x‖ ^ 2 + ‖t - P.starProjection t‖ ^ 2 -
        2 * inner ℝ (P.starProjection x - Q.starProjection (P.starProjection x)) t := by
  have he : (x + t) - P.starProjection (x + t) =
      (x - P.starProjection x) + (t - P.starProjection t) := by
    rw [map_add]
    abel
  rw [he, RiemannResearch.LinearAlgebra.TwoChannelCancellation.norm_add_sq,
    defect_inner_head_tail P Q x t hx ht]
  ring

/-- The boundary error is controlled by its actual leakage, not by a discarded cross term. -/
theorem full_source_defect_error (x t : H) (hx : x ∈ Q) (ht : t ∈ Qᗮ) :
    |‖(x + t) - P.starProjection (x + t)‖ ^ 2 - ‖x - P.starProjection x‖ ^ 2| ≤
      2 * ‖t‖ * ‖P.starProjection x - Q.starProjection (P.starProjection x)‖ + ‖t‖ ^ 2 := by
  rw [full_source_defect_exact P Q x t hx ht]
  have hc := norm_inner_le_norm (𝕜 := ℝ)
    (P.starProjection x - Q.starProjection (P.starProjection x)) t
  rw [Real.norm_eq_abs] at hc
  have hp := projection_pythagoras P t
  apply abs_le.mpr
  constructor
  · have hh := (abs_le.mp hc).2
    nlinarith [sq_nonneg ‖t - P.starProjection t‖, sq_nonneg ‖t‖]
  · have hh := (abs_le.mp hc).1
    nlinarith [sq_nonneg ‖P.starProjection t‖]

end
end RiemannResearch.Analysis.ProjectionCompression
