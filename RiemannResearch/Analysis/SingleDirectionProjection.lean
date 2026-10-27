/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Orthogonal single-direction extension and smoothed residual response

Source: the user's SingleConductorProjectionBound.md. The exact extension
formula is retained before the operator-norm estimate. The latter improves
the constant-target paper argument to arbitrary inputs.
-/

noncomputable section
namespace RiemannResearch.Analysis.SingleDirectionProjection
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem projection_extension_eq (U : Submodule ℝ H) [U.HasOrthogonalProjection]
    (v x : H) [(U ⊔ Submodule.span ℝ ({v} : Set H)).HasOrthogonalProjection]
    (hv : v - U.starProjection v ≠ 0) :
    (U ⊔ Submodule.span ℝ ({v} : Set H)).starProjection x =
      U.starProjection x +
        (inner ℝ x (v - U.starProjection v) / ‖v - U.starProjection v‖ ^ 2) •
          (v - U.starProjection v) := by
  let W := U ⊔ Submodule.span ℝ ({v} : Set H)
  let u := v - U.starProjection v
  let t := inner ℝ x u / ‖u‖ ^ 2
  have hu (y : H) (hy : y ∈ U) : inner ℝ u y = 0 :=
    U.starProjection_inner_eq_zero v y hy
  have hUW : U ≤ W := le_sup_left
  have hvW : v ∈ W := (show Submodule.span ℝ ({v} : Set H) ≤ W from le_sup_right)
    (Submodule.subset_span (by simp))
  have huW : u ∈ W := W.sub_mem hvW
    (hUW (U.starProjection_apply_mem v))
  have hyW : U.starProjection x + t • u ∈ W :=
    W.add_mem (hUW (U.starProjection_apply_mem x)) (W.smul_mem t huW)
  have horth (y : H) (hy : y ∈ U) :
      inner ℝ (x - (U.starProjection x + t • u)) y = 0 := by
    have hx := U.starProjection_inner_eq_zero x y hy
    rw [inner_sub_left] at hx
    rw [inner_sub_left, inner_add_left, real_inner_smul_left, hu y hy]
    linarith
  have hpu : inner ℝ (U.starProjection x) u = 0 := by
    rw [real_inner_comm]
    exact hu _ (U.starProjection_apply_mem x)
  have hn : ‖u‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
  have horthu : inner ℝ (x - (U.starProjection x + t • u)) u = 0 := by
    rw [inner_sub_left, inner_add_left, real_inner_smul_left, hpu,
      real_inner_self_eq_norm_sq]
    dsimp [t]
    rw [zero_add, div_mul_cancel₀ _ hn, sub_self]
  have horthv : inner ℝ (x - (U.starProjection x + t • u)) v = 0 := by
    have he : v = U.starProjection v + u := by dsimp [u]; abel
    rw [he, inner_add_right, horth _ (U.starProjection_apply_mem v), horthu, add_zero]
  change W.starProjection x = U.starProjection x + t • u
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hyW
  intro y hy
  rcases Submodule.mem_sup.mp hy with ⟨a, ha, b, hb, rfl⟩
  rcases Submodule.mem_span_singleton.mp hb with ⟨c, rfl⟩
  rw [inner_add_right, horth a ha, real_inner_smul_right, horthv, mul_zero, add_zero]

theorem residual_norm_le (W : Submodule ℝ H) [W.HasOrthogonalProjection]
    (x : H) : ‖x - W.starProjection x‖ ≤ ‖x‖ := by
  have h := Submodule.norm_sq_eq_add_norm_sq_starProjection x W
  simp only [Submodule.starProjection_orthogonal_val] at h
  nlinarith [sq_nonneg ‖W.starProjection x‖, norm_nonneg x,
    norm_nonneg (x - W.starProjection x)]

/-- The numerator estimate uses self-adjoint smoothing before Cauchy--Schwarz.
It holds for every input, not only for the constant target. -/
theorem smoothing_coefficient_le
    (W : Submodule ℝ H) [W.HasOrthogonalProjection]
    (B : H →L[ℝ] H) (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    (u f : H) :
    |inner ℝ (B (f - W.starProjection f)) u / ‖u‖ ^ 2| ≤
      ‖B u‖ * ‖f‖ / ‖u‖ ^ 2 := by
  rw [abs_div, abs_of_nonneg (sq_nonneg ‖u‖), hB]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  calc
    |inner ℝ (f - W.starProjection f) (B u)| ≤
        ‖f - W.starProjection f‖ * ‖B u‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖f‖ * ‖B u‖ := mul_le_mul_of_nonneg_right
      (residual_norm_le W f) (norm_nonneg _)
    _ = ‖B u‖ * ‖f‖ := mul_comm _ _

end RiemannResearch.Analysis.SingleDirectionProjection
