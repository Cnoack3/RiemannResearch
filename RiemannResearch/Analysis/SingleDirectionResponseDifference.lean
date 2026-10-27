/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Basic
import RiemannResearch.Analysis.SingleDirectionProjection
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact response change after one orthogonal direction

Source: user-provided argument in `SingleConductorProjectionBound.md`;
the exact rank-one algebra and its operator-norm consequences are assembled here.

The signed rank-one expansion is proved before taking norms. It shows that
self-adjoint smoothing suppresses a newly adjoined direction whenever the
smoothed direction is small relative to its Hilbert norm.
-/

noncomputable section
namespace RiemannResearch.Analysis.SingleDirectionProjection
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The bounded linear operator taking an input to its projected smoothed
orthogonal residual. -/
def responseOperator (U : Submodule ℝ H) [U.HasOrthogonalProjection]
    (B : H →L[ℝ] H) : H →L[ℝ] H :=
  U.starProjection.comp (B.comp (ContinuousLinearMap.id ℝ H - U.starProjection))

/-- Signed change in smoothed-residual response after adjoining one direction. -/
theorem response_extension_difference_eq
    (U : Submodule ℝ H) [U.HasOrthogonalProjection]
    (v : H) [(U ⊔ Submodule.span ℝ ({v} : Set H)).HasOrthogonalProjection]
    (B : H →L[ℝ] H) (f : H) (hv : v - U.starProjection v ≠ 0) :
    responseOperator (U ⊔ Submodule.span ℝ ({v} : Set H)) B f -
        responseOperator U B f =
      -(inner ℝ f (v - U.starProjection v) / ‖v - U.starProjection v‖ ^ 2) •
          U.starProjection (B (v - U.starProjection v)) +
        (inner ℝ (B (f -
          (U ⊔ Submodule.span ℝ ({v} : Set H)).starProjection f))
            (v - U.starProjection v) / ‖v - U.starProjection v‖ ^ 2) •
          (v - U.starProjection v) := by
  let W := U ⊔ Submodule.span ℝ ({v} : Set H)
  let u := v - U.starProjection v
  let a := inner ℝ f u / ‖u‖ ^ 2
  let r := f - W.starProjection f
  let b := inner ℝ (B r) u / ‖u‖ ^ 2
  have hr : r = (f - U.starProjection f) - a • u := by
    dsimp only [r]
    rw [projection_extension_eq U v f hv]
    dsimp only [a, u]
    abel
  have hB : U.starProjection (B r) =
      U.starProjection (B (f - U.starProjection f)) - a • U.starProjection (B u) := by
    rw [hr, map_sub, map_smul, map_sub, map_smul]
  have hW : W.starProjection (B r) = U.starProjection (B r) + b • u :=
    projection_extension_eq U v (B r) hv
  change W.starProjection (B r) - U.starProjection (B (f - U.starProjection f)) =
    -a • U.starProjection (B u) + b • u
  rw [hW, hB, neg_smul]
  abel

/-- Uniform input estimate obtained from the exact signed change. -/
theorem response_extension_difference_norm_le
    (U : Submodule ℝ H) [U.HasOrthogonalProjection]
    (v : H) [(U ⊔ Submodule.span ℝ ({v} : Set H)).HasOrthogonalProjection]
    (B : H →L[ℝ] H)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    (f : H) (hv : v - U.starProjection v ≠ 0) :
    ‖responseOperator (U ⊔ Submodule.span ℝ ({v} : Set H)) B f -
        responseOperator U B f‖ ≤
      (2 * ‖B (v - U.starProjection v)‖ / ‖v - U.starProjection v‖) * ‖f‖ := by
  let W := U ⊔ Submodule.span ℝ ({v} : Set H)
  let u := v - U.starProjection v
  let a := inner ℝ f u / ‖u‖ ^ 2
  let b := inner ℝ (B (f - W.starProjection f)) u / ‖u‖ ^ 2
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hv
  have ha : |a| ≤ ‖f‖ / ‖u‖ := by
    calc
      _ = |inner ℝ f u| / ‖u‖ ^ 2 := by
        dsimp only [a]
        rw [abs_div, abs_of_nonneg (sq_nonneg ‖u‖)]
      _ ≤ (‖f‖ * ‖u‖) / ‖u‖ ^ 2 :=
        div_le_div_of_nonneg_right (abs_real_inner_le_norm f u) (sq_nonneg _)
      _ = _ := by field_simp [hn.ne'] <;> ring
  have hb : |b| ≤ ‖B u‖ * ‖f‖ / ‖u‖ ^ 2 :=
    smoothing_coefficient_le W B hB u f
  have hproj : ‖U.starProjection (B u)‖ ≤ ‖B u‖ := by
    calc
      _ ≤ ‖U.starProjection‖ * ‖B u‖ := U.starProjection.le_opNorm (B u)
      _ ≤ 1 * ‖B u‖ := mul_le_mul_of_nonneg_right
        (Submodule.starProjection_norm_le U) (norm_nonneg _)
      _ = _ := one_mul _
  rw [response_extension_difference_eq U v B f hv]
  change ‖-a • U.starProjection (B u) + b • u‖ ≤ _
  calc
    _ ≤ ‖-a • U.starProjection (B u)‖ + ‖b • u‖ := norm_add_le _ _
    _ = |a| * ‖U.starProjection (B u)‖ + |b| * ‖u‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
    _ ≤ (‖f‖ / ‖u‖) * ‖B u‖ + (‖B u‖ * ‖f‖ / ‖u‖ ^ 2) * ‖u‖ :=
      add_le_add (mul_le_mul ha hproj (norm_nonneg _) (by positivity))
        (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
    _ = _ := by field_simp [hn.ne'] <;> ring

/-- Operator norm control is uniform over all inputs. -/
theorem response_extension_operator_norm_le
    (U : Submodule ℝ H) [U.HasOrthogonalProjection]
    (v : H) [(U ⊔ Submodule.span ℝ ({v} : Set H)).HasOrthogonalProjection]
    (B : H →L[ℝ] H)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    (hv : v - U.starProjection v ≠ 0) :
    ‖responseOperator (U ⊔ Submodule.span ℝ ({v} : Set H)) B -
        responseOperator U B‖ ≤
      2 * ‖B (v - U.starProjection v)‖ / ‖v - U.starProjection v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  exact response_extension_difference_norm_le U v B hB f hv

end RiemannResearch.Analysis.SingleDirectionProjection
