import RiemannResearch.Analysis.HeadTailResidualLift
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Solvability of a finite head compression

Source: user-provided `RH_Coupled_Residual_Corrections_2026-09-16.md`,
Section 8. This module proves the finite-dimensional geometric step.
The application supplies actual head surjectivity, rather than assuming
the compressed normal equation that was used by `HeadTailResidualLift`.
-/

noncomputable section
namespace RiemannResearch.Analysis.HeadTailResidualLift
open RiemannResearch.Analysis.ProjectionSourceImprovement

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (P R : Submodule ℝ H) [P.HasOrthogonalProjection] [R.HasOrthogonalProjection]

/-- The compressed projection, as an endomorphism of the actual head space. -/
def headCompression : R →ₗ[ℝ] R where
  toFun a := ⟨R.starProjection (P.starProjection (a : H)), R.starProjection_apply_mem _⟩
  map_add' a b := by apply Subtype.ext; simp
  map_smul' c a := by apply Subtype.ext; simp

theorem headCompression_injective
    (hhead : ∀ a : H, a ∈ R → ∃ v : H, v ∈ P ∧ R.starProjection v = a) :
    Function.Injective (headCompression P R) := by
  have hzero (a : R) (ha : headCompression P R a = 0) : a = 0 := by
    have ha0 : R.starProjection (P.starProjection (a : H)) = 0 :=
      congrArg Subtype.val ha
    have hp := Submodule.starProjection_inner_eq_zero (a : H)
      (P.starProjection (a : H)) (P.starProjection_apply_mem (a : H))
    have hr := Submodule.starProjection_inner_eq_zero
      (P.starProjection (a : H)) (a : H) a.property
    rw [inner_sub_left, real_inner_self_eq_norm_sq] at hp
    rw [ha0, sub_zero, real_inner_comm] at hr
    have hpa : P.starProjection (a : H) = 0 := by
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (P.starProjection (a : H))]
    obtain ⟨v, hv, hvhead⟩ := hhead (a : H) a.property
    have hinner := Submodule.starProjection_inner_eq_zero (a : H) v hv
    rw [hpa, sub_zero] at hinner
    have hheadinner := Submodule.starProjection_inner_eq_zero v (a : H) a.property
    rw [inner_sub_left, hvhead, real_inner_self_eq_norm_sq,
      real_inner_comm (a : H) v] at hheadinner
    apply Subtype.ext
    change (a : H) = 0
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (a : H)]
  intro a b hab
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub, hab, sub_self]

/-- Finite head surjectivity forces the compressed normal equation to have
a unique head-space solution for every prescribed head. -/
theorem exists_unique_compressed_solution [FiniteDimensional ℝ R]
    (hhead : ∀ a : H, a ∈ R → ∃ v : H, v ∈ P ∧ R.starProjection v = a)
    (x : H) (hx : x ∈ R) :
    ∃! a : R, R.starProjection (P.starProjection (a : H)) = x := by
  have hinj := headCompression_injective P R hhead
  have hsurj : Function.Surjective (headCompression P R) :=
    (LinearMap.injective_iff_surjective).mp hinj
  obtain ⟨a, ha⟩ := hsurj ⟨x, hx⟩
  refine ⟨a, congrArg Subtype.val ha, ?_⟩
  intro b hb
  apply hinj
  apply Subtype.ext
  exact hb.trans (congrArg Subtype.val ha).symm

/-- Unconditional feasibility and exact minimum once the actual finite
head-surjectivity theorem has been supplied. -/
theorem exists_minimum_raw_lift [FiniteDimensional ℝ R]
    (hhead : ∀ a : H, a ∈ R → ∃ v : H, v ∈ P ∧ R.starProjection v = a)
    (b : H) :
    ∃ a : H, a ∈ R ∧
      R.starProjection (P.starProjection a) = R.starProjection (residual P b) ∧
      R.starProjection (rawLift P b a) = 0 ∧
      residual P (rawLift P b a) = residual P b ∧
      ‖rawLift P b a‖ ^ 2 = ‖residual P b‖ ^ 2 +
        inner ℝ (R.starProjection (residual P b)) a ∧
      ∀ y : H, R.starProjection y = 0 → residual P y = residual P b →
        ‖y‖ ^ 2 = ‖rawLift P b a‖ ^ 2 + ‖y - rawLift P b a‖ ^ 2 := by
  obtain ⟨a, ha, _⟩ := exists_unique_compressed_solution P R hhead
    (R.starProjection (residual P b)) (R.starProjection_apply_mem _)
  refine ⟨a, a.property, ha, rawLift_tail P R b a ha,
    rawLift_screened P b a, rawLift_energy P R b a a.property ha, ?_⟩
  intro y hyt hys
  exact rawLift_minimum P R b a y a.property ha hyt hys

end RiemannResearch.Analysis.HeadTailResidualLift
