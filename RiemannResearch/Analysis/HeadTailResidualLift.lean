import RiemannResearch.Analysis.CorrelationNormalizedCorrection

/-!
# Actual-residual weighted minimum raw lift
Source: user-provided `RH_Coupled_Residual_Corrections_2026-09-16.md`,
head/tail relaxation. The hypothesis R(Pa)=Re with a in the head space
is the normal equation for the compressed projection. Arithmetic head
surjectivity, and hence unconditional solvability, are separate obligations.
-/
noncomputable section
namespace RiemannResearch.Analysis.HeadTailResidualLift
open RiemannResearch.Analysis.ProjectionSourceImprovement
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (P R : Submodule ℝ H) [P.HasOrthogonalProjection] [R.HasOrthogonalProjection]

private theorem projected_twice (x : H) :
    P.starProjection (P.starProjection x) = P.starProjection x :=
  Submodule.starProjection_eq_self_iff.mpr (P.starProjection_apply_mem x)

def rawLift (b a : H) : H := residual P b - P.starProjection a

theorem rawLift_screened (b a : H) :
    residual P (rawLift P b a) = residual P b := by
  unfold rawLift RiemannResearch.Analysis.ProjectionSourceImprovement.residual
  rw [map_sub, map_sub, projected_twice, projected_twice]
  abel

theorem rawLift_tail (b a : H)
    (hsolve : R.starProjection (P.starProjection a) = R.starProjection (residual P b)) :
    R.starProjection (rawLift P b a) = 0 := by
  rw [rawLift, map_sub, hsolve, sub_self]

/-- The inverse term is weighted by the actual head residual.
It is not replaced by a worst-case inverse eigenvalue. -/
theorem rawLift_energy (b a : H) (ha : a ∈ R)
    (hsolve : R.starProjection (P.starProjection a) = R.starProjection (residual P b)) :
    ‖rawLift P b a‖^2 =
      ‖residual P b‖^2 + inner ℝ (R.starProjection (residual P b)) a := by
  have he := Submodule.starProjection_inner_eq_zero b (P.starProjection a)
    (P.starProjection_apply_mem a)
  have hp := Submodule.starProjection_inner_eq_zero a (P.starProjection a)
    (P.starProjection_apply_mem a)
  have hr := Submodule.starProjection_inner_eq_zero (P.starProjection a) a ha
  change inner ℝ (residual P b) (P.starProjection a) = 0 at he
  rw [inner_sub_left, real_inner_self_eq_norm_sq,
    real_inner_comm (P.starProjection a) a] at hp
  rw [inner_sub_left, hsolve] at hr
  rw [rawLift, norm_sub_sq_real, he]
  linarith

/-- Exact minimality, with the complete feasible set and no hidden head
interpolation assumption. The normal equation is an explicit hypothesis. -/
theorem rawLift_minimum (b a y : H) (ha : a ∈ R)
    (hsolve : R.starProjection (P.starProjection a) = R.starProjection (residual P b))
    (hyTail : R.starProjection y = 0) (hyScreen : residual P y = residual P b) :
    ‖y‖^2 = ‖rawLift P b a‖^2 + ‖y - rawLift P b a‖^2 := by
  let z := rawLift P b a
  have hzScreen : residual P z = residual P b := rawLift_screened P b a
  have hzTail : R.starProjection z = 0 := rawLift_tail P R b a hsolve
  have hvEq : y-z = P.starProjection y-P.starProjection z := by
    have hy : y = residual P b + P.starProjection y := sub_eq_iff_eq_add.mp hyScreen
    have hz : z = residual P b + P.starProjection z := sub_eq_iff_eq_add.mp hzScreen
    conv_lhs => rw [hy, hz]
    abel
  have hvP : y-z ∈ P := hvEq.symm ▸ P.sub_mem
    (P.starProjection_apply_mem y) (P.starProjection_apply_mem z)
  have hvR : R.starProjection (y-z) = 0 := by rw [map_sub, hyTail, hzTail, sub_self]
  have he := Submodule.starProjection_inner_eq_zero b (y-z) hvP
  have hp := Submodule.starProjection_inner_eq_zero a (y-z) hvP
  have hr := Submodule.starProjection_inner_eq_zero (y-z) a ha
  rw [hvR, sub_zero, real_inner_comm] at hr
  have ho : inner ℝ z (y-z) = 0 := by
    change inner ℝ (residual P b-P.starProjection a) (y-z) = 0
    change inner ℝ (residual P b) (y-z) = 0 at he
    rw [inner_sub_left] at hp ⊢
    linarith
  have hy : y = z+(y-z) := by abel
  conv_lhs => rw [hy]
  rw [norm_add_sq_real, ho]
  ring

end RiemannResearch.Analysis.HeadTailResidualLift
