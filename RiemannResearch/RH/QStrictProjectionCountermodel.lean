/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QDivisorLegality
import RiemannResearch.RH.QDivisibilityHilbertMoments
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

/-!
# A strict projection with matching first and second moments

Source: user-provided projection-limit discussion, 25 October 2026.
This is a countermodel to an inference from projection geometry and moment
convergence alone. Its one-dimensional space is not the full squarefree space.
-/

noncomputable section
namespace RiemannResearch.RH.QStrictProjectionCountermodel
open ZetaTwoHilbert QDivisibilityDensity QDivisorLegality

def oddSpace : Submodule ℝ QHilbert :=
  Submodule.span ℝ ({qResidue 2} : Set QHilbert)

instance oddSpace_finiteDimensional : FiniteDimensional ℝ oddSpace :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_singleton _)

theorem oddSpace_projection :
    oddSpace.starProjection qOne = (2 : ℝ) • qResidue 2 := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (oddSpace.smul_mem (2 : ℝ) (Submodule.subset_span (by simp)))
  intro y hy
  rw [← qDivisor_two_eq]
  induction hy using Submodule.span_induction with
  | mem y hy =>
      simp only [Set.mem_singleton_iff] at hy
      subst y
      rw [real_inner_comm]
      exact qResidue_inner_qDivisor_eq_zero 2 2 (by decide) (dvd_refl _)
  | zero => simp
  | add y z hy hz ihy ihz => rw [inner_add_right, ihy, ihz, add_zero]
  | smul c y hy ih => rw [real_inner_smul_right, ih, mul_zero]

theorem oddSpace_projection_eq_one_sub_even :
    oddSpace.starProjection qOne = qOne - qDivisor 2 := by
  rw [oddSpace_projection, qDivisor_two_eq]
  abel

theorem oddSpace_projection_mean :
    inner ℝ qOne (oddSpace.starProjection qOne) = (3 / 4 : ℝ) := by
  rw [oddSpace_projection_eq_one_sub_even, inner_sub_right,
    real_inner_self_eq_norm_sq, qOne_norm_sq,
    qOne_inner_qDivisor 2 (by decide)]
  norm_num

theorem oddSpace_projection_norm_sq :
    ‖oddSpace.starProjection qOne‖ ^ 2 = (3 / 4 : ℝ) := by
  rw [oddSpace_projection_eq_one_sub_even, norm_sub_sq_real, qOne_norm_sq,
    qDivisor_norm_sq 2 (by decide), qOne_inner_qDivisor 2 (by decide)]
  norm_num

theorem oddSpace_projection_ne_one : oddSpace.starProjection qOne ≠ qOne := by
  intro heq
  have h := oddSpace_projection_norm_sq
  rw [heq, qOne_norm_sq] at h
  norm_num at h

theorem oddSpace_projection_variance :
    ‖oddSpace.starProjection qOne -
      (inner ℝ qOne (oddSpace.starProjection qOne)) • qOne‖ ^ 2 =
      (3 / 16 : ℝ) := by
  rw [oddSpace_projection_mean, norm_sub_sq_real, oddSpace_projection_norm_sq,
    norm_smul, qOne_norm, real_inner_smul_right, real_inner_comm,
    oddSpace_projection_mean]
  norm_num

/-- Equality of first and second moments is compatible with a strict projection. -/
theorem strict_projection_matching_moments :
    oddSpace.starProjection qOne ≠ qOne ∧
      inner ℝ qOne (oddSpace.starProjection qOne) =
        ‖oddSpace.starProjection qOne‖ ^ 2 := by
  exact ⟨oddSpace_projection_ne_one,
    oddSpace_projection_mean.trans oddSpace_projection_norm_sq.symm⟩

/-- The proposed extra squaring step fails even for a nonnegative projection. -/
theorem oddSpace_secondMoment_ne_mean_sq :
    ‖oddSpace.starProjection qOne‖ ^ 2 ≠
      (inner ℝ qOne (oddSpace.starProjection qOne)) ^ 2 := by
  rw [oddSpace_projection_norm_sq, oddSpace_projection_mean]
  norm_num

end RiemannResearch.RH.QStrictProjectionCountermodel
