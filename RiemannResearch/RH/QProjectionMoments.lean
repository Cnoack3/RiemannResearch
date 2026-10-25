/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.UnitVectorVariance
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Ring

/-!
# Exact normalized-constant projection moments

Source: the user's first- and second-moment discussion, 25 October 2026.
These generic Hilbert identities retain the complete residual energy.
-/

noncomputable section
namespace RiemannResearch.RH.ZetaTwoHilbert

variable (V : Submodule ℝ QHilbert) [V.HasOrthogonalProjection]

/-- The mean of a projected constant equals its second moment. -/
theorem qProjection_inner_qOne :
    inner ℝ (V.starProjection qOne) qOne = ‖V.starProjection qOne‖ ^ 2 := by
  have ho := Submodule.starProjection_inner_eq_zero qOne (V.starProjection qOne)
    (V.starProjection_apply_mem qOne)
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at ho
  rw [real_inner_comm] at ho
  exact (sub_eq_zero.mp ho)

/-- The residual's mean equals its complete squared Q norm. -/
theorem qResidual_inner_qOne :
    inner ℝ (qOne - V.starProjection qOne) qOne =
      ‖qOne - V.starProjection qOne‖ ^ 2 := by
  have ho := Submodule.starProjection_inner_eq_zero qOne (V.starProjection qOne)
    (V.starProjection_apply_mem qOne)
  calc
    _ = inner ℝ (qOne - V.starProjection qOne) (qOne - V.starProjection qOne) := by
      rw [inner_sub_right, ho, sub_zero]
    _ = _ := real_inner_self_eq_norm_sq _

/-- Exact energy identity, including any nonzero limiting residual. -/
theorem qProjection_error_eq :
    ‖qOne - V.starProjection qOne‖ ^ 2 = 1 - ‖V.starProjection qOne‖ ^ 2 := by
  have h := qResidual_inner_qOne V
  rw [inner_sub_left, real_inner_self_eq_norm_sq, qOne_norm_sq,
    qProjection_inner_qOne V] at h
  exact h.symm

/-- A strict projection has nonzero variance; the first/second moment equality
does not force a constant or an indicator. -/
theorem qProjection_variance_eq :
    ‖V.starProjection qOne -
      (inner ℝ qOne (V.starProjection qOne)) • qOne‖ ^ 2 =
      ‖qOne - V.starProjection qOne‖ ^ 2 *
        (1 - ‖qOne - V.starProjection qOne‖ ^ 2) := by
  have hm : inner ℝ qOne (V.starProjection qOne) = ‖V.starProjection qOne‖ ^ 2 := by
    rw [real_inner_comm]
    exact qProjection_inner_qOne V
  rw [hm, norm_sub_sq_real, real_inner_smul_right, qProjection_inner_qOne V,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, qOne_norm_sq]
  simp only [qProjection_error_eq V]
  ring


/-- Matching residual first and second moments leaves the exact variance delta*(1-delta). -/
theorem qResidual_variance_eq (V : Submodule ℝ QHilbert) [V.HasOrthogonalProjection] :
    ‖(qOne - V.starProjection qOne) -
      ‖qOne - V.starProjection qOne‖ ^ 2 • qOne‖ ^ 2 =
      ‖qOne - V.starProjection qOne‖ ^ 2 *
        (1 - ‖qOne - V.starProjection qOne‖ ^ 2) := by
  have h := RiemannResearch.Analysis.UnitVectorVariance.centered_norm_sq
    qOne (qOne - V.starProjection qOne) qOne_norm_sq
  have hm : inner ℝ qOne (qOne - V.starProjection qOne) =
      ‖qOne - V.starProjection qOne‖ ^ 2 := by
    calc
      _ = inner ℝ (qOne - V.starProjection qOne) qOne := real_inner_comm _ _
      _ = _ := qResidual_inner_qOne V
  rw [hm] at h
  rw [h]
  ring

end RiemannResearch.RH.ZetaTwoHilbert
