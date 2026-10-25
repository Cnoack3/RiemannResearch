/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QHilbertConvergence
import RiemannResearch.RH.QProjectionMoments
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.QSquarefreeWeakCompactness
import RiemannResearch.RH.QParityProjectionDefect
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import Mathlib.Tactic.Linarith

/-!
# Pointwise and moment consequences of the squarefree projection limit

Source: the user's L1, pointwise, and second-moment discussion, 25 October 2026.
The established strong limit is the projection of qOne onto the actual closed
squarefree span. None of these convergence statements identifies it with qOne.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QSquarefreeProjectionLimits
open ZetaTwoHilbert ZetaTwoOptimizerStage
open RiemannResearch.Analysis.ExhaustiveWalk

theorem optimizer_pointwise_tendsto (k : ℕ) :
    Tendsto (fun M => qSequence (optimizer M) k) atTop
      (𝓝 (qSequence (closure.starProjection qOne) k)) :=
  qSequence_tendsto_of_tendsto optimizer_tendsto k

theorem optimizer_L1_tendsto :
    Tendsto (fun M => qL1 (optimizer M - closure.starProjection qOne))
      atTop (𝓝 0) :=
  qL1_sub_tendsto_zero optimizer_tendsto

theorem optimizer_square_L1_tendsto :
    Tendsto (fun M => qSquareL1Dist (optimizer M) (closure.starProjection qOne))
      atTop (𝓝 0) :=
  qSquareL1Dist_tendsto_zero optimizer_tendsto

theorem optimizer_firstMoment_tendsto :
    Tendsto (fun M => ∑' k, positiveQWeight k * qSequence (optimizer M) k)
      atTop (𝓝 (∑' k, positiveQWeight k *
        qSequence (closure.starProjection qOne) k)) :=
  qFirstMoment_tendsto optimizer_tendsto

theorem optimizer_secondMoment_tendsto :
    Tendsto (fun M => ∑' k, positiveQWeight k * (qSequence (optimizer M) k)^2)
      atTop (𝓝 (∑' k, positiveQWeight k *
        (qSequence (closure.starProjection qOne) k)^2)) :=
  qSecondMoment_tendsto optimizer_tendsto

theorem optimizer_secondMoment_monotone :
    Monotone (fun M => ∑' k, positiveQWeight k * (qSequence (optimizer M) k)^2) := by
  simp_rw [← qNorm_weighted_sq]
  intro M N hMN
  have hm := QSquarefreeWeakCompactness.optimizer_residual_pythagoras M
  have hn := QSquarefreeWeakCompactness.optimizer_residual_pythagoras N
  have he : error N ≤ error M :=
    walkError_antitone squarefreeAtom id qOne hMN
  unfold error at he
  linarith

theorem residual_pointwise_tendsto (k : ℕ) :
    Tendsto (fun M => qSequence (residual M) k) atTop
      (𝓝 (qSequence limitingResidual k)) :=
  qSequence_tendsto_of_tendsto residual_tendsto k

theorem residual_L1_tendsto :
    Tendsto (fun M => qL1 (residual M - limitingResidual)) atTop (𝓝 0) :=
  qL1_sub_tendsto_zero residual_tendsto

theorem residual_square_L1_tendsto :
    Tendsto (fun M => qSquareL1Dist (residual M) limitingResidual) atTop (𝓝 0) :=
  qSquareL1Dist_tendsto_zero residual_tendsto

theorem optimizer_firstMoment_eq_secondMoment (M : ℕ) :
    (∑' k, positiveQWeight k * qSequence (optimizer M) k) =
      ∑' k, positiveQWeight k * (qSequence (optimizer M) k)^2 := by
  rw [← qOne_inner_weighted, ← qNorm_weighted_sq, real_inner_comm]
  exact qProjection_inner_qOne (stage M)

theorem limitingProjection_firstMoment_eq_secondMoment :
    (∑' k, positiveQWeight k * qSequence (closure.starProjection qOne) k) =
      ∑' k, positiveQWeight k * (qSequence (closure.starProjection qOne) k)^2 := by
  rw [← qOne_inner_weighted, ← qNorm_weighted_sq, real_inner_comm]
  exact qProjection_inner_qOne closure

theorem limitingResidual_mean_eq_energy :
    inner ℝ limitingResidual qOne = ‖limitingResidual‖ ^ 2 :=
  qResidual_inner_qOne closure

theorem limitingResidual_firstMoment_eq_energy :
    (∑' k, positiveQWeight k * qSequence limitingResidual k) =
      ‖limitingResidual‖ ^ 2 := by
  rw [← qOne_inner_weighted, real_inner_comm]
  exact limitingResidual_mean_eq_energy

theorem limitingProjection_mean_eq_one_sub_error :
    inner ℝ qOne (closure.starProjection qOne) = 1 - ‖limitingResidual‖ ^ 2 := by
  rw [real_inner_comm, qProjection_inner_qOne closure]
  have h := qProjection_error_eq closure
  change ‖limitingResidual‖ ^ 2 = 1 - ‖closure.starProjection qOne‖ ^ 2 at h
  linarith

/-- Exact variance of the actual limiting projection; no target membership is assumed. -/
theorem limitingProjection_variance_eq :
    ‖closure.starProjection qOne -
      (inner ℝ qOne (closure.starProjection qOne)) • qOne‖ ^ 2 =
      ‖limitingResidual‖ ^ 2 * (1 - ‖limitingResidual‖ ^ 2) :=
  qProjection_variance_eq closure

/-- A strict projection is algebraically consistent with a positive finite residual energy. -/
theorem strict_projection_error_bounds (h : closure.starProjection qOne ≠ qOne) :
    0 < ‖limitingResidual‖ ^ 2 ∧ ‖limitingResidual‖ ^ 2 < (1 / 4 : ℝ) := by
  refine ⟨?_, QParityProjectionDefect.limiting_error_lt_quarter⟩
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro hz
  apply h
  change qOne - closure.starProjection qOne = 0 at hz
  exact (sub_eq_zero.mp hz).symm

theorem strict_projection_mean_bounds (h : closure.starProjection qOne ≠ qOne) :
    (3 / 4 : ℝ) < inner ℝ qOne (closure.starProjection qOne) ∧
      inner ℝ qOne (closure.starProjection qOne) < 1 := by
  have hd := strict_projection_error_bounds h
  rw [limitingProjection_mean_eq_one_sub_error]
  constructor <;> linarith

theorem strict_projection_variance_pos (h : closure.starProjection qOne ≠ qOne) :
    0 < ‖closure.starProjection qOne -
      (inner ℝ qOne (closure.starProjection qOne)) • qOne‖ ^ 2 := by
  rw [limitingProjection_variance_eq]
  have hd := strict_projection_error_bounds h
  exact mul_pos hd.1 (by linarith)

end RiemannResearch.RH.QSquarefreeProjectionLimits
