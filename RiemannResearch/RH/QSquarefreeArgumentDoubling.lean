/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QArgumentDoubling
import RiemannResearch.RH.QDoublingMeasureChange
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import RiemannResearch.RH.QSquarefreeDyadicResampling
import RiemannResearch.RH.QParityConditionalTarget
import RiemannResearch.RH.ZetaTwoOptimizerStage
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-!
# Physical doubling detects the actual squarefree residual by its mean alone

Source: independently derived from the user's doubling research request,
27 October 2026. With e = ‖r‖², the exact physical doubling drift is 3e.
The full defect has the orthogonal decomposition 9e² plus a squared norm.
A nonpositive mean drift would imply RH. Providing that inequality for the
actual limiting residual remains Open; no invariance premise is discharged.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QSquarefreeArgumentDoubling
open ZetaTwoHilbert ZetaTwoParitySignal ZetaTwoOptimizerStage QArgumentDoubling

private theorem residual_mean (S : Submodule ℝ QHilbert) [S.HasOrthogonalProjection] :
    inner ℝ (qOne - S.starProjection qOne) qOne = ‖qOne - S.starProjection qOne‖ ^ 2 := by
  have hz := S.starProjection_inner_eq_zero qOne (S.starProjection qOne)
    (S.starProjection_apply_mem qOne)
  have he := real_inner_self_eq_norm_sq (qOne - S.starProjection qOne)
  rw [inner_sub_right, hz, sub_zero] at he
  exact he

/-- Every projection space containing g₂ has this exact mean inflation. -/
theorem projection_residual_doubling_mean
    (S : Submodule ℝ QHilbert) [S.HasOrthogonalProjection] (h2 : qResidue 2 ∈ S) :
    inner ℝ (doubling (qOne - S.starProjection qOne)) qOne =
      4 * ‖qOne - S.starProjection qOne‖ ^ 2 := by
  rw [doubling_mean, qEven, qOdd, inner_sub_right, real_inner_smul_right,
    S.starProjection_inner_eq_zero qOne (qResidue 2) h2,
    mul_zero, sub_zero, residual_mean]

def limitingDoublingDefect : QHilbert := doubling limitingResidual - limitingResidual

theorem limiting_doubling_mean :
    inner ℝ (doubling limitingResidual) qOne = 4 * ‖limitingResidual‖ ^ 2 :=
  projection_residual_doubling_mean closure QParityConditionalTarget.qResidue_two_mem_closure

/-- Complete signed drift, rather than just an absolute-value estimate. -/
theorem limiting_doubling_defect_mean :
    inner ℝ limitingDoublingDefect qOne = 3 * ‖limitingResidual‖ ^ 2 := by
  rw [limitingDoublingDefect, inner_sub_left, limiting_doubling_mean]
  change 4 * ‖limitingResidual‖ ^ 2 -
    inner ℝ (qOne - closure.starProjection qOne) qOne = _
  rw [residual_mean]
  change 4 * ‖limitingResidual‖ ^ 2 - ‖limitingResidual‖ ^ 2 =
    3 * ‖limitingResidual‖ ^ 2
  ring

/-- Exact full-norm decomposition for physical doubling. -/
theorem limiting_doubling_defect_energy_exact :
    ‖limitingDoublingDefect‖ ^ 2 = 9 * (‖limitingResidual‖ ^ 2) ^ 2 +
      ‖limitingDoublingDefect - (3 * ‖limitingResidual‖ ^ 2) • qOne‖ ^ 2 := by
  rw [norm_sub_sq_real, real_inner_smul_right, limiting_doubling_defect_mean,
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, qOne_norm_sq]
  ring

theorem limiting_doubling_defect_energy_lower :
    9 * (‖limitingResidual‖ ^ 2) ^ 2 ≤ ‖limitingDoublingDefect‖ ^ 2 := by
  rw [limiting_doubling_defect_energy_exact]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Only a scalar inequality is needed, but it is still an Open arithmetic obligation. -/
theorem limiting_mean_nonincrease_iff :
    inner ℝ (doubling limitingResidual) qOne ≤ inner ℝ limitingResidual qOne ↔
      limitingResidual = 0 := by
  rw [limiting_doubling_mean]
  change 4 * ‖limitingResidual‖ ^ 2 ≤
    inner ℝ (qOne - closure.starProjection qOne) qOne ↔ _
  rw [residual_mean]
  change 4 * ‖limitingResidual‖ ^ 2 ≤ ‖limitingResidual‖ ^ 2 ↔ limitingResidual = 0
  constructor
  · intro h
    have hz : ‖limitingResidual‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖limitingResidual‖]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  · intro h
    simp [h]

/-- Conditional research reduction, without assuming whole-space invariance. -/
theorem riemannHypothesis_of_limiting_mean_nonincrease
    (h : inner ℝ (doubling limitingResidual) qOne ≤ inner ℝ limitingResidual qOne) :
    RiemannHypothesis := by
  have hr := limiting_mean_nonincrease_iff.mp h
  apply QSquarefreeDyadicResampling.riemannHypothesis_of_limiting_dilation_invariant
  intro n
  rw [hr]
  change qSequenceLinear 0 (2 * n) = qSequenceLinear 0 n
  simp only [map_zero, Pi.zero_apply]

theorem riemannHypothesis_of_limiting_pointwise_nonincrease
    (h : ∀ n, qSequence limitingResidual (2 * n) ≤ qSequence limitingResidual n) :
    RiemannHypothesis :=
  riemannHypothesis_of_limiting_mean_nonincrease
    (doubling_mean_le_of_pointwise limitingResidual h)

/-- A nonzero residual necessarily increases on at least one doubling edge. -/
theorem exists_doubling_increase_of_residual_ne_zero (hr : limitingResidual ≠ 0) :
    ∃ n, qSequence limitingResidual n < qSequence limitingResidual (2 * n) := by
  by_contra h
  push Not at h
  exact hr (limiting_mean_nonincrease_iff.mp
    (doubling_mean_le_of_pointwise limitingResidual h))

def stageDoublingDefect (N : ℕ) : QHilbert := doubling (residual N) - residual N

theorem stageDoublingDefect_tendsto :
    Tendsto stageDoublingDefect atTop (𝓝 limitingDoublingDefect) :=
  (doubling.continuous.tendsto limitingResidual |>.comp residual_tendsto).sub residual_tendsto

/-- A stagewise upper estimate converging to zero would close the reduction. -/
theorem stageDoublingDefect_tendsto_zero_iff :
    Tendsto stageDoublingDefect atTop (𝓝 0) ↔ limitingResidual = 0 := by
  constructor
  · intro h
    have hz := tendsto_nhds_unique stageDoublingDefect_tendsto h
    have he := limiting_doubling_defect_mean
    rw [hz, inner_zero_left] at he
    apply norm_eq_zero.mp
    nlinarith [sq_nonneg ‖limitingResidual‖]
  · intro h
    have hz : limitingDoublingDefect = 0 := by simp [limitingDoublingDefect, h]
    simpa only [hz] using stageDoublingDefect_tendsto

/-- The existing hard correction is exactly the projected change-of-measure
adjoint discrepancy after physical doubling. Projection remains essential. -/
theorem correction_eq_doubled_adjointDefect :
    QSquarefreeSmoothedProjection.correction =
      (1 / 2 : ℝ) • closure.starProjection
        (doubling (QDoublingMeasureChange.adjointDefect limitingResidual)) := by
  rw [QDoublingMeasureChange.doubling_adjointDefect, map_smul, smul_smul]
  norm_num [QSquarefreeSmoothedProjection.correction]

end RiemannResearch.RH.QSquarefreeArgumentDoubling
