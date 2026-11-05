/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QSquarefreeFiniteDisplacement
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.RH.QParetoClosedProjectionComparison
import RiemannResearch.RH.QParetoMetric
import RiemannResearch.RH.QSquarefreeMeasureRigidity
import RiemannResearch.RH.QSquarefreeDisplacementRigidity
import Mathlib.Tactic.Linarith

/-! # A cofinal criterion from the gap between finite projection errors

The Q and Pareto projections use the same finite squarefree span. The signed
difference of minimum squared errors has an exact nonnegative decomposition.
For the underlying discrete squarefree closure criterion see B. Bagchi,
*Proc. Indian Acad. Sci. (Math. Sci.)* 116 (2006), Remark 8,
https://doi.org/10.1007/BF02829783. The argument here uses the project's
metric-comparison and capacity theorems. The cofinal smallness of the gap
for the actual finite stages is open. -/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QSquarefreeFiniteDisplacement
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QParetoEquivalence QParetoClosedProjectionComparison QSquarefreeMeasureRigidity
open QSquarefreeDisplacementRigidity ZetaTwoOptimizerStage

/-- The difference between the two squared minimum errors, in the unnormalized
Q scale. Both projections use conductors through `N + 1`. -/
def finiteMetricGap (N : ℕ) : ℝ :=
  zetaTwo * ‖residual N‖ ^ 2 - ‖toPareto (qOne - finitePFit N)‖ ^ 2

/-- Pythagoras in the Pareto norm and the change of measure decompose the gap
into the squared displacement and the metric correction of the Q residual. -/
theorem finiteMetricGap_exact (N : ℕ) :
    finiteMetricGap N = ‖toPareto (finiteDisplacement N)‖ ^ 2 +
      QParetoMetric.metricCorrection (residual N) := by
  have h := error_lower_identity (stage N) (paretoStage N)
    (toPareto_mem_paretoStage_iff N) qOne
  change zetaTwo * ‖residual N‖ ^ 2 = ‖toPareto (qOne - finitePFit N)‖ ^ 2 +
    ‖toPareto (finiteDisplacement N)‖ ^ 2 + QParetoMetric.metricCorrection (residual N) at h
  unfold finiteMetricGap
  linarith only [h]

/-- Every individual finite gap is strictly positive. -/
theorem finiteMetricGap_pos (N : ℕ) : 0 < finiteMetricGap N := by
  have hx : qOne ≠ qFit (stage N) qOne := fun h =>
    residual_ne_zero N (sub_eq_zero.mpr h)
  exact sub_pos.mpr (error_strict (stage N) (paretoStage N)
    (toPareto_mem_paretoStage_iff N) qOne hx)

theorem finiteMetricGap_tendsto :
    Tendsto finiteMetricGap atTop
      (𝓝 (zetaTwo * ‖limitingResidual‖ ^ 2 - ‖toPareto pResidual‖ ^ 2)) := by
  have hp : Tendsto (fun N => toPareto (qOne - finitePFit N)) atTop
      (𝓝 (toPareto pResidual)) :=
    (paretoEquiv.continuous.tendsto pResidual).comp
      (tendsto_const_nhds.sub finitePFit_tendsto)
  exact ((residual_tendsto.norm.pow 2).const_mul zetaTwo).sub (hp.norm.pow 2)

/-- Arbitrarily small upper bounds on the gap on cofinal finite stages detect
whether the constant belongs to the closed squarefree span. -/
theorem residual_zero_iff_cofinal_finiteMetricGap :
    limitingResidual = 0 ↔
      ∀ ε : ℝ, 0 < ε → ∃ᶠ N in atTop, finiteMetricGap N ≤ ε := by
  constructor
  · intro hr ε hε
    have hp : pResidual = 0 := by
      rw [pResidual_eq_residual_add_displacement, hr,
        displacement_eq_zero_of_residual_eq_zero hr, add_zero]
    have hz : toPareto (0 : QHilbert) = 0 := toParetoLinear.map_zero
    have ht : Tendsto finiteMetricGap atTop (𝓝 0) := by
      simpa only [hr, hp, hz, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
        sub_zero] using finiteMetricGap_tendsto
    exact (ht.eventually (gt_mem_nhds hε)).frequently.mono (fun _ h => h.le)
  · intro hgap
    by_contra hr
    have hx : qOne ≠ qFit closure qOne := fun h => hr (sub_eq_zero.mpr h)
    let L := zetaTwo * ‖limitingResidual‖ ^ 2 - ‖toPareto pResidual‖ ^ 2
    have hL : 0 < L := sub_pos.mpr
      (error_strict closure paretoSquarefreeClosure
        toPareto_mem_paretoSquarefreeClosure_iff qOne hx)
    have hhalf : L / 2 < L := by linarith
    have he : ∀ᶠ N in atTop, L / 2 < finiteMetricGap N :=
      finiteMetricGap_tendsto.eventually (lt_mem_nhds hhalf)
    obtain ⟨N, hlo, hhi⟩ := ((hgap (L / 2) (by linarith)).and_eventually he).exists
    exact (not_lt_of_ge hlo) hhi

/-- A cofinal gap condition on the two finite minimum errors suffices for RH. -/
theorem riemannHypothesis_of_cofinal_finiteMetricGap
    (hgap : ∀ ε : ℝ, 0 < ε → ∃ᶠ N in atTop, finiteMetricGap N ≤ ε) :
    RiemannHypothesis := by
  have hr := residual_zero_iff_cofinal_finiteMetricGap.mpr hgap
  have hm : qOne ∈ closure :=
    Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hr).symm
  exact QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
    (QSquarefreeCapacity.capacity_tendsto_iff_optimizer_closure.mpr hm)

end RiemannResearch.RH.QSquarefreeFiniteDisplacement
