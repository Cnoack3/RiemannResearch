/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QRationalMinimumLimit
import RiemannResearch.RH.QRationalWeightComparison
import RiemannResearch.RH.QSquarefreePrimorialCofinality
import RiemannResearch.RH.SquarefreeStageExhaustion
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith

/-!
# Convergence of the actual rational minimizers and their weight gaps

Source: user-provided RH/CRT research handoff, 20 October 2026, Section 8,
and the exact variational identity in `QRationalMinimumLimit`.

Both nonnegative excess terms in that identity tend to zero: the rational
weight gap and the squared Q-distance from the rational optimizer to the
finite Q optimizer. Hence the actual rational minimizers converge in Q to
the projection onto the closed squarefree legal span. No coefficient bound
for the moving optimizers is assumed.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.QRationalCoprimeTail
open ZetaTwoHilbert ZetaTwoProbability
open QSquarefreePrimorialCofinality QSquarefreeInverseCapacity
open Pareto.SquarefreeStageExhaustion

/-- The exact excess over the finite Q minimum tends to zero. -/
theorem rationalMinimum_excess_tendsto_zero :
    Tendsto (fun n => rationalMinimum (primorialPeriod n) -
      zetaTwo * primorialError n) atTop (𝓝 0) := by
  have hq : Tendsto (fun n => zetaTwo * primorialError n) atTop
      (𝓝 (zetaTwo * ‖qOne -
        qSquarefreeCRTSpan.topologicalClosure.starProjection qOne‖^2)) :=
    tendsto_const_nhds.mul primorialError_tendsto
  simpa only [sub_self] using rationalMinimum_tendsto.sub hq

theorem rationalMinimizer_gap_bounds (n : ℕ) :
    0 ≤ rationalGap (primorialPeriod n)
        (divisorFit (primorialPeriod n) (rationalCoefficients (primorialPeriod n))) ∧
      rationalGap (primorialPeriod n)
        (divisorFit (primorialPeriod n) (rationalCoefficients (primorialPeriod n))) ≤
        rationalMinimum (primorialPeriod n) - zetaTwo * primorialError n := by
  have hg := (rationalGap_bounds (primorialPeriod n) (primorialPeriod_pos n)
    (divisorFit (primorialPeriod n) (rationalCoefficients (primorialPeriod n)))
    (divisorFit_residual_bound _ _)).1
  have he := rationalMinimum_exact n
  have hs := mul_nonneg zetaTwo_pos.le
    (sq_nonneg ‖rationalMinimizer (primorialPeriod n) - primorialOptimizer n‖)
  exact ⟨hg, by linarith⟩

theorem rationalMinimizer_displacement_bound (n : ℕ) :
    zetaTwo * ‖rationalMinimizer (primorialPeriod n) - primorialOptimizer n‖^2 ≤
      rationalMinimum (primorialPeriod n) - zetaTwo * primorialError n := by
  have he := rationalMinimum_exact n
  have hg := (rationalMinimizer_gap_bounds n).1
  linarith

/-- The rational weight gap vanishes along the actual moving minimizers. -/
theorem rationalMinimizer_gap_tendsto_zero :
    Tendsto (fun n => rationalGap (primorialPeriod n)
      (divisorFit (primorialPeriod n) (rationalCoefficients (primorialPeriod n))))
      atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (rationalMinimizer_gap_bounds n).1
  · intro b hb
    filter_upwards [rationalMinimum_excess_tendsto_zero.eventually (Iio_mem_nhds hb)]
      with n hn
    exact (rationalMinimizer_gap_bounds n).2.trans_lt hn

theorem rationalMinimizer_displacement_sq_tendsto_zero :
    Tendsto (fun n => ‖rationalMinimizer (primorialPeriod n) - primorialOptimizer n‖^2)
      atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (sq_nonneg _)
  · intro b hb
    have hzb : 0 < zetaTwo * b := mul_pos zetaTwo_pos hb
    filter_upwards [rationalMinimum_excess_tendsto_zero.eventually (Iio_mem_nhds hzb)]
      with n hn
    have hmul := (rationalMinimizer_displacement_bound n).trans_lt hn
    have hdiv : ‖rationalMinimizer (primorialPeriod n) - primorialOptimizer n‖^2 <
        (zetaTwo * b) / zetaTwo := by
      apply (lt_div_iff₀ zetaTwo_pos).mpr
      simpa only [mul_comm] using hmul
    simpa [ne_of_gt zetaTwo_pos] using hdiv

theorem rationalMinimizer_sub_primorial_tendsto_zero :
    Tendsto (fun n => rationalMinimizer (primorialPeriod n) - primorialOptimizer n)
      atTop (𝓝 (0 : QHilbert)) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  filter_upwards [rationalMinimizer_displacement_sq_tendsto_zero.eventually
    (Iio_mem_nhds (sq_pos_of_pos hε))] with n hn
  have hnorm : ‖rationalMinimizer (primorialPeriod n) - primorialOptimizer n‖ < ε := by
    nlinarith [norm_nonneg
      (rationalMinimizer (primorialPeriod n) - primorialOptimizer n)]
  simpa only [dist_zero_right] using hnorm

/-- The actual rational minimizers converge in the full Q norm. -/
theorem rationalMinimizer_tendsto :
    Tendsto (fun n => rationalMinimizer (primorialPeriod n)) atTop
      (𝓝 (qSquarefreeCRTSpan.topologicalClosure.starProjection qOne)) := by
  have h := rationalMinimizer_sub_primorial_tendsto_zero.add primorialOptimizer_tendsto
  simpa only [sub_add_cancel, zero_add] using h

theorem rationalMinimizer_qError_tendsto :
    Tendsto (fun n => ‖qOne - rationalMinimizer (primorialPeriod n)‖^2) atTop
      (𝓝 (‖qOne - qSquarefreeCRTSpan.topologicalClosure.starProjection qOne‖^2)) :=
  (tendsto_const_nhds.sub rationalMinimizer_tendsto).norm.pow 2

/-- Convergence to the constant target itself is exactly the remaining
squarefree-closure obligation. -/
theorem rationalMinimizer_tendsto_qOne_iff :
    Tendsto (fun n => rationalMinimizer (primorialPeriod n)) atTop (𝓝 qOne) ↔
      qOne ∈ qSquarefreeCRTSpan.topologicalClosure := by
  constructor
  · intro ht
    have he := tendsto_nhds_unique rationalMinimizer_tendsto ht
    have hm := qSquarefreeCRTSpan.topologicalClosure.starProjection_apply_mem qOne
    rwa [he] at hm
  · intro hm
    simpa only [Submodule.starProjection_eq_self_iff.mpr hm] using rationalMinimizer_tendsto

end RiemannResearch.RH.QRationalCoprimeTail
