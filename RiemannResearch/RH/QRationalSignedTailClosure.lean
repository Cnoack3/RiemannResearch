/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteWeightedTailCharge
import RiemannResearch.RH.QRationalSignedTailLimit
import RiemannResearch.RH.QRationalMinimizerConvergence
import RiemannResearch.RH.QRationalWeightComparison
import RiemannResearch.RH.QSquarefreePrimorialCofinality
import RiemannResearch.RH.SquarefreeStageExhaustion
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Cofinal signed-tail budgets and the actual squarefree closure

Source: user-provided CRT/squarefree-closure research agenda and its
20 October 2026 continuation. This module assembles the attained rational
minimum, its complete-Q remainder, and its signed-tail identity.

The exact identities are unconditional. The cofinal arithmetic budget is
proved equivalent to constant-target closure; it is not supplied here.
No finite computation, including the seventh-primorial checks, proves that
budget for arbitrarily large stages.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QRationalCoprimeTail
open ZetaTwoHilbert ZetaTwoProbability
open QSquarefreePrimorialCofinality
open Pareto.SquarefreeStageExhaustion
open RiemannResearch.Analysis.FiniteWeightedTailCharge

/-- The signed charge completes the exact full-Q finite minimum,
optimizer displacement, and rational-weight gap to the endpoint. -/
theorem rationalSignedTail_complete_identity (n : ℕ) :
    zetaTwo * primorialError n +
      zetaTwo * ‖rationalMinimizer (primorialPeriod n) - primorialOptimizer n‖^2 +
      rationalGap (primorialPeriod n)
        (divisorFit (primorialPeriod n) (rationalCoefficients (primorialPeriod n))) +
      rationalSignedTail (primorialPeriod n) =
      5 * (Nat.totient (primorialPeriod n) : ℝ) /
        (3 * (primorialPeriod n : ℝ)^2) := by
  rw [← rationalMinimum_exact]
  exact rationalMinimum_signedTail_exact _ (primorialPeriod_pos n)

/-- A finite signed budget controls the complete-Q error of the actual
rational minimizer, not only the optimal Q distance. -/
theorem rationalMinimizer_qError_le_of_signed_budget (n : ℕ) {θ ε : ℝ}
    (hθ : θ < 1)
    (hbudget : -θ * rationalMinimum (primorialPeriod n) - ε ≤
      rationalSignedTail (primorialPeriod n)) :
    ‖qOne - rationalMinimizer (primorialPeriod n)‖^2 ≤
      (5 * (Nat.totient (primorialPeriod n) : ℝ) /
        (3 * (primorialPeriod n : ℝ)^2) + ε) / ((1 - θ) * zetaTwo) := by
  have hbound := absorption_bound
    (rationalMinimum_signedTail_exact _ (primorialPeriod_pos n)) hbudget hθ
  have hgap := (rationalMinimizer_gap_bounds n).1
  have he := rationalMinimum_exact n
  have hq := primorial_qError_exact (rationalMinimizer_mem n)
  have hle : zetaTwo * ‖qOne - rationalMinimizer (primorialPeriod n)‖^2 ≤
      rationalMinimum (primorialPeriod n) := by
    rw [hq]
    nlinarith
  apply (le_div_iff₀ (mul_pos (sub_pos.mpr hθ) zetaTwo_pos)).mpr
  have habs := (le_div_iff₀ (sub_pos.mpr hθ)).mp hbound
  have hm := mul_le_mul_of_nonneg_left hle (sub_pos.mpr hθ).le
  nlinarith

/-- For any fixed theta below one, cofinal signed absorption is exactly
constant-target membership in the squarefree closed span. This is a
conditional research reduction; the quantified arithmetic budget is open. -/
theorem cofinal_signed_absorption_iff_closure (θ : ℝ) (hθ : θ < 1) :
    (∀ ε > 0, ∀ N : ℕ, ∃ n, N ≤ n ∧
      -θ * rationalMinimum (primorialPeriod n) - ε ≤
        rationalSignedTail (primorialPeriod n)) ↔
      qOne ∈ qSquarefreeCRTSpan.topologicalClosure := by
  have hgeneric := cofinal_absorption_iff_zero_limit
    (fun n => rationalMinimum_signedTail_exact _ (primorialPeriod_pos n))
    rationalMinimum_tendsto rationalCoprimeBoundary_tendsto_zero
    (mul_nonneg zetaTwo_pos.le (sq_nonneg _)) hθ
  rw [hgeneric]
  constructor
  · intro hz
    have hzero : ‖qOne -
        qSquarefreeCRTSpan.topologicalClosure.starProjection qOne‖^2 = 0 :=
      (mul_eq_zero.mp hz).resolve_left (ne_of_gt zetaTwo_pos)
    rw [sq_eq_zero_iff, norm_eq_zero, sub_eq_zero, eq_comm,
      Submodule.starProjection_eq_self_iff] at hzero
    exact hzero
  · intro hmem
    rw [Submodule.starProjection_eq_self_iff.mpr hmem, sub_self, norm_zero]
    ring

/-- Any vanishing additive error and cofinally valid fixed-factor budget
discharge the closure obligation. Both hypotheses are explicit. -/
theorem closure_of_cofinal_signed_budget {θ : ℝ} (hθ : θ < 1)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hbudget : ∀ N : ℕ, ∃ n, N ≤ n ∧
      -θ * rationalMinimum (primorialPeriod n) - ε n ≤
        rationalSignedTail (primorialPeriod n)) :
    qOne ∈ qSquarefreeCRTSpan.topologicalClosure := by
  apply (cofinal_signed_absorption_iff_closure θ hθ).mp
  intro δ hδ N
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hε.eventually (Iio_mem_nhds hδ))
  obtain ⟨n, hn, hb⟩ := hbudget (max N K)
  refine ⟨n, (le_max_left _ _).trans hn, ?_⟩
  have he := hK n ((le_max_right _ _).trans hn)
  linarith

end RiemannResearch.RH.QRationalCoprimeTail
