/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QFiniteEighthMoment
import RiemannResearch.RH.ZetaTwoCoordinateDual
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Pareto residual representers for the finite matched displacement

Source: the matched finite-stage problem in the user's eighth-moment handoff.
The projection and adjoint identities are standard Hilbert space identities.
Orthogonality removes the Pareto-stage part of the transferred representer
before Cauchy--Schwarz is applied.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QSquarefreeFiniteDisplacement
open Pareto ZetaTwoHilbert ZetaTwoOptimizerStage ZetaTwoParetoTransfer
open QParetoEquivalence QParetoClosedProjectionComparison

/-- The Pareto residual of the Q-stage evaluation representer transferred by adjoint. -/
def finiteParetoDualKernel (N n : ℕ) : ThresholdHilbert :=
  let u := toQCLM.adjoint ((stage N).starProjection (qSiteRiesz n))
  u - (paretoStage N).starProjection u

/-- An exact signed pairing for the actual displacement at a positive site. -/
theorem finiteDisplacement_eq_paretoDual_pairing (N n : ℕ) (hn : 0 < n) :
    qSequence (finiteDisplacement N) n =
      inner ℝ (toPareto (qOne - finitePFit N)) (finiteParetoDualKernel N n) := by
  let x := qOne - finitePFit N
  let k := (stage N).starProjection (qSiteRiesz n)
  let u := toQCLM.adjoint k
  have hk : k ∈ stage N := (stage N).starProjection_apply_mem _
  have hq : inner ℝ (residual N) k = 0 := by
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal hk (residual_mem_orthogonal N)
  have hsite : inner ℝ (finiteDisplacement N) (qSiteRiesz n - k) = 0 :=
    Submodule.inner_right_of_mem_orthogonal (finiteDisplacement_mem N)
      (Submodule.sub_starProjection_mem_orthogonal (K := stage N) (qSiteRiesz n))
  have hx : toPareto x ∈ (paretoStage N)ᗮ := by
    change toPareto (qOne - pFit (paretoStage N) qOne) ∈ (paretoStage N)ᗮ
    rw [toPareto_sub, toPareto_pFit]
    exact Submodule.sub_starProjection_mem_orthogonal (K := paretoStage N) _
  have hp : inner ℝ (toPareto x) ((paretoStage N).starProjection u) = 0 := by
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal ((paretoStage N).starProjection_apply_mem _) hx
  calc
    qSequence (finiteDisplacement N) n = inner ℝ (finiteDisplacement N) (qSiteRiesz n) := by
      rw [real_inner_comm, qSiteRiesz_inner n hn]
    _ = inner ℝ (finiteDisplacement N) k := by
      rw [inner_sub_right] at hsite
      exact sub_eq_zero.mp hsite
    _ = inner ℝ x k := by
      dsimp only [x]
      rw [finitePResidual_eq, inner_add_left, hq, zero_add]
    _ = inner ℝ (toPareto x) u := by
      dsimp only [u]
      rw [ContinuousLinearMap.adjoint_inner_right]
      change inner ℝ x k = inner ℝ (toQ (toPareto x)) k
      rw [toQ_toPareto]
    _ = inner ℝ (toPareto x) (u - (paretoStage N).starProjection u) := by
      rw [inner_sub_right, hp, sub_zero]

/-- The dual bound uses the Pareto residual norm at the same stage as the output head. -/
theorem eighthHead_finiteDisplacement_le_paretoDual (N H : ℕ) :
    eighthHead (finiteDisplacement N) H ≤
      ‖toPareto (qOne - finitePFit N)‖ ^ 8 *
        ∑ n ∈ Finset.range (H + 1), ‖finiteParetoDualKernel N n‖ ^ 8 / (n : ℝ) ^ 2 := by
  let A := ‖toPareto (qOne - finitePFit N)‖
  unfold eighthHead
  calc
    _ ≤ ∑ n ∈ Finset.range (H + 1),
        (A * ‖finiteParetoDualKernel N n‖) ^ 8 / (n : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro n _
      by_cases hz : n = 0
      · simp [hz]
      · have hn : 0 < n := Nat.pos_of_ne_zero hz
        have hc : |qSequence (finiteDisplacement N) n| ≤ A * ‖finiteParetoDualKernel N n‖ := by
          rw [finiteDisplacement_eq_paretoDual_pairing N n hn]
          exact abs_real_inner_le_norm _ _
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        gcongr
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      dsimp only [A]
      simp only [mul_pow, div_eq_mul_inv, mul_assoc]

/-- A cofinal bound for the residual times the Pareto dual head suffices. -/
theorem riemannHypothesis_of_frequent_paretoDual_eighth
    (happrox : HasSubcriticalApproximation) (C : ℝ)
    (h : ∃ᶠ N : ℕ in atTop, ‖toPareto (qOne - finitePFit N)‖ ^ 8 *
      (∑ n ∈ Finset.range (N + 1), ‖finiteParetoDualKernel N n‖ ^ 8 / (n : ℝ) ^ 2) ≤ C) :
    RiemannHypothesis :=
  riemannHypothesis_of_displacement_eighth happrox
    (summable_eighth_of_frequent_diagonal finiteDisplacement_tendsto C
      (h.mono fun N hN => (eighthHead_finiteDisplacement_le_paretoDual N N).trans hN))

end RiemannResearch.RH.QSquarefreeFiniteDisplacement
