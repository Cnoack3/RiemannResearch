/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.OrthogonalKernelScreening
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.LinearAlgebra.FiniteHilbertSchur
import RiemannResearch.RH.QSquarefreeBoundary
import RiemannResearch.RH.QSquarefreeCorrectionKernel
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.SquarefreeMobiusProjection
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Arithmetic screening of actual squarefree correction kernels

Source: the user's RH_Shrinking_Head_and_Coupled_Response_Research_Handoff,
25 October 2026, and the ensuing orthogonality refinement.
The omitted nonsquarefree Möbius coordinates vanish on both the legal stage
and the actual residual. Their Riesz vectors can therefore be removed from
the correction kernel without changing its signed residual pairing.

The four-site formula subtracts an explicit square divided by 30*zeta(2).
The finite-family theorem supplies actual normal solutions even for redundant
families. The remaining uniform screened-energy bound is OPEN.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeKernelScreening
open ZetaTwoHilbert ZetaTwoOptimizerStage ZetaTwoProbability
open QShiftedReciprocal QSquarefreeCorrectionKernel QSquarefreeBoundary
open QSquarefreeSmoothedProjection
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.OrthogonalKernelScreening
open RiemannResearch.LinearAlgebra

def fourSiteVector : QHilbert := evaluation 4 - evaluation 3 - evaluation 2 + evaluation 1
theorem inner_fourSiteVector (f : QHilbert) : inner ℝ f fourSiteVector = fourSiteFunctional f := by
  simp only [fourSiteVector, inner_add_right, inner_sub_right, inner_evaluation,
    fourSiteFunctional_apply]
theorem fourSiteFunctional_stage {N : ℕ} {f : QHilbert} (hf : f ∈ stage N) :
    fourSiteFunctional f = 0 := by
  apply fourSiteFunctional_zero_on_closure
  exact (Submodule.span ℝ (Set.range squarefreeAtom)).le_topologicalClosure
    (walkSpan_le squarefreeAtom id N hf)
theorem residual_inner_fourSiteVector (N : ℕ) : inner ℝ (residual N) fourSiteVector = 0 := by
  rw [inner_fourSiteVector, ZetaTwoOptimizerStage.residual, map_sub,
    fourSiteFunctional_qOne, optimizer,
    fourSiteFunctional_stage ((stage N).starProjection_apply_mem qOne), sub_self]
theorem residualized_inner_fourSiteVector (N n : ℕ) :
    inner ℝ (residualizedKernel N n) fourSiteVector =
      fourSiteFunctional (B (kernel N n)) := by
  rw [inner_fourSiteVector, residualizedKernel, map_sub,
    fourSiteFunctional_stage ((stage N).starProjection_apply_mem _), sub_zero]

private theorem evaluation_inner_succ (m n : ℕ) :
    inner ℝ (evaluation (m + 1)) (evaluation (n + 1)) =
      if m = n then zetaTwo * ((m : ℝ) + 1) ^ 2 else 0 := by
  rw [inner_evaluation, qSequence_succ]
  by_cases h : m = n
  · subst n
    simp only [evaluation, lp.single_apply, Pi.single_eq_same]
    rw [div_div, ← pow_two, Real.sq_sqrt (qWeight_pos m).le]
    simp [qWeight, positiveQWeight]
  · simp [evaluation, lp.single_apply, h, Ne.symm h]
private theorem evaluation_norm_sq_succ (m : ℕ) : ‖evaluation (m+1)‖ ^ 2 =
    zetaTwo * ((m : ℝ)+1)^2 := by
  rw [← real_inner_self_eq_norm_sq, evaluation_inner_succ, if_pos rfl]
theorem fourSiteVector_norm_sq : ‖fourSiteVector‖ ^ 2 = 30 * zetaTwo := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [fourSiteVector, inner_add_left, inner_sub_left, inner_add_right, inner_sub_right]
  norm_num [show (4 : ℕ) = 3+1 by rfl, show (3 : ℕ) = 2+1 by rfl,
    show (2 : ℕ) = 1+1 by rfl, show (1 : ℕ) = 0+1 by rfl, evaluation_inner_succ, evaluation_norm_sq_succ]
  ring
theorem movingCorrection_sq_le_fourSite (N n : ℕ) :
    (qSequence (movingCorrection N) n) ^ 2 ≤
    error N * (kernelEnergy N n -
      fourSiteFunctional (B (kernel N n)) ^ 2 / (30 * zetaTwo)) := by
  rw [movingCorrection_eq_pairing]
  have hv : ‖fourSiteVector‖ ^ 2 ≠ 0 := by
    rw [fourSiteVector_norm_sq]
    exact ne_of_gt (mul_pos (by norm_num) zetaTwo_pos)
  have h := pairing_sq_le_rankOne (residual N) (residualizedKernel N n) fourSiteVector
    (residual_inner_fourSiteVector N) hv
  simpa only [fourSiteVector_norm_sq, residualized_inner_fourSiteVector, error, kernelEnergy] using h


/-- Removing the four-site direction keeps the actual signed pairing. -/
def fourSiteScreenedKernel (N n : ℕ) : QHilbert :=
  residualizedKernel N n -
    (fourSiteFunctional (B (kernel N n)) / (30 * zetaTwo)) • fourSiteVector

def fourSiteEnergy (N n : ℕ) : ℝ :=
  kernelEnergy N n - fourSiteFunctional (B (kernel N n)) ^ 2 / (30 * zetaTwo)

theorem fourSiteScreenedKernel_norm_sq (N n : ℕ) :
    ‖fourSiteScreenedKernel N n‖ ^ 2 = fourSiteEnergy N n := by
  have hv : ‖fourSiteVector‖ ^ 2 ≠ 0 := by
    rw [fourSiteVector_norm_sq]
    exact ne_of_gt (mul_pos (by norm_num) zetaTwo_pos)
  simpa only [fourSiteVector_norm_sq, residualized_inner_fourSiteVector,
    fourSiteScreenedKernel, fourSiteEnergy, kernelEnergy] using
    rankOne_norm_sq (residualizedKernel N n) fourSiteVector hv

theorem fourSiteEnergy_nonneg (N n : ℕ) : 0 ≤ fourSiteEnergy N n := by
  rw [← fourSiteScreenedKernel_norm_sq]
  exact sq_nonneg _

theorem fourSiteEnergy_le (N n : ℕ) : fourSiteEnergy N n ≤ kernelEnergy N n := by
  apply sub_le_self
  exact div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) zetaTwo_pos.le)

theorem fourSiteScreenedKernel_pairing (N n : ℕ) :
    inner ℝ (residual N) (fourSiteScreenedKernel N n) =
      qSequence (movingCorrection N) n := by
  rw [fourSiteScreenedKernel, inner_sub_right, real_inner_smul_right,
    residual_inner_fourSiteVector, mul_zero, sub_zero, movingCorrection_eq_pairing]

theorem fourSiteScore_physical (N n : ℕ) :
    fourSiteFunctional (B (kernel N n)) =
      qSequence (kernel N n) 4 / 5 - qSequence (kernel N n) 3 / 4 -
        qSequence (kernel N n) 2 / 3 + qSequence (kernel N n) 1 / 2 := by
  rw [fourSiteFunctional_apply]
  simp only [qSequence_B]
  norm_num

/-- Conditional research reduction; its common screened-energy bound is Open. -/
theorem riemannHypothesis_of_fourSiteEnergy_bound (C : ℝ) (hC : 0 ≤ C)
    (hK : ∀ N n : ℕ, 0 < n → n ≤ N → error N * fourSiteEnergy N n ≤ C ^ 2) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_moving_head_bound C hC
  intro N n hn hnN
  have h := (movingCorrection_sq_le_fourSite N n).trans (hK N n hn hnN)
  nlinarith [sq_abs (qSequence (movingCorrection N) n),
    abs_nonneg (qSequence (movingCorrection N) n)]

open RiemannResearch.RH.SquarefreeMobiusProjection
def omittedVector (i : ℕ) : QHilbert :=
  (InnerProductSpace.toDual ℝ QHilbert).symm (qCoefficientCLM (i+2))
theorem omittedVector_inner (i : ℕ) (f : QHilbert) :
    inner ℝ (omittedVector i) f = qCoefficientCLM (i+2) f := by
  exact congrArg (fun L : QHilbert →L[ℝ] ℝ => L f)
    ((InnerProductSpace.toDual ℝ QHilbert).apply_symm_apply (qCoefficientCLM (i+2)))
theorem omitted_stage {N i : ℕ} (hi : ¬ Squarefree (i+2))
    {f : QHilbert} (hf : f ∈ stage N) : qCoefficientCLM (i+2) f = 0 := by
  apply q_omitted_coordinate_zero i hi
  exact (Submodule.span ℝ (Set.range squarefreeAtom)).le_topologicalClosure
    (walkSpan_le squarefreeAtom id N hf)
theorem residual_inner_omitted (N i : ℕ) (hi : ¬ Squarefree (i+2)) :
    inner ℝ (residual N) (omittedVector i) = 0 := by
  rw [real_inner_comm, omittedVector_inner,
    ZetaTwoOptimizerStage.residual, map_sub,
    q_target_coordinate (i+2) (by omega),
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree hi, optimizer,
    omitted_stage hi ((stage N).starProjection_apply_mem qOne)]
  norm_num
theorem residualized_inner_omitted (N n i : ℕ) (hi : ¬ Squarefree (i+2)) :
    inner ℝ (omittedVector i) (residualizedKernel N n) =
      qCoefficientCLM (i+2) (B (kernel N n)) := by
  rw [omittedVector_inner, residualizedKernel, map_sub,
    omitted_stage hi ((stage N).starProjection_apply_mem _), sub_zero]

theorem exists_omitted_screening (N n M : ℕ) (d : Fin M → ℕ)
    (hd : ∀ i, ¬ Squarefree (d i + 2)) :
    ∃ c : Fin M → ℝ,
      (∀ i, inner ℝ (omittedVector (d i))
        (finiteSchurCombination (fun j => omittedVector (d j)) c) =
        qCoefficientCLM (d i + 2) (B (kernel N n))) ∧
      ‖finiteSchurResidual (residualizedKernel N n)
        (fun i => omittedVector (d i)) c‖ ^ 2 =
        kernelEnergy N n -
          ∑ i, c i * qCoefficientCLM (d i + 2) (B (kernel N n)) ∧
      (qSequence (movingCorrection N) n) ^ 2 ≤
        error N * (kernelEnergy N n -
          ∑ i, c i * qCoefficientCLM (d i + 2) (B (kernel N n))) := by
  obtain ⟨c, hc⟩ := finiteSchur_exists_normal (residualizedKernel N n)
    (fun i => omittedVector (d i))
  refine ⟨c, ?_, ?_, ?_⟩
  · intro i
    rw [hc i, residualized_inner_omitted N n (d i) (hd i)]
  · rw [finiteSchurResidual_norm_sq _ _ c hc]
    simp only [kernelEnergy, residualized_inner_omitted N n _ (hd _)]
  · rw [movingCorrection_eq_pairing]
    have h := pairing_sq_le_finite (residual N) (residualizedKernel N n)
      (fun i => omittedVector (d i)) c
      (fun i => residual_inner_omitted N (d i) (hd i)) hc
    simpa only [error, kernelEnergy, residualized_inner_omitted N n _ (hd _)] using h

end RiemannResearch.RH.QSquarefreeKernelScreening
