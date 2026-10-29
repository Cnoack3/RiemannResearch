/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.RH.QSquarefreeResidualTail
import RiemannResearch.RH.QProjectionMoments
import RiemannResearch.RH.ZetaTwoOptimizerStage
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith

/-!
# The uniform finite-head dual estimate equivalent to residual vanishing

Source: the user-directed finite-head dimension investigation, 29 October 2026.
Finite annihilator classification only tests an exactly zero denominator.
The uniform estimate below is a conditional research reduction: no provider
for its existence is proved. Its constant is independent of the head length
and of the finite-support test. The reverse implication has constant one.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QSquarefreeUniformHeadDual
open ZetaTwoHilbert ZetaTwoOptimizerStage QFiniteSupportDualCriterion
open QSquarefreeResidualTail

def UniformHeadDualBound (C : ℝ) : Prop :=
  ∀ (H : ℕ) (a : QHilbert),
    (inner ℝ qOne (finiteHead H a)) ^ 2 ≤
      C * ‖ZetaTwoOptimizerStage.closure.starProjection (finiteHead H a)‖ ^ 2

/-- Conditional reduction. The uniform bound is the substantive open premise. -/
theorem residual_eq_zero_of_uniformHeadDualBound (C : ℝ) (hC : UniformHeadDualBound C) :
    limitingResidual = 0 := by
  have hf := finiteHead_tendsto limitingResidual
  have hp0 : ZetaTwoOptimizerStage.closure.starProjection limitingResidual = 0 :=
    ZetaTwoOptimizerStage.closure.starProjection_apply_eq_zero_iff.mpr
      limitingResidual_mem_squarefree_orthogonal
  have hp : Tendsto (fun H =>
      ZetaTwoOptimizerStage.closure.starProjection (finiteHead H limitingResidual))
      atTop (𝓝 0) := by
    have ht := (ZetaTwoOptimizerStage.closure.starProjection.continuous.tendsto
      limitingResidual).comp hf
    simpa only [Function.comp_def, hp0] using ht
  have hi : Tendsto (fun H => inner ℝ qOne (finiteHead H limitingResidual))
      atTop (𝓝 (inner ℝ qOne limitingResidual)) :=
    tendsto_const_nhds.inner hf
  have hb : (inner ℝ qOne limitingResidual) ^ 2 ≤ 0 := by
    have ht := le_of_tendsto_of_tendsto (hi.pow 2) ((hp.norm.pow 2).const_mul C)
      (Filter.Eventually.of_forall (fun H => hC H limitingResidual))
    simpa using ht
  have hz : inner ℝ qOne limitingResidual = 0 :=
    sq_eq_zero_iff.mp (le_antisymm hb (sq_nonneg _))
  have hm : inner ℝ qOne limitingResidual = ‖limitingResidual‖ ^ 2 := by
    rw [real_inner_comm]
    exact qResidual_inner_qOne ZetaTwoOptimizerStage.closure
  rw [hm] at hz
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

theorem uniformHeadDualBound_one_of_residual_eq_zero (hr : limitingResidual = 0) :
    UniformHeadDualBound 1 := by
  have hproj : qOne = ZetaTwoOptimizerStage.closure.starProjection qOne :=
    sub_eq_zero.mp hr
  intro H a
  have he : inner ℝ qOne (finiteHead H a) = inner ℝ qOne
      (ZetaTwoOptimizerStage.closure.starProjection (finiteHead H a)) := by
    calc
      _ = inner ℝ (ZetaTwoOptimizerStage.closure.starProjection qOne) (finiteHead H a) :=
        congrArg (fun x => inner ℝ x (finiteHead H a)) hproj
      _ = _ := ZetaTwoOptimizerStage.closure.inner_starProjection_left_eq_right _ _
  rw [he, one_mul]
  have h := abs_real_inner_le_norm qOne
    (ZetaTwoOptimizerStage.closure.starProjection (finiteHead H a))
  rw [qOne_norm, one_mul] at h
  have hh := mul_self_le_mul_self (abs_nonneg _) h
  simpa only [← pow_two, sq_abs] using hh

/-- No uniform constant is asserted to exist. If one exists, constant one works. -/
theorem exists_uniformHeadDualBound_iff :
    (∃ C : ℝ, UniformHeadDualBound C) ↔ limitingResidual = 0 := by
  constructor
  · rintro ⟨C, hC⟩
    exact residual_eq_zero_of_uniformHeadDualBound C hC
  · intro hr
    exact ⟨1, uniformHeadDualBound_one_of_residual_eq_zero hr⟩

end RiemannResearch.RH.QSquarefreeUniformHeadDual
