/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QZeroPhaseSampling
import RiemannResearch.RH.ZetaTwoParetoTransfer
import Mathlib.Tactic.Linarith

/-!
# A conditional RH consumer for complete weighted sampled errors

Source: user-directed zero-phase research, 21 October 2026.
The finite relative-frequency comparison is combined with the existing
squarefree Q-closure-to-RH theorem. Vanishing sampled error is an explicit
arithmetic hypothesis; neither it nor RH is asserted unconditionally.
-/
noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.QZeroPhaseSampling

open ZetaTwoHilbert ZetaTwoProbability
open RiemannResearch.Analysis.FiniteCellSampling

/-- A general complete-Q approximation consumer. The membership hypotheses
are for the genuine squarefree closure; no constant has been adjoined. -/
theorem riemannHypothesis_of_legal_norm_sq_error_tendsto_zero
    (v : ℕ → QHilbert)
    (hlegal : ∀ j, v j ∈ ZetaTwoOptimizerStage.closure)
    (herror : Tendsto (fun j => ‖qOne - v j‖ ^ 2) atTop (𝓝 0)) :
    RiemannHypothesis := by
  have hlim : Tendsto v atTop (𝓝 qOne) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [(tendsto_order.1 herror).2 (ε ^ 2)
      (sq_pos_of_pos hε)] with j hj
    rw [dist_eq_norm, norm_sub_rev]
    nlinarith [norm_nonneg (qOne - v j)]
  have hclosed : IsClosed (ZetaTwoOptimizerStage.closure : Set QHilbert) := by
    change IsClosed (_root_.closure
      (Submodule.span ℝ (Set.range ZetaTwoOptimizerStage.squarefreeAtom) : Set QHilbert))
    exact isClosed_closure
  exact ZetaTwoParetoTransfer.riemannHypothesis_of_qOne_mem_squarefree_closure
    (hclosed.mem_of_tendsto hlim (Filter.Eventually.of_forall hlegal))

/-- Sampled errors converging to zero imply actual complete-Q error
convergence, provided the samples retain at least half the true energy.
This comparison is supplied below by relative coded-cell frequencies. -/
theorem norm_sq_error_tendsto_zero_of_sampled_error
    (v : ℕ → QHilbert) (sampledError : ℕ → ℝ)
    (hcompare : ∀ j, (1 / 2 : ℝ) * ‖qOne - v j‖ ^ 2 ≤ sampledError j)
    (hsampled : Tendsto sampledError atTop (𝓝 0)) :
    Tendsto (fun j => ‖qOne - v j‖ ^ 2) atTop (𝓝 0) := by
  have hupper : ∀ j, ‖qOne - v j‖ ^ 2 ≤ 2 * sampledError j := by
    intro j
    have h := hcompare j
    linarith
  apply squeeze_zero (fun j => sq_nonneg ‖qOne - v j‖) hupper
  simpa only [mul_zero] using hsampled.const_mul 2

/-- Conditional RH consequence of genuine legal approximants with vanishing
weighted sampled errors and relative coded-cell discrepancy at most 1/2.
Both arithmetic inputs remain explicit; no zero-equidistribution or
vanishing sampled-minimum theorem is supplied by this consumer.

The representative R_j is the physical error on positive coordinates.
Its value at zero may be nonzero; this is essential for qOne-v_j. -/
theorem riemannHypothesis_of_weighted_sampled_error
    {κ : Type*}
    (L : ℕ → ℕ) (hL : ∀ j, 0 < L j)
    (s : ℕ → Finset κ) (A : (j : ℕ) → κ → Fin (L j))
    (v : ℕ → QHilbert)
    (hlegal : ∀ j, v j ∈ ZetaTwoOptimizerStage.closure)
    (R : ℕ → ℕ → ℝ) (C : ℕ → ℝ)
    (hR : ∀ j k, |R j k| ≤ C j)
    (hperiod : ∀ j k, R j (k + L j) = R j k)
    (hsequence : ∀ j k, qSequence (qOne - v j) (k + 1) = R j (k + 1))
    (δ : ℕ → ℝ) (hδ : ∀ j, δ j ≤ (1 / 2 : ℝ))
    (hfrequency : ∀ j (a : Fin (L j)),
      |(L j : ℝ) * cellFrequency (s j) (A j) a - 1| ≤ δ j)
    (hsampled : Tendsto (fun j =>
      sampleMean (s j) (A j) (fun a =>
        ((L j : ℝ) * residuePowerWeight 0 (L j) (a.val + 1)) *
          R j (a.val + 1) ^ 2)) atTop (𝓝 0)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_legal_norm_sq_error_tendsto_zero v hlegal
  apply norm_sq_error_tendsto_zero_of_sampled_error v _ _ hsampled
  intro j
  have hlow := (weighted_norm_sample_comparison (L j) (hL j)
    (s j) (A j) (qOne - v j) (R j) (hR j) (hperiod j)
    (hsequence j) (δ j) (hfrequency j)).1
  have hhalf : (1 / 2 : ℝ) * ‖qOne - v j‖ ^ 2 ≤
      (1 - δ j) * ‖qOne - v j‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith [hδ j]) (sq_nonneg _)
  exact hhalf.trans hlow

end RiemannResearch.RH.QZeroPhaseSampling
