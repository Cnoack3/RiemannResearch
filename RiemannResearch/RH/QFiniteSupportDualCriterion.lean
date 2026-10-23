/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.DenseProjectionTesting
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QOptimizerParityRH
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega

/-!
# Finite-support dual testing in the actual complete Q space

Source: continuation of the user-provided UnitSignalBoundednessAudit20261022.md,
22 October 2026. Finite coordinate vectors are tests, not legal approximants.
Their density is unconditional. The testing denominator uses the actual
orthogonal projection onto the closed full legal span.

The finite-test bound is equivalent to target membership. Its RH consumer is
a conditional research reduction: a uniform arithmetic testing constant is Open.
The unit constant suffices whenever the constant target belongs to the closure.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.QFiniteSupportDualCriterion
open ZetaTwoHilbert
open RiemannResearch.Analysis.DenseProjectionTesting

def finiteHead (M : ℕ) (a : QHilbert) : QHilbert :=
  ∑ n ∈ Finset.range M, lp.single 2 n (a n)

theorem finiteHead_tendsto (a : QHilbert) :
    Tendsto (fun M => finiteHead M a) atTop (𝓝 a) := by
  exact (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) a).tendsto_sum_nat

def finiteTests : Set QHilbert := {a | ∃ M b, finiteHead M b = a}

theorem finiteTests_dense : Dense finiteTests := by
  intro a
  apply mem_closure_of_tendsto (finiteHead_tendsto a)
  exact Filter.Eventually.of_forall (fun M => ⟨M, a, rfl⟩)

theorem mem_closure_iff_finite_test_bound (x : QHilbert) :
    x ∈ QFullResidueProjection.closure ↔
      ∃ C : ℝ, ∀ M a,
        |inner ℝ x (finiteHead M a)| ≤
          C * ‖QFullResidueProjection.closure.starProjection (finiteHead M a)‖ := by
  rw [mem_iff_dense_test_bound _ x finiteTests finiteTests_dense]
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, fun M a => hC _ ⟨M, a, rfl⟩⟩
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    rintro a ⟨M, b, rfl⟩
    exact hC M b

theorem riemannHypothesis_of_finite_test_bound
    (h : ∃ C : ℝ, ∀ M a,
      |inner ℝ qOne (finiteHead M a)| ≤
        C * ‖QFullResidueProjection.closure.starProjection (finiteHead M a)‖) :
    RiemannHypothesis := by
  apply QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure
  exact (mem_closure_iff_finite_test_bound qOne).mpr h

theorem not_RH_finite_test_violation (hRH : ¬ RiemannHypothesis) (C : ℝ) :
    ∃ M a, C * ‖QFullResidueProjection.closure.starProjection (finiteHead M a)‖ <
      |inner ℝ qOne (finiteHead M a)| := by
  by_contra h
  push Not at h
  exact hRH (riemannHypothesis_of_finite_test_bound ⟨C, h⟩)


theorem finiteHead_apply_eq_zero (M : ℕ) (a : QHilbert) (n : ℕ) (hn : M ≤ n) :
    finiteHead M a n = 0 := by
  induction M with
  | zero => simp [finiteHead]
  | succ M ih =>
    rw [finiteHead, Finset.sum_range_succ]
    change finiteHead M a n + (lp.single 2 M (a M) : QHilbert) n = 0
    rw [ih (by omega)]
    have hne : n ≠ M := by omega
    simp [lp.single_apply, hne]

theorem qOne_mem_iff_unit_finite_test_bound :
    qOne ∈ QFullResidueProjection.closure ↔
      ∀ M a, |inner ℝ qOne (finiteHead M a)| ≤
        ‖QFullResidueProjection.closure.starProjection (finiteHead M a)‖ := by
  constructor
  · intro h M a
    rw [inner_eq_projected_test _ h (finiteHead M a)]
    simpa only [qOne_norm, one_mul] using
      abs_real_inner_le_norm qOne
        (QFullResidueProjection.closure.starProjection (finiteHead M a))
  · intro h
    apply (mem_closure_iff_finite_test_bound qOne).mpr
    exact ⟨1, by simpa only [one_mul] using h⟩

end RiemannResearch.RH.QFiniteSupportDualCriterion
