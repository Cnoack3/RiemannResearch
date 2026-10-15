/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCanonicalMovingCovariance
import RiemannResearch.RH.CanonicalMobiusSignedAverages
import RiemannResearch.RH.CanonicalPrimeSubpolynomialWindow
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Complete signed Q energy and the squarefree closure uniformity gap

Source: the user's request to retain the complete covariance energy,
15 October 2026. The exact Q norm equals both the full residual Gram
quadratic form and the infinite physical weighted sum. All cross terms remain.

The two closure/RH consumers are conditional research reductions.
Open: a single uniform upper bound for the actual cofinal signed Gram
energies. Column decay and PNT sublinear energy do not discharge this input.
Squarefree boundary conductors, coefficient sum one, and cofinal support
supply legal candidates matching growing heads exactly.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.RH.QCanonicalMovingCovariance
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer Pareto

def residualAverage (s : Finset ℕ) (a : ℕ → ℝ) : QHilbert :=
  ∑ k ∈ s, a k • residual k

theorem residualAverage_energy (s : Finset ℕ) (a : ℕ → ℝ) :
    ‖residualAverage s a‖ ^ 2 =
      ∑ k ∈ s, ∑ l ∈ s, a k * a l * inner ℝ (residual k) (residual l) := by
  rw [residualAverage, ← real_inner_self_eq_norm_sq]
  simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  simp only [mul_assoc]

theorem residual_covariance_weighted (K N : ℕ) :
    inner ℝ (residual K) (residual N) =
      ∑' n : ℕ, positiveQWeight n * (qOneSequence n - canonicalMobiusHead K n) *
        (qOneSequence n - canonicalMobiusHead N n) := by
  rw [qInner_weighted, residual_sequence, residual_sequence]

theorem residualAverage_weighted (s : Finset ℕ) (a : ℕ → ℝ) :
    ‖residualAverage s a‖ ^ 2 = ∑' n : ℕ, positiveQWeight n *
      (∑ k ∈ s, a k * (qOneSequence n - canonicalMobiusHead k n)) ^ 2 := by
  rw [qNorm_weighted_sq]
  apply tsum_congr
  intro n
  congr 2
  change qSequenceLinear (∑ k ∈ s, a k • residual k) n = _
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ k ∈ s, a k * qSequence (residual k) n) = _
  simp_rw [residual_sequence]



open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer Pareto
open Pareto.CoefficientStabilization

theorem toPareto_residualAverage (s : Finset ℕ) (a : ℕ → ℝ)
    (hsum : ∑ k ∈ s, a k = 1) :
    toPareto (residualAverage s a) = hilbertOne - signedMobiusAverage s a := by
  change toParetoLinear (∑ k ∈ s, a k • residual k) = _
  simp only [map_sum, map_smul]
  change (∑ k ∈ s, a k • toPareto (residual k)) = _
  simp only [toPareto_residual, Pareto.MovingCovariance.residual]
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, one_smul]
  rfl

/-- Conditional research reduction: the complete signed Q-Gram budget is
the unresolved substantive arithmetic input. Squarefree support and exact
growing heads are discharged by the existing canonical construction. -/
theorem squarefree_closure_of_bounded_residual_gram
    (s : ℕ → Finset ℕ) (a : ℕ → ℕ → ℝ)
    (hsum : ∀ M, ∑ k ∈ s M, a M k = 1)
    (hindex : ∀ M k, k ∈ s M → M ≤ k)
    (hsquarefree : ∀ M k, k ∈ s M → Squarefree (k + 1))
    (C : ℝ)
    (hbudget : ∀ M,
      (∑ k ∈ s M, ∑ l ∈ s M,
        a M k * a M l * inner ℝ (residual k) (residual l)) ≤ C) :
    qOne ∈ qSquarefreeCRTSpan.topologicalClosure := by
  apply qSquarefreeClosure_iff_paretoSquarefreeClosure.mpr
  have hmem (M : ℕ) : signedMobiusAverage (s M) (a M) ∈ squarefreeCRTSpan := by
    unfold signedMobiusAverage
    apply squarefreeCRTSpan.sum_mem
    intro k hk
    exact squarefreeCRTSpan.smul_mem _
      (canonicalMobiusHilbert_mem_squarefreeCRTSpan k (hsquarefree M k hk))
  apply hilbertOne_mem_closure_of_bounded_exact_heads squarefreeCRTSpan
    (fun M => signedMobiusAverage (s M) (a M)) hmem (C := zetaTwo * C + 2)
  · intro M
    exact signedMobiusAverage_exact _ _ M (hsum M) (hindex M)
  · intro M
    have hp : ‖hilbertOne - signedMobiusAverage (s M) (a M)‖ ^ 2 ≤ zetaTwo * C := by
      have h := toPareto_norm_sq_le (residualAverage (s M) (a M))
      rw [toPareto_residualAverage _ _ (hsum M), residualAverage_energy] at h
      exact h.trans (mul_le_mul_of_nonneg_left (hbudget M) zetaTwo_pos.le)
    have herr : ‖hilbertOne - signedMobiusAverage (s M) (a M)‖ ≤ zetaTwo * C + 1 := by
      nlinarith [sq_nonneg (‖hilbertOne - signedMobiusAverage (s M) (a M)‖ - 1)]
    have hone : ‖hilbertOne‖ ≤ 1 := by
      nlinarith [hilbertOne_norm_sq, norm_nonneg hilbertOne]
    calc
      _ = ‖hilbertOne - (hilbertOne - signedMobiusAverage (s M) (a M))‖ := by
        congr 1; abel
      _ ≤ ‖hilbertOne‖ + ‖hilbertOne - signedMobiusAverage (s M) (a M)‖ :=
        norm_sub_le _ _
      _ ≤ 1 + (zetaTwo * C + 1) := add_le_add hone herr
      _ = _ := by ring

/-- Conditional research reduction: bounded full Q energy of cofinal
squarefree canonical averages implies RH. The covariance budget stays open. -/
theorem riemannHypothesis_of_bounded_residual_gram
    (s : ℕ → Finset ℕ) (a : ℕ → ℕ → ℝ)
    (hsum : ∀ M, ∑ k ∈ s M, a M k = 1)
    (hindex : ∀ M k, k ∈ s M → M ≤ k)
    (hsquarefree : ∀ M k, k ∈ s M → Squarefree (k + 1))
    (C : ℝ)
    (hbudget : ∀ M,
      (∑ k ∈ s M, ∑ l ∈ s M,
        a M k * a M l * inner ℝ (residual k) (residual l)) ≤ C) :
    RiemannHypothesis := by
  obtain ⟨D, hD⟩ := qSquarefreeClosure_iff_exact_head_tail_bound.mp
    (squarefree_closure_of_bounded_residual_gram s a hsum hindex hsquarefree C hbudget)
  choose L F hL hF hhead htail using hD
  apply riemannHypothesis_of_squarefree_span_bounded_tail
    id L F tendsto_id hL hF hhead
  refine ⟨D, ?_⟩
  rintro _ ⟨j, rfl⟩
  exact htail j
end RiemannResearch.RH.QCanonicalMovingCovariance
