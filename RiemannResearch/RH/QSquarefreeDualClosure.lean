/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.RH.SquarefreeFiniteObservation
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Squarefree Q closure through infinite annihilators

Source: the user's request to avoid a uniform approximant bound,
17 October 2026. The duality proof is standard Hilbert-space orthogonal
separation. Bagchi, "On Nyman, Beurling and Baez-Duarte's Hilbert space
reformulation of the Riemann hypothesis", Remark 8 and the equivalent-weight
discussion, https://arxiv.org/abs/math/0607733, support the mathematical
relevance of squarefree closure and its external RH equivalence.

This module establishes exact closure/dual equivalences, a normalized
separator and its full error obstruction, and the necessity of infinite
physical support for any separator of one. It does not establish the
infinite annihilator mean-zero assertion. That arithmetic provider remains
Open, and the RH consumer is a conditional research reduction.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeDualClosure
open ZetaTwoHilbert ZetaTwoProbability

theorem annihilator_iff (h : QHilbert) :
    h ∈ qSquarefreeCRTSpanᗮ ↔
      ∀ d : ℕ, 2 ≤ d → Squarefree d → inner ℝ h (qResidue d) = 0 := by
  constructor
  · intro hh d hd hsf
    exact (Submodule.mem_orthogonal' _ h).mp hh (qResidue d)
      (Submodule.subset_span ⟨⟨d, hd, hsf⟩, rfl⟩)
  · intro hh
    have hs : qSquarefreeCRTSpan ≤ (innerSL ℝ h).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨d, rfl⟩
      exact hh d.val d.property.1 d.property.2
    exact (Submodule.mem_orthogonal' _ h).mpr (fun f hf => hs hf)
theorem closure_iff_annihilator_mean_zero :
    qOne ∈ qSquarefreeCRTSpan.topologicalClosure ↔
      ∀ h : QHilbert,
        (∀ d : ℕ, 2 ≤ d → Squarefree d → inner ℝ h (qResidue d) = 0) →
          inner ℝ h qOne = 0 := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure]
  constructor
  · intro hx h hh
    exact (Submodule.mem_orthogonal _ qOne).mp hx h ((annihilator_iff h).mpr hh)
  · intro hh
    exact (Submodule.mem_orthogonal _ qOne).mpr
      (fun h ha => hh h ((annihilator_iff h).mp ha))
theorem normalized_separator_of_not_closure
    (hx : qOne ∉ qSquarefreeCRTSpan.topologicalClosure) :
    ∃ h : QHilbert,
      (∀ d : ℕ, 2 ≤ d → Squarefree d → inner ℝ h (qResidue d) = 0) ∧
        inner ℝ h qOne = 1 := by
  have hn : ¬ ∀ h : QHilbert,
      (∀ d : ℕ, 2 ≤ d → Squarefree d → inner ℝ h (qResidue d) = 0) →
        inner ℝ h qOne = 0 := by
    intro ht
    exact hx (closure_iff_annihilator_mean_zero.mpr ht)
  push Not at hn
  obtain ⟨h, ha, hm⟩ := hn
  refine ⟨(inner ℝ h qOne)⁻¹ • h, ?_, ?_⟩
  · intro d hd hsf
    rw [real_inner_smul_left, ha d hd hsf, mul_zero]
  · rw [real_inner_smul_left, inv_mul_cancel₀ hm]
theorem normalized_separator_error_lower
    (h : QHilbert)
    (ha : ∀ d : ℕ, 2 ≤ d → Squarefree d → inner ℝ h (qResidue d) = 0)
    (hm : inner ℝ h qOne = 1)
    (F : QHilbert) (hF : F ∈ qSquarefreeCRTSpan) :
    1 ≤ ‖h‖ ^ 2 * ‖qOne - F‖ ^ 2 := by
  have hz : inner ℝ h F = 0 :=
    (Submodule.mem_orthogonal' _ h).mp ((annihilator_iff h).mpr ha) F hF
  have he : inner ℝ h (qOne - F) = 1 := by rw [inner_sub_right, hm, hz, sub_zero]
  have hc := real_inner_mul_inner_self_le h (qOne - F)
  rw [he, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hc
  simpa using hc
theorem mean_eq_weighted_sum (h : QHilbert) :
    inner ℝ h qOne = ∑' k, positiveQWeight k * qSequence h k := by
  rw [qInner_weighted, qSequence_qOne]
  congr 1
  funext k
  by_cases hk : k = 0
  · simp [hk, positiveQWeight]
  · simp [qOneSequence, hk]
theorem correlation_eq_weighted_sum (h : QHilbert) (d : ℕ) :
    inner ℝ h (qResidue d) =
      ∑' k, positiveQWeight k * qSequence h k * ArithmeticCumulative.residueFraction d k := by
  rw [qInner_weighted, qSequence_qResidue]

/-- The no-bound criterion stated entirely through literal atomic-Q series. -/
theorem closure_iff_weighted_annihilator :
    qOne ∈ qSquarefreeCRTSpan.topologicalClosure ↔
      ∀ h : QHilbert,
        (∀ d : ℕ, 2 ≤ d → Squarefree d →
          (∑' k, positiveQWeight k * qSequence h k *
            ArithmeticCumulative.residueFraction d k) = 0) →
          (∑' k, positiveQWeight k * qSequence h k) = 0 := by
  simpa only [mean_eq_weighted_sum, correlation_eq_weighted_sum] using
    closure_iff_annihilator_mean_zero

/-- The infinite tail may be dropped only when the annihilator really has
finite physical support. No support claim is made for a general separator. -/
theorem inner_eq_finite_head (h : QHilbert) (N : ℕ)
    (hsupport : ∀ k, N < k → qSequence h k = 0) (f : QHilbert) :
    inner ℝ h f =
      ∑ k ∈ Finset.Icc 1 N, positiveQWeight k * qSequence h k * qSequence f k := by
  rw [qInner_weighted]
  apply tsum_eq_sum
  intro k hk
  have hc : k = 0 ∨ N < k := by
    by_contra hn
    push Not at hn
    exact hk (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  rcases hc with rfl | hc
  · simp
  · rw [hsupport k hc]
    simp

/-- Unconditionally, every finitely supported squarefree annihilator has
mean zero. This does not extend finite observations to arbitrary functionals. -/
theorem finite_support_annihilator_mean_zero (h : QHilbert) (N : ℕ)
    (hsupport : ∀ k, N < k → qSequence h k = 0)
    (ha : ∀ d : ℕ, 2 ≤ d → Squarefree d → inner ℝ h (qResidue d) = 0) :
    inner ℝ h qOne = 0 := by
  have hz := Pareto.squarefree_finite_observation_annihilator N
    (fun k => positiveQWeight k * qSequence h k) (by
      intro d hd hsf
      have he := ha d hd hsf
      rw [inner_eq_finite_head h N hsupport (qResidue d), qSequence_qResidue] at he
      exact he)
  rw [inner_eq_finite_head h N hsupport qOne, qSequence_qOne]
  have he :
      (∑ k ∈ Finset.Icc 1 N, positiveQWeight k * qSequence h k * qOneSequence k) =
        ∑ k ∈ Finset.Icc 1 N, positiveQWeight k * qSequence h k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk0 : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
    simp [qOneSequence, hk0]
  exact he.trans hz

/-- A normalized obstruction, if one exists, must involve arbitrarily distant
physical sites. Finite squarefree jump witnesses cannot separate the constant. -/
theorem normalized_separator_has_tail (h : QHilbert)
    (ha : ∀ d : ℕ, 2 ≤ d → Squarefree d → inner ℝ h (qResidue d) = 0)
    (hm : inner ℝ h qOne = 1) (N : ℕ) :
    ∃ k, N < k ∧ qSequence h k ≠ 0 := by
  by_contra hn
  push Not at hn
  have hz := finite_support_annihilator_mean_zero h N hn ha
  rw [hm] at hz
  norm_num at hz

/-- Conditional research reduction: the infinite annihilator mean-zero
provider is Open. No bound on a family of approximants is a hypothesis. -/
theorem riemannHypothesis_of_annihilator_mean_zero
    (hdual : ∀ h : QHilbert,
      (∀ d : ℕ, 2 ≤ d → Squarefree d → inner ℝ h (qResidue d) = 0) →
        inner ℝ h qOne = 0) : RiemannHypothesis :=
  QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
    (QSquarefreeCapacity.capacity_tendsto_iff_squarefree_closure.mpr
      (closure_iff_annihilator_mean_zero.mpr hdual))

end RiemannResearch.RH.QSquarefreeDualClosure
