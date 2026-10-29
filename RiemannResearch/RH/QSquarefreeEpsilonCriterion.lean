/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QExactHeadEpsilonBounds
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.RH.QCRTPeriodHeadBalance
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Epsilon witnesses for legal squarefree CRT approximation

Source: the user's forall-epsilon/exists-witness request, 28 October 2026.
The metric closure characterization is standard. The existing
QSquarefreeResidualLimit.epsilon_approximation_iff_mem concerns eventual
optimizer errors; here the quantifiers concern an independently chosen finite
legal vector at each tolerance.

The epsilon provider for actual primorial minima remains an open arithmetic
hypothesis. The formal implication does not prove that provider or RH.
Uniform control of a preassigned canonical family is not assumed, while
selected approximating witnesses are automatically bounded.
-/

noncomputable section
namespace RiemannResearch.RH.QSquarefreeEpsilonCriterion
open ZetaTwoHilbert ZetaTwoProbability
open scoped Topology
/-- Direct complete-norm approximation is precisely membership in the legal closure. -/
theorem epsilon_approximation_iff_closure :
    (∀ ε : ℝ, 0 < ε → ∃ f : QHilbert, f ∈ qSquarefreeCRTSpan ∧ ‖qOne - f‖ < ε) ↔
      qOne ∈ qSquarefreeCRTSpan.topologicalClosure := by
  change _ ↔ qOne ∈ closure (qSquarefreeCRTSpan : Set QHilbert)
  rw [Metric.mem_closure_iff]
  simp only [dist_eq_norm, norm_sub_rev]
  rfl
/-- Conditional research reduction: the universal witness hypothesis is not established. -/
theorem riemannHypothesis_of_epsilon_approximation
    (h : ∀ ε : ℝ, 0 < ε → ∃ f : QHilbert, f ∈ qSquarefreeCRTSpan ∧ ‖qOne - f‖ < ε) :
    RiemannHypothesis := by
  exact QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
    (QSquarefreeCapacity.capacity_tendsto_iff_squarefree_closure.mpr
      (epsilon_approximation_iff_closure.mp h))
/-- Norm control follows for each selected complete-error witness. -/
theorem selected_witness_norm_lt (f : QHilbert) (ε : ℝ)
    (h : ‖qOne - f‖ < ε) : ‖f‖ < 1 + ε := by
  have ht := norm_sub_le qOne (qOne - f)
  rw [sub_sub_cancel, qOne_norm] at ht
  linarith

/-- A family-wide bound is replaced by a complete error witness at each tolerance. -/
theorem epsilon_approximation_of_energy_witnesses
    (h : ∀ ε : ℝ, 0 < ε → ∃ H : ℕ, ∃ f : QHilbert,
      f ∈ qSquarefreeCRTSpan ∧
      (∀ n, 0 < n → n ≤ H → qSequence f n = 1) ∧
      ‖f‖ ^ 2 ≤ 1 + ε ^ 2 / 8 ∧ QExactHeadEpsilonBounds.targetTail H ≤ ε ^ 2 / 8) :
    ∀ ε : ℝ, 0 < ε → ∃ f : QHilbert, f ∈ qSquarefreeCRTSpan ∧ ‖qOne - f‖ < ε := by
  intro ε hε
  obtain ⟨H, f, hf, hh, he, ht⟩ := h ε hε
  exact ⟨f, hf, QExactHeadEpsilonBounds.norm_error_lt_of_epsilon_budget H f hh ε hε he ht⟩

/-- Rational head cutoff discharges the complete target-tail budget. -/
theorem targetTail_le_of_cutoff (H : ℕ) (hH : 0 < H) (ε : ℝ)
    (hcut : (608 / 125 : ℝ) ≤ (H : ℝ) * ε ^ 2) :
    QExactHeadEpsilonBounds.targetTail H ≤ ε ^ 2 / 8 := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  apply le_trans (QExactHeadEpsilonBounds.targetTail_le_rational H hH)
  apply (div_le_iff₀ hHR).mpr
  nlinarith

/-- The open arithmetic provider is stated for the actual primorial minima.
Its head and period may both depend on the requested tolerance. -/
theorem epsilon_approximation_of_minimum_energy_witnesses
    (h : ∀ ε : ℝ, 0 < ε → ∃ j H : ℕ,
      0 < H ∧ H ≤ j + 1 ∧ (608 / 125 : ℝ) ≤ (H : ℝ) * ε ^ 2 ∧
      ‖QCRTPeriodHeadBalance.minimumAt j H‖ ^ 2 ≤ 1 + ε ^ 2 / 8) :
    ∀ ε : ℝ, 0 < ε → ∃ f : QHilbert, f ∈ qSquarefreeCRTSpan ∧ ‖qOne - f‖ < ε := by
  apply epsilon_approximation_of_energy_witnesses
  intro ε hε
  obtain ⟨j, H, hH, hHj, hcut, he⟩ := h ε hε
  exact ⟨H, QCRTPeriodHeadBalance.minimumAt j H,
    QCRTPeriodHeadBalance.minimumAt_legal j H,
    QCRTPeriodHeadBalance.minimumAt_head j H hHj, he, targetTail_le_of_cutoff H hH ε hcut⟩


/-- A successful tolerance certificate survives every later primorial period. -/
theorem minimum_energy_witness_at_later_period (i j H : ℕ) (hij : i ≤ j)
    (hH : H ≤ i + 1) (ε : ℝ)
    (he : ‖QCRTPeriodHeadBalance.minimumAt i H‖ ^ 2 ≤ 1 + ε ^ 2 / 8) :
    ‖QCRTPeriodHeadBalance.minimumAt j H‖ ^ 2 ≤ 1 + ε ^ 2 / 8 := by
  have hg := QCRTPeriodHeadBalance.minimumAt_period_gain i j H hij hH
  nlinarith [sq_nonneg ‖QCRTPeriodHeadBalance.minimumAt i H -
    QCRTPeriodHeadBalance.minimumAt j H‖]

/-- Adding an arbitrary period cutoff does not strengthen the epsilon provider. -/
theorem minimum_energy_witnesses_cofinal_iff :
    (∀ ε : ℝ, 0 < ε → ∃ j H : ℕ,
      0 < H ∧ H ≤ j + 1 ∧ (608 / 125 : ℝ) ≤ (H : ℝ) * ε ^ 2 ∧
      ‖QCRTPeriodHeadBalance.minimumAt j H‖ ^ 2 ≤ 1 + ε ^ 2 / 8) ↔
    (∀ ε : ℝ, 0 < ε → ∀ J : ℕ, ∃ j H : ℕ,
      J ≤ j ∧ 0 < H ∧ H ≤ j + 1 ∧ (608 / 125 : ℝ) ≤ (H : ℝ) * ε ^ 2 ∧
      ‖QCRTPeriodHeadBalance.minimumAt j H‖ ^ 2 ≤ 1 + ε ^ 2 / 8) := by
  constructor
  · intro h ε hε J
    obtain ⟨i, H, hH, hHi, hcut, he⟩ := h ε hε
    refine ⟨max i J, H, le_max_right _ _, hH, ?_, hcut, ?_⟩
    · exact hHi.trans (Nat.add_le_add_right (le_max_left _ _) 1)
    · exact minimum_energy_witness_at_later_period i (max i J) H
        (le_max_left _ _) hHi ε he
  · intro h ε hε
    obtain ⟨j, H, _, hH, hHj, hcut, he⟩ := h ε hε 0
    exact ⟨j, H, hH, hHj, hcut, he⟩

/-- Selected epsilon witnesses automatically have a common norm bound.
This is a consequence of approximation, not an assumed bound on the canonical family. -/
theorem bounded_selection_of_epsilon_approximation
    (h : ∀ ε : ℝ, 0 < ε → ∃ f : QHilbert, f ∈ qSquarefreeCRTSpan ∧ ‖qOne - f‖ < ε) :
    ∃ F : ℕ → QHilbert, (∀ n, F n ∈ qSquarefreeCRTSpan) ∧
      (∀ n, ‖qOne - F n‖ < 1 / (n + 1 : ℝ)) ∧ (∀ n, ‖F n‖ < 2) := by
  classical
  have hw : ∀ n : ℕ, ∃ f : QHilbert,
      f ∈ qSquarefreeCRTSpan ∧ ‖qOne - f‖ < 1 / (n + 1 : ℝ) :=
    fun n => h _ (by positivity)
  choose F hlegal herr using hw
  refine ⟨F, hlegal, herr, ?_⟩
  intro n
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hden : (0 : ℝ) < n + 1 := by positivity
  have hfrac : 1 / (n + 1 : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hden).mpr
    linarith
  have hnorm := selected_witness_norm_lt (F n) _ (herr n)
  linarith

end RiemannResearch.RH.QSquarefreeEpsilonCriterion
