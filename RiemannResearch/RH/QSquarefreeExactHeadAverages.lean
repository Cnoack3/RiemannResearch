/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QExactHeadAverages
import RiemannResearch.RH.QDivisorHilbertBasis
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ZetaTwoCRTReciprocalEnergy
import RiemannResearch.RH.CRTSquarefreeBoundedTail
import Mathlib.Tactic.Ring

/-!
# Squarefree exact-head block averages and complete Parseval convergence

Source: the user's squarefree CRT/Parseval bounded-tail request, 16 October 2026.
This assembles the existing actual Q block-average theorem with the algebraic
squarefree span, common squarefree periods, and the complete divisor basis.

Conditional research reduction: the uniform full-Q bound, or its literal
finite-period tail provider, is an explicit arithmetic hypothesis. Neither
provider is proved here. Parseval always sums over all positive indices.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.QSquarefreeExactHeadAverages

open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QExactHeadAverages
open QDivisorHilbert

/-- Algebraic squarefree membership is exactly membership in a finite divisor
span with some squarefree common period. No closure is used in this assertion. -/
theorem squarefree_span_iff_common_period (f : QHilbert) :
    f ∈ qSquarefreeCRTSpan ↔
      ∃ L : ℕ, Squarefree L ∧ qSequence f ∈ Pareto.divisorResidueSpan L := by
  constructor
  · intro hf
    have hp : toParetoLinear f ∈ Pareto.squarefreeCRTSpan := by
      rw [← qSquarefreeCRTSpan_map]
      exact ⟨f, hf, rfl⟩
    obtain ⟨L, hL, hp⟩ := hp
    refine ⟨L, hL, ?_⟩
    change Pareto.hilbertSequence (toPareto f) ∈ Pareto.divisorResidueSpan L at hp
    simpa only [toPareto_sequence] using hp
  · rintro ⟨L, hL, hf⟩
    have hp : toParetoLinear f ∈ Pareto.squarefreeCRTSpan := by
      refine ⟨L, hL, ?_⟩
      change Pareto.hilbertSequence (toPareto f) ∈ Pareto.divisorResidueSpan L
      simpa only [toPareto_sequence] using hf
    rw [← qSquarefreeCRTSpan_map] at hp
    obtain ⟨g, hg, he⟩ := hp
    have hseq := congrArg Pareto.hilbertSequence he
    change Pareto.hilbertSequence (toPareto g) =
      Pareto.hilbertSequence (toPareto f) at hseq
    simp only [toPareto_sequence] at hseq
    have hgf : g = f := qSequence_injective hseq
    exact hgf ▸ hg

/-- Conditional squarefree specialization with actual common periods, exact
growing heads, strong convergence, and vanishing complete Parseval energy. -/
theorem exists_squarefree_exact_head_block_averages
    (F : ℕ → QHilbert)
    (hlegal : ∀ N, F N ∈ qSquarefreeCRTSpan) {B : ℝ}
    (hbound : ∀ N, ‖qOne - F N‖ ^ 2 ≤ B)
    (hhead : ∀ N k, 0 < k → k ≤ N → qSequence (F N) k = 1) :
    ∃ q : ℕ → ℕ, StrictMono q ∧
      (∀ m, blockAverage F q m ∈ qSquarefreeCRTSpan) ∧
      (∀ m, ∃ L : ℕ, Squarefree L ∧
        qSequence (blockAverage F q m) ∈ Pareto.divisorResidueSpan L) ∧
      (∀ m k, 0 < m → 0 < k → k ≤ m →
        qSequence (blockAverage F q m) k = 1) ∧
      Tendsto (blockAverage F q) atTop (𝓝 qOne) ∧
      Tendsto (fun m => ∑' r : ℕ+,
        (inner ℝ (qOne - blockAverage F q m) (divisorWavelet (r : ℕ))) ^ 2 /
          qJordanTwo (r : ℕ)) atTop (𝓝 0) := by
  obtain ⟨q, hq, hm, hh, ht⟩ :=
    exists_legal_exact_head_block_averages qSquarefreeCRTSpan F hlegal hbound hhead
  refine ⟨q, hq, hm, fun m => (squarefree_span_iff_common_period _).mp (hm m),
    hh, ht, ?_⟩
  have he : Tendsto (fun m => ‖qOne - blockAverage F q m‖ ^ 2) atTop (𝓝 0) := by
    have hsub : Tendsto (fun m => qOne - blockAverage F q m)
        atTop (𝓝 (qOne - qOne)) := tendsto_const_nhds.sub ht
    simpa using hsub.norm.pow 2
  simpa only [divisorWavelet_parseval_norm] using he

/-- The literal squarefree finite-period tail supplies both algebraic legality
and the full Q error bound. Boundedness and periodicity are derived from the
divisor span, rather than added as independent assumptions. -/
theorem squarefree_full_error_bound_of_periodic_tail_bound
    (F : ℕ → QHilbert) (L : ℕ → ℕ)
    (hL : ∀ N, Squarefree (L N))
    (hspan : ∀ N, qSequence (F N) ∈ Pareto.divisorResidueSpan (L N))
    (hhead : ∀ N k, 0 < k → k ≤ N → qSequence (F N) k = 1)
    {B : ℝ}
    (htail : ∀ N, (∑ a ∈ Finset.Icc (N + 1) (L N),
      |1 - qSequence (F N) a| ^ 2 / (a : ℝ) ^ 2) ≤ B) :
    (∀ N, F N ∈ qSquarefreeCRTSpan) ∧
      (∀ N, ‖qOne - F N‖ ^ 2 ≤ B) := by
  constructor
  · intro N
    exact (squarefree_span_iff_common_period _).mpr ⟨L N, hL N, hspan N⟩
  · intro N
    obtain ⟨_, _, _, ⟨C, hC⟩, hp⟩ := Pareto.divisorResidueSpan_lift (hspan N)
    have hb := (periodic_qError_comparison (L N)
      (Nat.pos_of_ne_zero (hL N).ne_zero) (F N) hC hp).2
    rw [Pareto.crtReciprocalEnergy_eq_Icc_tail N (L N) _
      (by intro n hn hnN; rw [hhead N n hn hnN]; ring)] at hb
    exact hb.trans (htail N)

/-- Conditional closure, divergence of the actual squarefree capacity, and
Mathlib RH, all from the same still-open bounded exact-head family. -/
theorem squarefree_closure_capacity_and_rh_of_bounded_exact_heads
    (F : ℕ → QHilbert)
    (hlegal : ∀ N, F N ∈ qSquarefreeCRTSpan) {B : ℝ}
    (hbound : ∀ N, ‖qOne - F N‖ ^ 2 ≤ B)
    (hhead : ∀ N k, 0 < k → k ≤ N → qSequence (F N) k = 1) :
    qOne ∈ qSquarefreeCRTSpan.topologicalClosure ∧
      Tendsto QSquarefreeCapacity.capacity atTop atTop ∧ RiemannHypothesis := by
  obtain ⟨q, _, hm, _, _, ht, _⟩ :=
    exists_squarefree_exact_head_block_averages F hlegal hbound hhead
  have hc : qOne ∈ qSquarefreeCRTSpan.topologicalClosure :=
    qSquarefreeCRTSpan.isClosed_topologicalClosure.mem_of_tendsto ht
      (Filter.Eventually.of_forall fun m =>
        qSquarefreeCRTSpan.le_topologicalClosure (hm m))
  have hk := QSquarefreeCapacity.capacity_tendsto_iff_squarefree_closure.mpr hc
  exact ⟨hc, hk, QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto hk⟩

end RiemannResearch.RH.QSquarefreeExactHeadAverages
