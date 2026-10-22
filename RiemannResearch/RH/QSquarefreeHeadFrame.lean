/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.RH.QSquarefreeExactHeadAverages
import RiemannResearch.RH.QSquarefreeHeadRepair
import RiemannResearch.Analysis.FiniteHilbertGram
import RiemannResearch.Analysis.FiniteConstrainedProjection
import RiemannResearch.Analysis.FiniteFeasibleGramRepair
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Choose
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Probability-normalized physical head frames

Source: user-provided continuation agenda, 22 October 2026, Sections 4--5,
and an independently developed normalization of its finite Gram condition.
The exact probability weights remove the artificial factor equal to the
head length. Dependence among physical rows is allowed. The uniform lower
frame estimate for actual legal dictionaries remains an open arithmetic
provider; this module does not establish such an estimate.

For prescribed dictionaries the frame condition controls every represented
row direction, stronger than controlling only the target repair. Allowing
arbitrary dictionaries does not make this an independently weaker criterion
than bounded exact heads: a one-dimensional span of an exact-head candidate
already supplies a corresponding frame estimate.
-/

noncomputable section
open scoped BigOperators Topology

namespace RiemannResearch.RH.QSquarefreeHeadFrame

open Analysis.FiniteHilbertGram Analysis.FiniteConstrainedProjection
open Analysis.FiniteFeasibleGramRepair
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeHeadRepair

/-- The complete Q law gives a head mass at most one, uniformly in its length. -/
theorem positiveQWeight_head_sum_le_one (M : ℕ) :
    (∑ i : Fin M, positiveQWeight (i.val + 1)) ≤ 1 := by
  have hs := Summable.sum_le_tsum (Finset.range (M + 1))
    (fun k _ => positiveQWeight_nonneg k) positiveQWeight_summable
  have hzero : positiveQWeight 0 = 0 := by simp [positiveQWeight]
  rw [positiveQWeight_tsum, Finset.sum_range_succ', hzero, add_zero] at hs
  rw [← Fin.sum_univ_eq_sum_range (fun n : ℕ => positiveQWeight (n + 1)) M] at hs
  exact hs

/-- Feasibility and a probability-weighted frame bound on the actual row
span produce a legal exact-head vector with complete norm at most `1 / c`.
The rows need not be independent. -/
theorem exists_exact_head_of_frame {ι : Type*} [Fintype ι]
    {v : ι → QHilbert} (hv : LinearIndependent ℝ v)
    (hlegal : ∀ i, v i ∈ qSquarefreeCRTSpan) (M : ℕ)
    (c : ℝ) (hc : 0 < c)
    (hfeasible : ∃ a : ι → ℝ, ∀ i : Fin M,
      qSequence (Fintype.linearCombination ℝ v a) (i.val + 1) = 1)
    (hframe : ∀ d : Fin M → ℝ,
      c * ‖Fintype.linearCombination ℝ (projectedRow hv (headObservation M)) d‖ ^ 2 ≤
        ∑ i : Fin M, positiveQWeight (i.val + 1) *
          (qSequence (Fintype.linearCombination ℝ
            (projectedRow hv (headObservation M)) d) (i.val + 1)) ^ 2) :
    ∃ F : QHilbert, F ∈ qSquarefreeCRTSpan ∧
      (∀ i : Fin M, qSequence F (i.val + 1) = 1) ∧ ‖F‖ ^ 2 ≤ 1 / c := by
  obtain ⟨a, ha⟩ := hfeasible
  have hfa : ∀ i : Fin M, inner ℝ (projectedRow hv (headObservation M) i)
      (Fintype.linearCombination ℝ v a) = 1 := by
    intro i
    rw [← projectedRow_pairing hv (headObservation M) a i, headObservation_inner]
    exact ha i
  obtain ⟨d, hn⟩ := exists_normal_of_feasible
    (projectedRow hv (headObservation M)) (fun _ => 1)
    (Fintype.linearCombination ℝ v a) hfa
  let F := Fintype.linearCombination ℝ (projectedRow hv (headObservation M)) d
  have hhead : ∀ i : Fin M, qSequence F (i.val + 1) = 1 := by
    intro i
    have hh := hn i
    rw [← projectedRow_pairing_rowSynthesis hv (headObservation M) d i,
      headObservation_inner] at hh
    exact hh
  refine ⟨F, ?_, hhead, ?_⟩
  · apply legal_synthesis
    intro i
    exact legal_synthesis v hlegal _
  · have hf := hframe d
    change c * ‖F‖ ^ 2 ≤
      ∑ i : Fin M, positiveQWeight (i.val + 1) * (qSequence F (i.val + 1)) ^ 2 at hf
    simp only [hhead, one_pow, mul_one] at hf
    have hb := hf.trans (positiveQWeight_head_sum_le_one M)
    apply (le_div_iff₀ hc).2
    simpa only [mul_comm] using hb

/-- Conditional arithmetic reduction: the frame constant must be positive
and independent of the physical head length, and feasibility remains explicit. -/
theorem closure_capacity_rh_of_uniform_head_frame
    (J : ℕ → ℕ) (v : ∀ M, Fin (J M) → QHilbert)
    (hv : ∀ M, LinearIndependent ℝ (v M))
    (hlegal : ∀ M i, v M i ∈ qSquarefreeCRTSpan)
    (c : ℝ) (hc : 0 < c)
    (hfeasible : ∀ M, ∃ a : Fin (J M) → ℝ, ∀ i : Fin M,
      qSequence (Fintype.linearCombination ℝ (v M) a) (i.val + 1) = 1)
    (hframe : ∀ M (d : Fin M → ℝ),
      c * ‖Fintype.linearCombination ℝ
        (projectedRow (hv M) (headObservation M)) d‖ ^ 2 ≤
        ∑ i : Fin M, positiveQWeight (i.val + 1) *
          (qSequence (Fintype.linearCombination ℝ
            (projectedRow (hv M) (headObservation M)) d) (i.val + 1)) ^ 2) :
    qOne ∈ qSquarefreeCRTSpan.topologicalClosure ∧
      Filter.Tendsto QSquarefreeCapacity.capacity Filter.atTop Filter.atTop ∧
        RiemannHypothesis := by
  have hex : ∀ M, ∃ F : QHilbert, F ∈ qSquarefreeCRTSpan ∧
      (∀ i : Fin M, qSequence F (i.val + 1) = 1) ∧ ‖F‖ ^ 2 ≤ 1 / c :=
    fun M => exists_exact_head_of_frame (hv M) (hlegal M) M c hc
      (hfeasible M) (hframe M)
  choose F hlegalF hhead hnorm using hex
  apply QSquarefreeExactHeadAverages.squarefree_closure_capacity_and_rh_of_bounded_exact_heads
    F (B := 2 + 2 * (1 / c)) hlegalF
  · intro M
    have hp := sq_nonneg ‖qOne + F M‖
    rw [norm_add_sq_real, qOne_norm_sq] at hp
    rw [norm_sub_sq_real, qOne_norm_sq]
    have hb := hnorm M
    nlinarith
  · intro M k hk hkM
    let i : Fin M := ⟨k - 1, by omega⟩
    have hh := hhead M i
    have hi : i.val + 1 = k := by dsimp [i]; omega
    simpa only [hi] using hh

end RiemannResearch.RH.QSquarefreeHeadFrame
