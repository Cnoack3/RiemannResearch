/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeHeadCompression
import RiemannResearch.RH.QSquarefreeHeadRepair
import RiemannResearch.RH.QSquarefreeExactHeadAverages
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.Analysis.FiniteHilbertConstraints
import RiemannResearch.Analysis.FiniteFeasibleGramRepair
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import RiemannResearch.Analysis.FiniteHilbertGram
import RiemannResearch.Analysis.FiniteConstrainedProjection
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The reduced complete-Q Gram repair system

Source: user-provided compression request, 22 October 2026. This assembles
QSquarefreeHeadCompression with the existing exact constrained projection.
Every inner product is the complete Q pairing. The signed infinite-tail
identity and norm-square remainder are retained. The uniform directional
repair bound remains an open arithmetic provider.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeReducedGram
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeHeadCompression QSquarefreeHeadRepair
open Analysis.FiniteHilbertGram Analysis.FiniteHilbertConstraints
open Analysis.FiniteConstrainedProjection Analysis.FiniteFeasibleGramRepair

variable {ι : Type*} [Fintype ι] {v : ι → QHilbert}

/-- Entries of A G^{-1} A^T, using the existing actual complete Gram inverse. -/
theorem reduced_gram_entry (hv : LinearIndependent ℝ v) (M : ℕ)
    (i j : sites M) :
    inner ℝ (projectedRow hv (observation M) i) (projectedRow hv (observation M) j) =
      ∑ d, inner ℝ (observation M i) (v d) * inverseCoeff hv (observation M j) d := by
  change inner ℝ (projectedRow hv (observation M) i)
    (Fintype.linearCombination ℝ v (inverseCoeff hv (observation M j))) = _
  rw [← projectedRow_pairing hv (observation M) (inverseCoeff hv (observation M j)) i]
  rw [Fintype.linearCombination_apply, inner_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [inner_smul_right, mul_comm]

/-- Every reduced normal repair is a literal exact physical-head repair. -/
theorem repaired_head (hv : LinearIndependent ℝ v)
    (hlegal : ∀ i, v i ∈ qSquarefreeCRTSpan) (M : ℕ)
    (hr : LinearIndependent ℝ (projectedRow hv (observation M))) :
    ∀ n, 0 < n → n ≤ M →
      qSequence (correctedProjection hv (observation M) hr qOne) n = 1 := by
  have hF : correctedProjection hv (observation M) hr qOne ∈ qSquarefreeCRTSpan := by
    apply Submodule.add_mem
    · exact legal_synthesis v hlegal _
    · apply legal_synthesis
      intro i
      exact legal_synthesis v hlegal _
  have hh := (observations_iff_head M _ qOne
    (legal_radicalCompatible _ hF) one_radicalCompatible).mp
      (correctedProjection_observation hv (observation M) hr qOne)
  intro n hn hnM
  rw [hh n hn hnM, qSequence_qOne]
  simp [qOneSequence, ne_of_gt hn]

/-- Complete norm equals the infinite tail once the literal physical head is exact. -/
theorem exact_head_tail (M : ℕ) (F : QHilbert)
    (hh : ∀ n, 0 < n → n ≤ M → qSequence F n = 1) :
    ‖qOne - F‖ ^ 2 = ∑' n, if M < n then
      positiveQWeight n * (1 - qSequence F n) ^ 2 else 0 := by
  rw [qNorm_weighted_sq]
  apply tsum_congr
  intro n
  have hsub := congrFun (qSequenceLinear.map_sub qOne F) n
  change qSequence (qOne - F) n = qSequence qOne n - qSequence F n at hsub
  rw [hsub]
  by_cases hn : n = 0
  · subst n
    simp [positiveQWeight]
  · have h1 : qSequence qOne n = 1 := by
      rw [qSequence_qOne]; simp [qOneSequence, hn]
    rw [h1]
    split_ifs with h
    · rfl
    · rw [hh n (Nat.pos_of_ne_zero hn) (by omega)]
      simp

/-- The reduced inverse-Gram cost is exactly the full constrained error minus
its unconstrained projection deficit. No tail truncation occurs. -/
theorem reduced_complete_tail_identity (hv : LinearIndependent ℝ v)
    (hlegal : ∀ i, v i ∈ qSquarefreeCRTSpan) (M : ℕ)
    (hr : LinearIndependent ℝ (projectedRow hv (observation M))) :
    (∑' n, if M < n then positiveQWeight n *
      (1 - qSequence (correctedProjection hv (observation M) hr qOne) n) ^ 2 else 0) =
      ‖projectionResidual hv qOne‖ ^ 2 +
        ∑ i, (gramEquiv hr).symm (headMismatch hv (observation M) qOne) i *
          headMismatch hv (observation M) qOne i := by
  rw [← exact_head_tail M _ (repaired_head hv hlegal M hr)]
  exact correctedProjection_error_inverseGram hv (observation M) hr qOne

/-- Compression preserves the physical constrained optimum and its complete
norm-square remainder, not merely feasibility of one selected candidate. -/
theorem physical_constrained_completion (hv : LinearIndependent ℝ v)
    (hlegal : ∀ i, v i ∈ qSquarefreeCRTSpan) (M : ℕ)
    (hr : LinearIndependent ℝ (projectedRow hv (observation M))) (c : ι → ℝ)
    (hh : ∀ n, 0 < n → n ≤ M →
      qSequence (Fintype.linearCombination ℝ v c) n = 1) :
    ‖qOne - Fintype.linearCombination ℝ v c‖ ^ 2 =
      ‖qOne - correctedProjection hv (observation M) hr qOne‖ ^ 2 +
        ‖Fintype.linearCombination ℝ v c - correctedProjection hv (observation M) hr qOne‖ ^ 2 := by
  apply constrained_error_completion hv (observation M) hr qOne c
  apply (observations_iff_head M _ qOne
    (legal_radicalCompatible _ (legal_synthesis v hlegal c)) one_radicalCompatible).mpr
  intro n hn hnM
  rw [hh n hn hnM, qSequence_qOne]
  simp [qOneSequence, ne_of_gt hn]

/-- Unconditional signed decomposition for every correction, before any
orthogonality or normal equation is used. -/
theorem signed_correction_tail (M : ℕ) (P U : QHilbert)
    (hh : ∀ n, 0 < n → n ≤ M → qSequence (P + U) n = 1) :
    (∑' n, if M < n then positiveQWeight n *
      (1 - qSequence (P + U) n) ^ 2 else 0) =
      ‖qOne - P‖ ^ 2 - 2 * inner ℝ (qOne - P) U + ‖U‖ ^ 2 := by
  rw [← exact_head_tail M (P + U) hh]
  have he : qOne - (P + U) = (qOne - P) - U := by abel
  rw [he, norm_sub_sq_real]

/-- The normalized complete Q weights are retained even for structurally
redundant physical sites. -/
def headEnergy (M : ℕ) (F : QHilbert) : ℝ :=
  ∑ n ∈ Finset.range (M + 1), positiveQWeight n * (qSequence F n) ^ 2

theorem headEnergy_succ (M : ℕ) (F : QHilbert) :
    headEnergy (M + 1) F = headEnergy M F +
      positiveQWeight (M + 1) * (qSequence F (M + 1)) ^ 2 := by
  exact Finset.sum_range_succ _ _

theorem headEnergy_mono_step (M : ℕ) (F : QHilbert) :
    headEnergy M F ≤ headEnergy (M + 1) F := by
  rw [headEnergy_succ]
  exact le_add_of_nonneg_right
    (mul_nonneg (positiveQWeight_nonneg _) (sq_nonneg _))

/-- Conditional research reduction. Only the actual target-direction reduced
repair costs require a uniform bound. Independence is supplied concretely by
QSquarefreeHeadCompression.projected_observations_independent. -/
theorem closure_capacity_rh_of_uniform_reduced_cost
    (J : ℕ → ℕ) (v : ∀ M, Fin (J M) → QHilbert)
    (hv : ∀ M, LinearIndependent ℝ (v M))
    (hlegal : ∀ M i, v M i ∈ qSquarefreeCRTSpan)
    (hr : ∀ M, LinearIndependent ℝ (projectedRow (hv M) (observation M)))
    (B : ℝ)
    (hcost : ∀ M, ∑ i, (gramEquiv (hr M)).symm
      (headMismatch (hv M) (observation M) qOne) i *
        headMismatch (hv M) (observation M) qOne i ≤ B) :
    qOne ∈ qSquarefreeCRTSpan.topologicalClosure ∧
      Filter.Tendsto QSquarefreeCapacity.capacity Filter.atTop Filter.atTop ∧
        RiemannHypothesis := by
  let F : ℕ → QHilbert := fun M => correctedProjection (hv M) (observation M) (hr M) qOne
  apply QSquarefreeExactHeadAverages.squarefree_closure_capacity_and_rh_of_bounded_exact_heads
    F (B := 1 + B)
  · intro M
    apply Submodule.add_mem
    · exact legal_synthesis _ (hlegal M) _
    · apply legal_synthesis
      intro i
      exact legal_synthesis _ (hlegal M) _
  · intro M
    rw [show F M = correctedProjection (hv M) (observation M) (hr M) qOne from rfl,
      correctedProjection_error_inverseGram]
    exact add_le_add (projection_residual_sq_le_one (hv M)) (hcost M)
  · intro M
    exact repaired_head (hv M) (hlegal M) M (hr M)


/-- The transported head metric keeps every physical weight, including
redundant nonsquarefree rows. Its matrix is R^T diag(Q(n)) R. -/
theorem headEnergy_reconstructed (M : ℕ) (F : QHilbert)
    (R : Fin M → sites M → ℝ)
    (hR : ∀ i : Fin M, qSequence F (i.val + 1) =
      ∑ j, R i j * inner ℝ (observation M j) F) :
    headEnergy M F = ∑ i : Fin M, positiveQWeight (i.val + 1) *
      (∑ j, R i j * inner ℝ (observation M j) F) ^ 2 := by
  unfold headEnergy
  rw [Finset.sum_range_succ']
  simp only [show positiveQWeight 0 = 0 from by simp [positiveQWeight], zero_mul, add_zero]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hR i]


end RiemannResearch.RH.QSquarefreeReducedGram
