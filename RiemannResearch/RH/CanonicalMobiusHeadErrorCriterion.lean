/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CanonicalMobiusHeadRepair
import RiemannResearch.RH.ExactHeadCofinalBounds

/-!
# Cofinal bounded exact heads and actual closure membership

Source: user-provided Green-Pareto-Schur continuation and the requested
GitHub improvement, 6 October 2026. All errors are complete Pareto norms.
The closure criterion is explicit; no RH-to-density converse is assumed.
-/
noncomputable section
open scoped Topology
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
/-- A conductor schedule with exact growing heads and a common error bound
at arbitrarily late indices. -/
def FiniteCofinalBoundedExactHeads : Prop :=
  ∃ support : ℕ → ℕ, ∃ x : ℕ → ThresholdHilbert, ∃ C : ℝ,
    (∀ N, N ≤ support N ∧ x N ∈ finiteSpace (support N) ∧
      ∀ j, 0 < j → j ≤ N → hilbertSequence (x N) j = 1) ∧
    (∀ M, ∃ N, M ≤ N ∧ ‖hilbertOne - x N‖ ^ 2 ≤ C)

/-- A cofinal bounded-error certificate is already equivalent to the
actual closure criterion. The support schedule remains unrestricted. -/
theorem finiteCofinalBoundedExactHeads_iff_one_mem_closedSpace :
    FiniteCofinalBoundedExactHeads ↔ hilbertOne ∈ closedSpace := by
  constructor
  · rintro ⟨support, x, C, hx, hC⟩
    apply limitEnergy_zero_iff_mem.mp
    apply limitEnergy_eq_zero_of_cofinally_bounded_exact_head_errors x
      (fun N => Submodule.le_topologicalClosure _
        (RiemannResearch.Analysis.ExhaustiveWalk.walkSpan_le
          residueAtom id _ (hx N).2.1))
      (fun N j hj hjN => (hx N).2.2 j hj hjN) C hC
  · intro hz
    obtain ⟨support, x, hx⟩ := exists_legal_exact_head_arbitrary_error_budget
      hilbertOne hz (fun _ => 1) (fun _ => by norm_num)
    refine ⟨support, x, 1, ?_, ?_⟩
    · intro N
      refine ⟨(hx N).1, (hx N).2.1, ?_⟩
      intro j hj hjN
      have he := (hx N).2.2.1 j hj hjN
      rw [hilbertOne_sequence] at he
      simpa [zeroAnchor, Nat.ne_of_gt hj] using he
    · intro M
      refine ⟨M, le_rfl, ?_⟩
      rw [norm_sub_rev]
      exact (hx M).2.2.2.le


end RiemannResearch.RH.Pareto.CoefficientStabilization
