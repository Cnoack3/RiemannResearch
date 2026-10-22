import RiemannResearch.RH.ThresholdBoundedInterpolation
import RiemannResearch.RH.ParetoGibbsTailBasis
import Mathlib.Tactic.Ring

/-!
# Completeness from the target and all integer dilations

Source: user-provided argument in the September 9, 2026 conversation.
The Pareto tail basis is exactly the consecutive-dilation difference of
the target. Consequently a closed all-integer legal space containing the
target is the entire weighted Hilbert space.

The final uniform interpolation bound remains an explicit open arithmetic
input; this file does not assert that bound or the Riemann Hypothesis.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- The exact martingale tail basis is a difference of target dilations. -/
theorem tailBasisHilbert_eq_dilation_one (n : ℕ) :
    tailBasisHilbert n =
      hilbertDilation (n+1) (by omega) hilbertOne -
      hilbertDilation (n+2) (by omega) hilbertOne := by
  apply hilbertSequence_injective
  have hsub (f g : ThresholdHilbert) :
      hilbertSequence (f-g) = hilbertSequence f - hilbertSequence g :=
    hilbertSequenceLinear.map_sub f g
  rw [hsub, hilbertDilation_sequence, hilbertDilation_sequence, hilbertOne_sequence]
  funext k
  cases k with
  | zero => simp [dilation, zeroAnchor]
  | succ k =>
    change hilbertGibbsPhysical (tailBasisHilbert n) k = _
    rw [hilbertGibbsPhysical_tailBasis]
    by_cases he : k = n
    · subst k
      have hlt : n+1 < n+2 := by omega
      simp [tailBasisPhysical, dilation, zeroAnchor, Nat.div_self (by omega : 0 < n+1),
        Nat.div_eq_of_lt hlt]
    · by_cases hlt : k < n
      · have h1 : k+1 < n+1 := by omega
        have h2 : k+1 < n+2 := by omega
        have hn : ¬ n < k := by omega
        simp [tailBasisPhysical, he, hn, dilation, zeroAnchor,
          Nat.div_eq_of_lt h1, Nat.div_eq_of_lt h2]
      · have hn : n < k := by omega
        have h1 : (k+1)/(n+1) ≠ 0 := by
          apply Nat.ne_of_gt
          exact Nat.div_pos (by omega) (by omega)
        have h2 : (k+1)/(n+2) ≠ 0 := by
          apply Nat.ne_of_gt
          exact Nat.div_pos (by omega) (by omega)
        simp [tailBasisPhysical, he, hn, dilation, zeroAnchor, h1, h2]
        ring

/-- Target membership forces density because every positive integer dilation
is available. No RH equivalence is used in this proof. -/
theorem hilbertLegalClosure_eq_top_of_one_mem (A : Set ℕ)
    (hone : hilbertOne ∈ hilbertLegalClosure A) :
    hilbertLegalClosure A = ⊤ := by
  let V := hilbertLegalClosure A
  have hV : IsClosed (V : Set ThresholdHilbert) :=
    (hilbertLegalSubspace A).isClosed_topologicalClosure
  have : CompleteSpace V := inferInstance
  apply Submodule.orthogonal_eq_bot_iff.mp
  apply le_antisymm
  · intro f hf
    change f = 0
    apply tailBasis_total
    · rw [real_inner_comm]
      exact (V.mem_orthogonal f).mp hf hilbertOne hone
    · intro n
      rw [real_inner_comm]
      apply (V.mem_orthogonal f).mp hf
      rw [tailBasisHilbert_eq_dilation_one]
      exact V.sub_mem
        (hilbertLegalClosure_dilation A hone (n+1) (by omega))
        (hilbertLegalClosure_dilation A hone (n+2) (by omega))
  · exact bot_le

/-- Explicit open arithmetic target. This definition supplies no witness. -/
def UniformLegalExactHeadBound (A : Set ℕ) : Prop :=
  ∃ C : ℝ, ∀ N : ℕ, ∃ f : ThresholdHilbert,
    f ∈ hilbertLegalSubspace A ∧
    (∀ k : ℕ, 0 < k → k ≤ N → hilbertSequence f k = 1) ∧
    ‖f‖^2 ≤ C

/-- The proved consequence of the open uniform bound is full Hilbert density. -/
theorem hilbertLegalClosure_eq_top_of_uniform_exact_head_bound (A : Set ℕ)
    (h : UniformLegalExactHeadBound A) : hilbertLegalClosure A = ⊤ := by
  obtain ⟨C, hC⟩ := h
  exact hilbertLegalClosure_eq_top_of_one_mem A
    (hilbertLegalClosure_of_bounded_exact_heads A C hC)

end
end RiemannResearch.RH.Pareto
