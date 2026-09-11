import RiemannResearch.RH.ParetoAnnihilatorPositivity
import RiemannResearch.RH.ParetoLegalApproximationClosure
import RiemannResearch.RH.ThresholdInterpolationCompleteness

/-!
# The actual legal annihilator and Pareto completeness

Source: user-provided September 11, 2026 conversation about independence,
completeness, indicator reduction, and absolute-value closure.

The previously proved theorem `hilbertLegalClosure_eq_top_of_one_mem`
already establishes completeness from constant approximation, by actual
bounded integer dilations and a complete tail basis. This module supplies
the bridge from the sequence annihilator used in the positivity argument
to the genuine Hilbert orthogonal complement.

Signed annihilator uniqueness and absolute-value closure remain explicit
domain-specific hypotheses in the respective conditional research reductions.
No such uniqueness or closure property is asserted unconditionally.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Hilbert orthogonality to the actual closed legal space implies membership
in the weighted sequence annihilator, including unbounded L2 vectors. -/
theorem legalAnnihilator_of_hilbert_orthogonal
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    {h : ThresholdHilbert} (hh : h ∈ (hilbertLegalClosure A)ᗮ) :
    LegalAnnihilator A (hilbertSequence h) := by
  refine ⟨hilbertSequence_square_summable h, ?_⟩
  intro g hg
  obtain ⟨f, hf, hfg⟩ := legalSeedSpan_exists_hilbert A hA hg
  have hfclosed : f ∈ hilbertLegalClosure A :=
    (hilbertLegalSubspace A).le_topologicalClosure hf
  have ho := (Submodule.mem_orthogonal _ _).mp hh f hfclosed
  rw [real_inner_comm, hilbert_inner_weighted, hfg] at ho
  exact ho

/-- Conditional research reduction: uniqueness for signed weighted sequence
annihilators implies completeness of the actual legal Hilbert space.
The zero coordinate carries no mass and is anchored in the Hilbert realization. -/
theorem hilbertLegalClosure_eq_top_of_legalAnnihilator_unique
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (hunique : ∀ h : ℕ → ℝ, LegalAnnihilator A h →
      ∀ n : ℕ, 0 < n → h n = 0) :
    hilbertLegalClosure A = ⊤ := by
  let V := hilbertLegalClosure A
  have hV : IsClosed (V : Set ThresholdHilbert) :=
    (hilbertLegalSubspace A).isClosed_topologicalClosure
  have : CompleteSpace V := inferInstance
  apply Submodule.orthogonal_eq_bot_iff.mp
  apply le_antisymm
  · intro f hf
    change f = 0
    have hseq := hunique (hilbertSequence f)
      (legalAnnihilator_of_hilbert_orthogonal A hA hf)
    apply hilbertSequence_injective
    have hzero : hilbertSequence (0 : ThresholdHilbert) = 0 :=
      hilbertSequenceLinear.map_zero
    rw [hzero]
    funext n
    cases n with
    | zero => exact hilbertSequence_zero f
    | succ n => exact hseq (n+1) (Nat.succ_pos n)
  · exact bot_le

/-- Conditional research reduction: absolute-value stability of the entire
signed annihilator, together with the proved nonnegative uniqueness theorem,
forces full legal completeness. Absolute-value stability is the open input. -/
theorem hilbertLegalClosure_eq_top_of_annihilator_abs_closed
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) (h2 : 2 ∈ A)
    (habs : ∀ h, LegalAnnihilator A h →
      LegalAnnihilator A (fun n => |h n|)) :
    hilbertLegalClosure A = ⊤ :=
  hilbertLegalClosure_eq_top_of_legalAnnihilator_unique A hA
    (fun _ hh _ hn => legalAnnihilator_eq_zero_of_abs_closed h2 habs hh hn)

/-- Conditional research reduction to the actual Riemann hypothesis.
The substantive hypothesis is absolute-value closure of the signed legal
annihilator; monotone convergence and indicator uniqueness do not supply it. -/
theorem riemannHypothesis_of_legalAnnihilator_abs_closed
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) (h2 : 2 ∈ A)
    (habs : ∀ h, LegalAnnihilator A h →
      LegalAnnihilator A (fun n => |h n|)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_hilbertOne_mem_legalClosure A hA
  rw [hilbertLegalClosure_eq_top_of_annihilator_abs_closed A hA h2 habs]
  trivial

end
end RiemannResearch.RH.Pareto
