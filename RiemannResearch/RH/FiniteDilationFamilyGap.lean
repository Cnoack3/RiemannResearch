import RiemannResearch.RH.ParetoCoordinateEvaluation
import RiemannResearch.RH.ThresholdHilbertAdjoint
import RiemannResearch.Analysis.ContinuousBiorthogonalDeletion

/-!
# No fixed finite family of legal generators approximates the constant

Source: RH_Minimal_Seeds_Canonical_Basis_and_Arithmetic_Charge_20260914.md,
Section 11. A common integer multiple is an actual positive-mass Pareto atom.
-/

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis
open scoped BigOperators
noncomputable section

/-- A vanishing physical coordinate gives an exact positive error floor. -/
theorem hilbert_error_lower_of_zero_coordinate (f : ThresholdHilbert)
    (Q : ℕ) (hQ : 0 < Q) (hf : hilbertSequence f Q = 0) :
    positiveWeight Q ≤ ‖hilbertOne - f‖ ^ 2 := by
  rw [hilbert_norm_weighted_sq]
  have hs := (hilbertSequence_square_summable (hilbertOne - f)).le_tsum Q
    (fun n _ => mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _))
  simpa [hilbertSequence_sub, hilbertOne_sequence, zeroAnchor, hQ.ne', hf] using hs

/-- At a common multiple of both remainder endpoints every selected generator vanishes. -/
theorem dilation_residue_zero_of_endpoint_dvd (a m Q : ℕ)
    (hQ : a * m ∣ Q) : dilation m (residue a) Q = 0 := by
  have hm : m ∣ Q := dvd_trans (dvd_mul_left m a) hQ
  have ham : m * a ∣ Q := by simpa [Nat.mul_comm] using hQ
  have he := residue_mul_floor m a Q
  have hz1 : residue (m * a) Q = 0 := by simp [residue, Nat.mod_eq_zero_of_dvd ham]
  have hz2 : residue m Q = 0 := by simp [residue, Nat.mod_eq_zero_of_dvd hm]
  linarith

/-- The entire closed span still vanishes at a common endpoint multiple. -/
theorem finiteDilationClosure_zero_at_multiple {ι : Type*} [DecidableEq ι]
    (v : ι → ThresholdHilbert) (a m : ι → ℕ) (S : Set ι)
    (hv : ∀ i ∈ S, hilbertSequence (v i) = dilation (m i) (residue (a i)))
    (Q : ℕ) (hQ : 0 < Q) (hd : ∀ i ∈ S, a i * m i ∣ Q)
    {f : ThresholdHilbert} (hf : f ∈ dictionaryClosure v S) :
    hilbertSequence f Q = 0 := by
  let l := physicalEvaluationCLM (Q - 1)
  have hl (g : ThresholdHilbert) : l g = hilbertSequence g Q := by
    simp only [l, physicalEvaluationCLM_apply, Nat.sub_add_cancel hQ]
  have hspan : ∀ g ∈ dictionarySpan v S, l g = 0 := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
        obtain ⟨i, hi, rfl⟩ := hg
        rw [hl, hv i hi]
        exact dilation_residue_zero_of_endpoint_dvd _ _ _ (hd i hi)
    | zero => simp
    | add g h hg hh ihg ihh => simp [map_add, ihg, ihh]
    | smul c g hg ih => simp [map_smul, ih]
  have hz := (closure_minimal hspan (isClosed_eq l.continuous continuous_const)) hf
  change l f = 0 at hz
  rwa [hl] at hz

/-- A finite collection of individual generators has a positive full-norm gap.
The explicit common multiple is the product of its positive endpoints. -/
theorem finiteDilationFamily_distance_gap {ι : Type*} [DecidableEq ι]
    (v : ι → ThresholdHilbert) (a m : ι → ℕ) (s : Finset ι)
    (ha : ∀ i ∈ s, 0 < a i) (hm : ∀ i ∈ s, 0 < m i)
    (hv : ∀ i ∈ s, hilbertSequence (v i) = dilation (m i) (residue (a i))) :
    ∃ Q : ℕ, 0 < Q ∧ ∀ f ∈ dictionaryClosure v (s : Set ι),
      positiveWeight Q ≤ ‖hilbertOne - f‖ ^ 2 := by
  let Q := ∏ i ∈ s, a i * m i
  have hQ : 0 < Q := Finset.prod_pos (fun i hi => Nat.mul_pos (ha i hi) (hm i hi))
  refine ⟨Q, hQ, ?_⟩
  intro f hf
  apply hilbert_error_lower_of_zero_coordinate f Q hQ
  exact finiteDilationClosure_zero_at_multiple v a m (s : Set ι) hv Q hQ
    (fun i hi => Finset.dvd_prod_of_mem (fun i => a i * m i) hi) hf

end
end RiemannResearch.RH.Pareto
