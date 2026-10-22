import RiemannResearch.RH.PrimeSieveDerivativeApproximation
import RiemannResearch.RH.ThresholdHilbertDifference
import RiemannResearch.RH.MobiusCoefficientStabilization

/-!
# The derivative target is in the actual residue-derivative closure

Source: the sieve argument in `CRTPrimitiveTransferAudit20260929.md`, §6.
The approximants are explicit finite sums of the existing normalized residue
atoms, not merely members of a larger comparison space. The error is the full
Pareto Hilbert norm.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative PrimitiveEnergy
open CoefficientStabilization
open RiemannResearch.Analysis.ExhaustiveWalk

/-- The physical sieve as an actual finite sum of normalized residue Hilbert atoms. -/
def derivativeSieveHilbert (Y : ℕ) : ThresholdHilbert :=
  ∑ d ∈ Y.factorial.divisors,
    if 2 ≤ d then -(ArithmeticFunction.moebius d : ℝ) • residueAtom (d - 2) else 0

theorem derivativeSieveHilbert_sequence (Y : ℕ) :
    hilbertSequence (derivativeSieveHilbert Y) = derivativeSievePrimitive Y := by
  unfold derivativeSieveHilbert
  change hilbertSequenceLinear _ = _
  rw [map_sum]
  funext n
  simp only [Finset.sum_apply]
  change (∑ d ∈ Y.factorial.divisors, hilbertSequence
    (if 2 ≤ d then -(ArithmeticFunction.moebius d : ℝ) • residueAtom (d - 2) else 0) n) = _
  unfold derivativeSievePrimitive sieveResidue
  simp only [Nat.one_mul]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hd2 : 2 ≤ d
  · simp only [if_pos hd2, hilbertSequence_smul, residueAtom,
      normalizedResidueHilbert_sequence, Nat.sub_add_cancel hd2,
      Pi.smul_apply, smul_eq_mul]
    ring
  · have hd1 : d = 1 := by
      have := Nat.pos_of_mem_divisors hd
      omega
    subst d
    cases n <;> simp [residueFraction, hilbertSequence, Nat.mod_one]

/-- Each sieve derivative belongs to the finite span of the actual derivative dictionary. -/
theorem derivativeSieveHilbert_mem_span (Y : ℕ) :
    hilbertDifference (derivativeSieveHilbert Y) ∈ Submodule.span ℝ
      (Set.range (fun i => hilbertDifference (residueAtom i))) := by
  unfold derivativeSieveHilbert
  rw [map_sum]
  apply Submodule.sum_mem
  intro d hd
  by_cases hd2 : 2 ≤ d
  · rw [if_pos hd2, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨d - 2, rfl⟩)
  · simp only [if_neg hd2, map_zero, Submodule.zero_mem]

/-- Exact identity transfers the physical full error to the actual Hilbert norm. -/
theorem derivativeSieveHilbert_error (Y : ℕ) :
    ‖hilbertAtom 1 (by decide) - hilbertDifference (derivativeSieveHilbert Y)‖^2 =
      derivativeSieveError Y := by
  rw [hilbert_norm_weighted_sq, hilbertSequence_sub, hilbertDifference_sequence,
    hilbertAtom_sequence, derivativeSieveHilbert_sequence]
  simp only [derivativeSieveError, PrimitiveEnergy.energy, paretoInner,
    Pi.sub_apply, pow_two]

/-- Unconditional density at the derivative target for the exact legal atom dictionary. -/
theorem derivative_target_mem_dictionaryClosure :
    hilbertAtom 1 (by decide) ∈ dictionaryClosure
      (fun i => hilbertDifference (residueAtom i)) := by
  change hilbertAtom 1 (by decide) ∈ closure
    ((Submodule.span ℝ (Set.range (fun i => hilbertDifference (residueAtom i)))) :
      Set ThresholdHilbert)
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have he : ∀ᶠ Y : ℕ in atTop, derivativeSieveError Y < ε^2 :=
    derivativeSieveError_tendsto_zero.eventually (gt_mem_nhds (sq_pos_of_pos hε))
  obtain ⟨Y, hY⟩ := he.exists
  refine ⟨hilbertDifference (derivativeSieveHilbert Y),
    derivativeSieveHilbert_mem_span Y, ?_⟩
  rw [dist_eq_norm]
  rw [← derivativeSieveHilbert_error Y] at hY
  nlinarith [norm_nonneg (hilbertAtom 1 (by decide) -
    hilbertDifference (derivativeSieveHilbert Y))]

/-- Exhaustive derivative-optimal errors tend to zero without RH. -/
theorem derivative_optimal_error_tendsto_zero :
    Tendsto (walkError (fun i => hilbertDifference (residueAtom i)) id
      (hilbertAtom 1 (by decide))) atTop (𝓝 0) :=
  (walkError_tendsto_zero_iff _ id Function.surjective_id _).mpr
    derivative_target_mem_dictionaryClosure

end RiemannResearch.RH.Pareto
