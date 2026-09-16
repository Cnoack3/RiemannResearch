import RiemannResearch.Analysis.FiniteHilbertGram
import RiemannResearch.RH.BalancedExactHeadEnergy

/-!
# Exact signed tail optimization for the minimal-support RH criterion

Source: `RH_Minimal_Seeds_Continuation_20260916.md`, Section 13, equations
(13.7)–(13.8). Every finite tail uses actual balanced Hilbert vectors and their
full signed Gram matrix. Invertibility follows from the established continuous
biorthogonal coordinates. The uniform gain estimate remains an explicit,
unproved hypothesis of the final reduction to Mathlib's Riemann Hypothesis.
-/

namespace RiemannResearch.RH.Pareto.BalancedFiniteTailGram
open scoped BigOperators
open RiemannResearch.Analysis
noncomputable section

/-- Actual Hilbert vectors indexed by a finite set of positive integers. -/
def family (S : Finset ℕ+) (m : S) : ThresholdHilbert := scalarBalancedHilbert m.val

theorem family_independent (S : Finset ℕ+) : LinearIndependent ℝ (family S) :=
  scalarBalancedHilbert_linearIndependent.comp _ Subtype.val_injective

/-- All selected vectors are permitted by the nonzero-target support and begin
strictly after the prescribed head. -/
def SupportedTail (N : ℕ) (S : Finset ℕ+) : Prop :=
  ∀ m ∈ S, N < (m : ℕ) ∧ scalarBalancedIndex m ∈ balancedNonzeroTargetSupport

/-- Exact inverse-Gram improvement, including all mixed terms. -/
def gain (N : ℕ) (S : Finset ℕ+) : ℝ :=
  ∑ m : S, FiniteHilbertGram.inverseCoeff (family_independent S) (balancedTargetHead N) m *
    FiniteHilbertGram.cross (family S) (balancedTargetHead N) m

/-- Simultaneous optimal additive correction; no sequential projection is used. -/
def optimizedHead (N : ℕ) (S : Finset ℕ+) : ThresholdHilbert :=
  balancedTargetHead N + Fintype.linearCombination ℝ (family S)
    (-FiniteHilbertGram.inverseCoeff (family_independent S) (balancedTargetHead N))

theorem optimizedHead_norm_sq (N : ℕ) (S : Finset ℕ+) :
    ‖optimizedHead N S‖ ^ 2 = ‖balancedTargetHead N‖ ^ 2 - gain N S :=
  FiniteHilbertGram.additive_inverse_schur_value (family_independent S) (balancedTargetHead N)

private theorem scalar_zero_before (m : ℕ+) (k : ℕ) (hkm : k < (m : ℕ)) :
    hilbertSequence (scalarBalancedHilbert m) k = 0 := by
  rw [hilbertSequence_scalarBalanced]
  simp [balancedSelected, dilation, residue, Nat.div_eq_of_lt hkm]

/-- Every signed correction in a supported tail preserves feasibility. -/
theorem correctedHead_feasible {N : ℕ} {S : Finset ℕ+} (hS : SupportedTail N S)
    (c : S → ℝ) :
    BalancedExactHeadEnergy.Feasible N
      (balancedTargetHead N + Fintype.linearCombination ℝ (family S) c) := by
  classical
  constructor
  · apply Submodule.add_mem _ (balancedTargetHead_mem_nonzeroTargetSpan N)
    rw [Fintype.linearCombination_apply]
    apply Submodule.sum_mem
    intro m _
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨scalarBalancedIndex m.val, (hS m.val m.property).2, rfl⟩
  · intro k hk hkN
    have hz : hilbertSequence (Fintype.linearCombination ℝ (family S) c) k = 0 := by
      change hilbertSequenceLinear (Fintype.linearCombination ℝ (family S) c) k = 0
      simp only [Fintype.linearCombination_apply, map_sum, Finset.sum_apply,
        map_smul, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_eq_zero
      intro m _
      change c m * hilbertSequence (scalarBalancedHilbert m.val) k = 0
      rw [scalar_zero_before m.val k (lt_of_le_of_lt hkN (hS m.val m.property).1), mul_zero]
    change hilbertSequenceLinear
      (balancedTargetHead N + Fintype.linearCombination ℝ (family S) c) k = 1
    rw [map_add]
    change hilbertSequence (balancedTargetHead N) k +
      hilbertSequence (Fintype.linearCombination ℝ (family S) c) k = 1
    rw [balancedTargetHead_exact N k hk hkN, hz, add_zero]

theorem optimizedHead_feasible {N : ℕ} {S : Finset ℕ+} (hS : SupportedTail N S) :
    BalancedExactHeadEnergy.Feasible N (optimizedHead N S) :=
  correctedHead_feasible hS _

/-- A concrete finite inverse-Gram calculation bounds the unrestricted optimum. -/
theorem energy_le_schur_value {N : ℕ} {S : Finset ℕ+} (hS : SupportedTail N S) :
    BalancedExactHeadEnergy.energy N ≤ ‖balancedTargetHead N‖ ^ 2 - gain N S := by
  rw [← optimizedHead_norm_sq]
  exact BalancedExactHeadEnergy.energy_le (optimizedHead_feasible hS)

/-- CONDITIONAL RESEARCH REDUCTION: the estimate supplied in `hC` is open.
Proving it for actual finite supported tails would prove Riemann Hypothesis. -/
theorem riemannHypothesis_of_uniform_tail_gain (C : ℝ)
    (hC : ∀ N : ℕ, ∃ S : Finset ℕ+, SupportedTail N S ∧
      ‖balancedTargetHead N‖ ^ 2 - gain N S ≤ C) : RiemannHypothesis := by
  apply BalancedExactHeadEnergy.riemannHypothesis_of_energy_bddAbove
  refine ⟨C, ?_⟩
  rintro e ⟨N, rfl⟩
  obtain ⟨S, hS, hbound⟩ := hC N
  exact (energy_le_schur_value hS).trans hbound

end
end RiemannResearch.RH.Pareto.BalancedFiniteTailGram
