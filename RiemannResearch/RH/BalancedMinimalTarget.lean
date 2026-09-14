import RiemannResearch.Analysis.ContinuousBiorthogonalDeletion
import RiemannResearch.RH.BalancedCoefficientTargets

/-!
# Finite deletions and the unique possible minimal balanced target family

Source: RH_Minimal_Seeds_Canonical_Basis_and_Arithmetic_Charge_20260914.md,
Section 5. The continuous coordinates and all finite-span identifications here
are actual Pareto objects. Infinite deletion remains precisely the displayed
target-closure condition and is not claimed as a theorem.
-/

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis
noncomputable section

/-- The actual indexed Hilbert dictionary has exactly the original legal span. -/
theorem balanced_dictionarySpan_univ :
    dictionarySpan balancedIndexHilbert Set.univ =
      hilbertLegalSubspace ({2, 3} : Set ℕ) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨i, hi, rfl⟩
    change hilbertSequence (balancedIndexHilbert i) ∈ legalSeedSpan {2, 3}
    rw [hilbertSequence_balancedIndex, ← balancedResidueSpan_eq_twoSeedSpan]
    exact Submodule.subset_span ⟨i.u, i.a, i.b, i.rough, rfl⟩
  · have hmap : balancedResidueSpan ≤
        (dictionarySpan balancedIndexHilbert Set.univ).map hilbertSequenceLinear := by
      apply Submodule.span_le.mpr
      rintro f ⟨u, a, b, hu, rfl⟩
      let i : BalancedArithmeticIndex := ⟨u, a, b, hu⟩
      refine ⟨balancedIndexHilbert i, ?_, ?_⟩
      · exact Submodule.subset_span ⟨i, Set.mem_univ _, rfl⟩
      · exact hilbertSequence_balancedIndex i
    intro f hf
    have hphys : hilbertSequence f ∈ balancedResidueSpan := by
      rw [balancedResidueSpan_eq_twoSeedSpan]
      exact hf
    obtain ⟨g, hg, he⟩ := hmap hphys
    have hgf : g = f := hilbertSequence_injective he
    change g ∈ dictionarySpan balancedIndexHilbert Set.univ at hg
    rw [hgf] at hg
    exact hg

theorem balanced_dictionaryClosure_univ :
    dictionaryClosure balancedIndexHilbert Set.univ =
      hilbertLegalClosure ({2, 3} : Set ℕ) := by
  unfold dictionaryClosure hilbertLegalClosure
  rw [balanced_dictionarySpan_univ]

def balancedNonzeroTargetSupport : Set BalancedArithmeticIndex :=
  {i | balancedCoefficientTarget i ≠ 0}

/-- Explicit arithmetic description of the source's proposed smallest support. -/
theorem mem_balancedNonzeroTargetSupport_iff (i : BalancedArithmeticIndex) :
    i ∈ balancedNonzeroTargetSupport ↔
      ArithmeticFunction.moebius i.u ≠ 0 ∧
        (i.a = i.b ∨ i.a = i.b + 1 ∨ (i.a = 0 ∧ i.b = 1)) := by
  exact balancedCut_signal_ne_zero_iff i.u i.a i.b i.rough

/-- OPEN: simultaneous deletion of all zero-target balanced coefficients.
This named proposition has no asserted proof. -/
def BalancedSupportThinning : Prop :=
  hilbertLegalClosure ({2, 3} : Set ℕ) = ⊤ →
    hilbertOne ∈ dictionaryClosure balancedIndexHilbert balancedNonzeroTargetSupport

/-- Every successful balanced subfamily contains the actual nonzero Möbius-cut
target support. -/
theorem balanced_nonzero_support_necessary
    (S : Set BalancedArithmeticIndex)
    (hS : hilbertOne ∈ dictionaryClosure balancedIndexHilbert S) :
    balancedNonzeroTargetSupport ⊆ S := by
  intro i hi
  apply biorthogonal_nonzero_target_mem balancedIndexHilbert balancedCoefficientCLM
    balancedCoefficientCLM_biorthogonal S hS i
  change balancedCoefficientTarget i ≠ 0 at hi
  rw [balancedCoefficientCLM_one]
  exact hi

/-- Exact finite-deletion criterion with the genuine continuous coefficients. -/
theorem balanced_finite_deletion_iff
    (S : Set BalancedArithmeticIndex) (J : Finset BalancedArithmeticIndex) :
    hilbertOne ∈ dictionaryClosure balancedIndexHilbert (S \ (J : Set _)) ↔
      hilbertOne ∈ dictionaryClosure balancedIndexHilbert S ∧
        ∀ i ∈ J, balancedCoefficientTarget i = 0 := by
  simpa only [balancedCoefficientCLM_one] using
    biorthogonal_delete_finite_iff balancedIndexHilbert balancedCoefficientCLM
      balancedCoefficientCLM_biorthogonal S J hilbertOne

/-- Removing any finite zero-target collection preserves the original two-seed
constant approximation problem. -/
theorem balanced_finite_zero_deletion_iff_twoSeed
    (J : Finset BalancedArithmeticIndex)
    (hJ : ∀ i ∈ J, balancedCoefficientTarget i = 0) :
    hilbertOne ∈ dictionaryClosure balancedIndexHilbert (Set.univ \ (J : Set _)) ↔
      hilbertOne ∈ hilbertLegalClosure ({2, 3} : Set ℕ) := by
  rw [balanced_finite_deletion_iff, balanced_dictionaryClosure_univ]
  exact and_iff_left hJ

/-- Any inclusion-minimal target family must be exactly the arithmetic target
support. Existence is not presupposed. -/
theorem balanced_minimal_target_eq_support
    (S : Set BalancedArithmeticIndex)
    (hS : IsMinimalTargetFamily balancedIndexHilbert hilbertOne S) :
    S = balancedNonzeroTargetSupport := by
  simpa only [balancedCoefficientCLM_one, balancedNonzeroTargetSupport] using
    biorthogonal_minimal_family_eq_support balancedIndexHilbert balancedCoefficientCLM
      balancedCoefficientCLM_biorthogonal hilbertOne S hS

/-- This exact equivalence isolates the still-open infinite-deletion question:
minimality exists if and only if the nonzero arithmetic support itself works. -/
theorem balanced_exists_minimal_iff_support_approximates :
    (∃ S, IsMinimalTargetFamily balancedIndexHilbert hilbertOne S) ↔
      hilbertOne ∈ dictionaryClosure balancedIndexHilbert balancedNonzeroTargetSupport := by
  simpa only [balancedCoefficientCLM_one, balancedNonzeroTargetSupport] using
    biorthogonal_exists_minimal_iff_support_approximates balancedIndexHilbert
      balancedCoefficientCLM balancedCoefficientCLM_biorthogonal hilbertOne

theorem balanced_each_generator_indispensable_for_density
    (S : Set BalancedArithmeticIndex) (i : BalancedArithmeticIndex) :
    balancedIndexHilbert i ∉ dictionaryClosure balancedIndexHilbert (S \ {i}) :=
  biorthogonal_deleted_generator_not_mem balancedIndexHilbert balancedCoefficientCLM
    balancedCoefficientCLM_biorthogonal S i

end
end RiemannResearch.RH.Pareto
