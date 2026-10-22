import RiemannResearch.Analysis.MultiplicativeSequenceRigidity
import RiemannResearch.RH.ThresholdDyadicTailSummability
import RiemannResearch.RH.ThresholdTwoSeedConverse

/-!
# Actual two-seed adjoint rigidity and the full-density converse

Source: user-provided `RH_Iff_Two_Seed_Approximation_20260914.md`, Sections 3--5.
The fixed-space theorem is unconditional and concerns the existing complete
Pareto Hilbert space and its genuine adjoints. The last theorem assumes full
remainder density and proves two-seed density; it does not assume that RH
supplies the full-density input.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- The actual joint adjoint fixed space consists exactly of constants. -/
theorem hilbertDilationAdjoint_two_three_fixed_iff (f : ThresholdHilbert) :
    (hilbertDilationAdjoint 2 (by norm_num) f = f ∧
      hilbertDilationAdjoint 3 (by norm_num) f = f) ↔
      ∃ c : ℝ, f = c • hilbertOne := by
  constructor
  · rintro ⟨h2, h3⟩
    have hc := RiemannResearch.Analysis.multiplicativeSequence_rigidity
      (hilbertNormalizedTail f)
      (fun n hn => hilbertNormalizedTail_scaling f 2 n (by norm_num) hn h2)
      (fun n hn => hilbertNormalizedTail_scaling f 3 n (by norm_num) hn h3)
      (hilbertNormalizedTail_increment_square_summable_of_dyadic_fixed f h2)
    exact ⟨hilbertNormalizedTail f 1,
      eq_smul_hilbertOne_of_normalizedTail_constant f (hilbertNormalizedTail f 1) hc⟩
  · rintro ⟨c, rfl⟩
    constructor <;> rw [map_smul, hilbertDilationAdjoint_one]

/-- Full remainder density implies two-seed density with the rigidity
obligation completely discharged by the preceding theorem. -/
theorem twoSeed_legalClosure_eq_top_of_full_density
    (hfull : hilbertLegalClosure {n : ℕ | 0 < n} = ⊤) :
    hilbertLegalClosure {2, 3} = ⊤ :=
  twoSeed_legalClosure_eq_top_of_full_density_of_joint_fixed_constants hfull
    (fun f h2 h3 => (hilbertDilationAdjoint_two_three_fixed_iff f).mp ⟨h2, h3⟩)

theorem twoSeed_legalClosure_le_full :
    hilbertLegalClosure {2, 3} ≤ hilbertLegalClosure {n : ℕ | 0 < n} := by
  have hs : legalSeedSpan ({2, 3} : Set ℕ) ≤ legalSeedSpan {n : ℕ | 0 < n} := by
    apply Submodule.span_mono
    rintro f ⟨a, ha, m, hm, rfl⟩
    refine ⟨a, ?_, m, hm, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl <;> norm_num
  exact Submodule.topologicalClosure_mono (Submodule.comap_mono hs)

/-- Unconditional equivalence between density of the two-seed space and
density of the full remainder space, in the same actual Pareto norm.
This does not claim equality of their closures when they are proper. -/
theorem twoSeed_density_iff_full_density :
    hilbertLegalClosure {2, 3} = ⊤ ↔
      hilbertLegalClosure {n : ℕ | 0 < n} = ⊤ := by
  constructor
  · intro h
    apply top_unique
    rw [← h]
    exact twoSeed_legalClosure_le_full
  · exact twoSeed_legalClosure_eq_top_of_full_density

end
end RiemannResearch.RH.Pareto
