import RiemannResearch.RH.ThresholdJointAdjointRigidity
import RiemannResearch.RH.ThresholdRiemannHypothesis
import RiemannResearch.RH.ParetoMeanOneApproximation

/-!
# Explicit provider boundary for the two-seed RH equivalence

Source: user-provided proof in
`RH_Iff_Two_Seed_Approximation_20260914.md`, Sections 1, 5, and 6.
The external strong Nyman--Beurling/Báez-Duarte theorem is stated for the exact
discrete Pareto Hilbert space by B. Bagchi, "On Nyman, Beurling and Baez-Duarte's
Hilbert space reformulation of the Riemann hypothesis", Theorem 1,
https://arxiv.org/abs/math/0607733 . This reference supports the mathematical
statement of the full-residue RH-to-density input. It is not a Lean provider.

The approximation-to-RH implication used here is already proved in the
repository by the actual continuous Mellin functional. The reverse implication
still has an explicit full-residue density provider argument. Until a checked
declaration supplies that argument, these RH equivalences are conditional
formalization results. Joint-adjoint rigidity is now a proved dependency and
is no longer an assumption in these declarations.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section
open Filter
open scoped Topology

/-- Exact identification of the full positive-seed closure with the closure
of the physical finite residue span in the original weighted Hilbert space. -/
theorem hilbertLegalClosure_positive_eq_residue_closure :
    hilbertLegalClosure {n : ℕ | 0 < n} =
      ((Submodule.span ℝ
        {f : ℕ → ℝ | ∃ n : ℕ, 0 < n ∧ f = residue n}).comap
          hilbertSequenceLinear).topologicalClosure := by
  unfold hilbertLegalClosure hilbertLegalSubspace
  rw [legalSeedSpan_positive_eq_residue_span]

/-- Known mathematical strong Nyman--Beurling/Báez-Duarte input, without a
provider in this declaration. Defining the proposition does not prove it. -/
def PositiveResidueDensityFromRH : Prop :=
  RiemannHypothesis → hilbertLegalClosure {n : ℕ | 0 < n} = ⊤

/-- Conditional research reduction: the remaining classical density-from-RH
input is explicit. The new two-seed rigidity argument is fully discharged. -/
theorem riemannHypothesis_iff_twoSeed_closure_of_density_from_rh
    (hfull : PositiveResidueDensityFromRH) :
    RiemannHypothesis ↔ hilbertOne ∈ hilbertLegalClosure {2, 3} := by
  constructor
  · intro hRH
    rw [twoSeed_legalClosure_eq_top_of_full_density (hfull hRH)]
    trivial
  · exact riemannHypothesis_of_twoSeed_closure

/-- Conditional formalization of density of the entire original Hilbert
space, rather than only approximation of the constant. -/
theorem riemannHypothesis_iff_twoSeed_density_of_density_from_rh
    (hfull : PositiveResidueDensityFromRH) :
    RiemannHypothesis ↔ hilbertLegalClosure {2, 3} = ⊤ := by
  exact (riemannHypothesis_iff_twoSeed_closure_of_density_from_rh hfull).trans
    (hilbertLegalClosure_eq_top_iff_one_mem {2, 3}).symm

/-- Under RH and the stated classical density input, the two-seed and full
residue closures agree because both are the whole Hilbert space. This does
not assert equality of the two closed spaces when RH is false. -/
theorem twoSeed_closure_eq_full_of_rh_of_density_from_rh
    (hfull : PositiveResidueDensityFromRH)
    (hRH : RiemannHypothesis) :
    hilbertLegalClosure {2, 3} = hilbertLegalClosure {n : ℕ | 0 < n} := by
  rw [twoSeed_legalClosure_eq_top_of_full_density (hfull hRH), hfull hRH]

/-- The iff in the user's mean-one variance language, with all positive
integer dilations and the complete infinite Pareto variance retained. -/
theorem riemannHypothesis_iff_twoSeed_meanOne_sequence_of_density_from_rh
    (hfull : PositiveResidueDensityFromRH) :
    RiemannHypothesis ↔
      ∃ F : ℕ → ℕ → ℝ,
        (∀ j, F j ∈ legalSeedSpan ({2, 3} : Set ℕ)) ∧
        (∀ j, paretoMean (F j) = 1) ∧
        Tendsto (fun j => paretoVariance (F j)) atTop (𝓝 0) := by
  have hpos : ∀ a ∈ ({2, 3} : Set ℕ), 0 < a := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl <;> norm_num
  exact (riemannHypothesis_iff_twoSeed_closure_of_density_from_rh hfull).trans
    (hilbertOne_mem_legalClosure_iff_meanOne_variance_sequence {2, 3} hpos)

end
end RiemannResearch.RH.Pareto
