import RiemannResearch.Analysis.OccurrenceCollisionMultiplicity

/-!
# Exact energy aggregation over distinct ordinate locations

The occurrence kernel sum equals the double sum over the finite ordinate
support, weighted by the product of the two fibre multiplicities. Thus the
ranked multiplicity formulation of the sharp remainder uses the same energy
as the occurrence formulation.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.OrdinateCollisionCertificate

variable {ι : Type*} [Fintype ι]

theorem sum_occurrences_eq_sum_multiplicity (frequency : ι → ℝ) (f : ℝ → ℝ) :
    (∑ i, f (frequency i)) =
      ∑ τ ∈ ordinateSupport frequency, (ordinateMultiplicity frequency τ : ℝ) * f τ := by
  classical
  have hmaps : ∀ i ∈ (Finset.univ : Finset ι), frequency i ∈ ordinateSupport frequency := by
    intro i hi
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have hf := Finset.sum_fiberwise_of_maps_to'
    (s := (Finset.univ : Finset ι)) (t := ordinateSupport frequency) (g := frequency)
    hmaps f
  simpa only [Finset.sum_const, nsmul_eq_mul, ordinateMultiplicity] using hf.symm

theorem kernelEnergy_eq_sum_multiplicity_product (frequency : ι → ℝ) (K : ℝ → ℝ) :
    kernelEnergy frequency K =
      ∑ τ ∈ ordinateSupport frequency, ∑ σ ∈ ordinateSupport frequency,
        (ordinateMultiplicity frequency τ : ℝ) *
          (ordinateMultiplicity frequency σ : ℝ) * K (τ - σ) := by
  classical
  unfold kernelEnergy
  calc
    (∑ i, ∑ j, K (frequency i - frequency j)) =
        ∑ i, ∑ σ ∈ ordinateSupport frequency,
          (ordinateMultiplicity frequency σ : ℝ) * K (frequency i - σ) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact sum_occurrences_eq_sum_multiplicity frequency (fun σ => K (frequency i - σ))
    _ = ∑ τ ∈ ordinateSupport frequency,
        (ordinateMultiplicity frequency τ : ℝ) *
          (∑ σ ∈ ordinateSupport frequency,
            (ordinateMultiplicity frequency σ : ℝ) * K (τ - σ)) :=
      sum_occurrences_eq_sum_multiplicity frequency
        (fun τ => ∑ σ ∈ ordinateSupport frequency,
          (ordinateMultiplicity frequency σ : ℝ) * K (τ - σ))
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro τ hτ
      apply Finset.sum_congr rfl
      intro σ hσ
      ring

theorem sincEnergy_eq_sum_multiplicity_product (frequency : ι → ℝ) (R : ℝ) :
    sincEnergy frequency R =
      ∑ τ ∈ ordinateSupport frequency, ∑ σ ∈ ordinateSupport frequency,
        (ordinateMultiplicity frequency τ : ℝ) *
          (ordinateMultiplicity frequency σ : ℝ) * sincSquared R (τ - σ) :=
  kernelEnergy_eq_sum_multiplicity_product frequency (sincSquared R)

end RiemannResearch.Analysis.OrdinateCollisionCertificate
