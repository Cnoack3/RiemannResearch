import RiemannResearch.RH.ExactHeadOccurrenceDispersion
import RiemannResearch.RH.ExactHeadGreenClosure
import RiemannResearch.RH.ExactHeadFloorExtension
import RiemannResearch.RH.MobiusHeadGreenNormal

/-!
# Cofinal bounded occurrence/reuse criteria for RH

Source: Christian Noack, `sdf_modified.pdf`, sections 14.9--14.14.
The repository's bounded exact-head closure theorem improves the sufficient
analytic target: cofinal boundedness suffices; vanishing at every cutoff is
not required. The cofinal bounds remain unresolved domain-specific premises.
This module supplies no unconditional proof of RH.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection
open RiemannResearch.Analysis.FiniteProfileEnergy
open RiemannResearch.RH.ExactHeadGcdAtoms
open ExactHeadAtomOptimizer MobiusHeadGreen FloorProfileExtension

/-- Uniformly bounded actual atom energy on cofinal cutoffs suffices. -/
theorem riemannHypothesis_of_cofinal_bounded_atomEnergy (B : ℝ)
    (hdata : ∀ J : ℕ, ∃ x, J ≤ x ∧ atomEnergy (greenPeriod x) x ≤ B) :
    RiemannHypothesis := by
  have hPpos (x : ℕ) : 0 < greenPeriod x :=
    lt_of_le_of_lt (Nat.zero_le x) (greenPeriod_gt x)
  let hd := fun x d (hd : d ∈ Finset.Icc 1 (greenPeriod x)) => (Finset.mem_Icc.mp hd).1
  let f (x : ℕ) := hilbertExtension (greenPeriod x) (hPpos x)
    (Finset.Icc 1 (greenPeriod x)) (primorialNormalCoefficients x) (hd x)
  choose n hn he using hdata
  refine riemannHypothesis_of_bounded_exact_head_residuals (Set.Ici 1)
    (by intro a ha; exact ha) (fun J => f (n J))
    (fun J => hilbertExtension_legal _ _ _ _ _) ?_ (1 + B) ?_
  · intro J k hk hkJ
    apply hilbertExtension_head (greenPeriod (n J)) (hPpos (n J)) _
      (primorialNormalCoefficients (n J)) _ (n J) (greenPeriod_gt (n J))
      (mobius_floor_head (greenPeriod (n J)) (n J) (greenPeriod_gt (n J)).le
        (primorialNormalCoefficients (n J)) (primorialNormalCoefficients_spec (n J)).1)
    · exact hk
    · exact hkJ.trans (hn J)
  · intro J
    let x := n J
    have hterm : progressionWeight (greenPeriod x) (greenPeriod x) ≤ 1 := by
      have hh := Finset.single_le_sum (s := Finset.Icc 1 (greenPeriod x))
        (f := progressionWeight (greenPeriod x)) (fun r _ => progressionWeight_nonneg _ r)
        (Finset.mem_Icc.mpr ⟨hPpos x, le_rfl⟩)
      simpa [ExactHeadGreen.period_mass (greenPeriod x) (hPpos x)] using hh
    change ‖hilbertOne - hilbertExtension (greenPeriod x) (hPpos x) _
      (primorialNormalCoefficients x) _‖ ^ 2 ≤ _
    rw [actual_energy_split (greenPeriod x) (hPpos x) (primorialNormalCoefficients x)
      (primorialNormalCoefficients_spec x).2.1, primorial_q_eq_atomEnergy]
    exact add_le_add hterm (he J)

/-- The occurrence and reuse bounds must hold at the same cofinal stages. -/
theorem riemannHypothesis_of_cofinal_bounded_occurrence_reuse (B : ℝ)
    (hdata : ∀ J : ℕ, ∃ x, J ≤ x ∧
      occurrenceEnergy (greenPeriod x) x + reuseEnergy (greenPeriod x) x ≤ B) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_bounded_atomEnergy B
  simpa only [atomEnergy_eq_occurrence_add_reuse] using hdata

/-- An explicit sufficient return-statistic target, weaker than requiring
the occurrence and pooled dispersion errors to tend to zero. -/
theorem riemannHypothesis_of_cofinal_bounded_returnDispersion (B : ℝ)
    (hdata : ∀ J : ℕ, ∃ x, J ≤ x ∧
      occurrenceEnergy (greenPeriod x) x + 5 * returnDispersion (greenPeriod x) x ≤ B) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_bounded_atomEnergy B
  intro J
  obtain ⟨x,hx,he⟩ := hdata J
  refine ⟨x,hx,?_⟩
  exact (atomEnergy_le_occurrence_add_dispersion (greenPeriod x) x
    (lt_of_le_of_lt (Nat.zero_le x) (greenPeriod_gt x))).trans he

/-- A signed Green trial can bypass the stronger, often very lossy, coefficient
dispersion estimate. The atom vector may depend on the stage. -/
theorem riemannHypothesis_of_cofinal_bounded_green_trial (B : ℝ)
    (u : ℕ → ℕ → ℝ)
    (hdata : ∀ J : ℕ, ∃ x, J ≤ x ∧
      occurrenceEnergy (greenPeriod x) x +
        energy (Finset.Icc 1 (greenPeriod x - 1)) (progressionWeight (greenPeriod x))
          (fit (greenPeriod x) x (occurrenceCoefficients (greenPeriod x) x) -
            synthesis (greenPeriod x) (upperDivisors (greenPeriod x) x) (u x)) ≤ B) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_bounded_occurrence_reuse B
  intro J
  obtain ⟨x,hx,he⟩ := hdata J
  exact ⟨x,hx,(add_le_add le_rfl (reuseEnergy_le_trial (greenPeriod x) x (u x))).trans he⟩

end RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection
