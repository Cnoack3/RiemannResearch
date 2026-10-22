import RiemannResearch.Analysis.OrdinateCollisionCertificate
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Exact aggregation of occurrence collisions by ordinate multiplicity

The support is the image of the finite occurrence family. Multiplicity at an
ordinate is the cardinality of its fibre, so repeated analytic occurrences and
distinct zeros with the same ordinate are both retained. The exact identities
are `N = ∑ M(τ)` and `C = ∑ M(τ)^2`; their excess is a nonnegative even integer.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.OrdinateCollisionCertificate

variable {ι : Type*} [Fintype ι]

def ordinateSupport (frequency : ι → ℝ) : Finset ℝ := by
  classical
  exact Finset.univ.image frequency

def ordinateMultiplicity (frequency : ι → ℝ) (τ : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => frequency i = τ)).card

theorem card_eq_sum_ordinateMultiplicity (frequency : ι → ℝ) :
    Fintype.card ι = ∑ τ ∈ ordinateSupport frequency, ordinateMultiplicity frequency τ := by
  classical
  simpa only [ordinateSupport, ordinateMultiplicity, Finset.card_univ] using
    Finset.card_eq_sum_card_image frequency (Finset.univ : Finset ι)

theorem collision_row_eq_ordinateMultiplicity (frequency : ι → ℝ) (i : ι) :
    (∑ j, if frequency i = frequency j then (1 : ℕ) else 0) =
      ordinateMultiplicity frequency (frequency i) := by
  classical
  simp only [ordinateMultiplicity, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [eq_comm]

/-- Every ordered same-ordinate pair is retained in this exact fibre-square formula. -/
theorem occurrenceCollision_eq_sum_multiplicity_sq (frequency : ι → ℝ) :
    occurrenceCollision frequency =
      ∑ τ ∈ ordinateSupport frequency, (ordinateMultiplicity frequency τ) ^ 2 := by
  classical
  have hmaps : ∀ i ∈ (Finset.univ : Finset ι), frequency i ∈ ordinateSupport frequency := by
    intro i hi
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have hf := Finset.sum_fiberwise_of_maps_to'
    (s := (Finset.univ : Finset ι)) (t := ordinateSupport frequency) (g := frequency)
    hmaps (ordinateMultiplicity frequency)
  calc
    occurrenceCollision frequency = ∑ i, ordinateMultiplicity frequency (frequency i) := by
      unfold occurrenceCollision
      exact Finset.sum_congr rfl (fun i _ => collision_row_eq_ordinateMultiplicity frequency i)
    _ = ∑ τ ∈ ordinateSupport frequency, (ordinateMultiplicity frequency τ) ^ 2 := by
      simpa only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id,
        ordinateMultiplicity, pow_two] using hf.symm

theorem card_eq_multiplicityCount (frequency : ι → ℝ) :
    Fintype.card ι = multiplicityCount (ordinateSupport frequency) (ordinateMultiplicity frequency) :=
  card_eq_sum_ordinateMultiplicity frequency

theorem occurrenceCollision_eq_multiplicityCollision (frequency : ι → ℝ) :
    occurrenceCollision frequency =
      multiplicityCollision (ordinateSupport frequency) (ordinateMultiplicity frequency) :=
  occurrenceCollision_eq_sum_multiplicity_sq frequency

theorem occurrenceExcess_eq_multiplicityExcess (frequency : ι → ℝ) :
    occurrenceExcess frequency =
      multiplicityExcess (ordinateSupport frequency) (ordinateMultiplicity frequency) := by
  have hc := occurrenceCollision_eq_card_add_excess frequency
  have hm := multiplicityCollision_eq_count_add_excess
    (ordinateSupport frequency) (ordinateMultiplicity frequency)
  rw [← occurrenceCollision_eq_multiplicityCollision,
    ← card_eq_multiplicityCount] at hm
  omega

/-- Exact occurrence collision excess is even, including all repeated ordinates. -/
theorem occurrenceExcess_even (frequency : ι → ℝ) : Even (occurrenceExcess frequency) := by
  rw [occurrenceExcess_eq_multiplicityExcess]
  exact multiplicityExcess_even (ordinateSupport frequency) (ordinateMultiplicity frequency)

theorem occurrenceCollision_sub_card_even (frequency : ι → ℝ) :
    Even (occurrenceCollision frequency - Fintype.card ι) := by
  rw [occurrenceCollision_eq_card_add_excess, Nat.add_sub_cancel_left]
  exact occurrenceExcess_even frequency

end RiemannResearch.Analysis.OrdinateCollisionCertificate
