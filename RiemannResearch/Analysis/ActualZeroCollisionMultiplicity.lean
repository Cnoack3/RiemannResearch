import RiemannResearch.Analysis.OccurrenceCollisionMultiplicity
import RiemannResearch.Analysis.ActualZeroCollisionCertificate

/-!
# Exact ordinate multiplicity identities for actual zeta-zero occurrences

The multiplicity at an ordinate aggregates all zero copies sharing it, including
distinct horizontal locations. It is therefore different from the analytic
multiplicity of one zero. Reflection, simplicity and RH are not assumed.
-/

noncomputable section
open scoped BigOperators
open Zeta23

namespace RiemannResearch.Analysis.ActualZeroCollisionCertificate

open ActualZeroOrdinate OrdinateCollisionCertificate

def actualOrdinateSupport (T : ℝ) : Finset ℝ := ordinateSupport (copyOrdinate T)

def actualOrdinateMultiplicity (T τ : ℝ) : ℕ := ordinateMultiplicity (copyOrdinate T) τ

/-- Ordered same-ordinate pairs of actual zero occurrences, including the diagonal. -/
def actualCollision (T : ℝ) : ℕ := occurrenceCollision (copyOrdinate T)

theorem actualCount_eq_sum_ordinateMultiplicity (T : ℝ) :
    Ncount 0 T = ∑ τ ∈ actualOrdinateSupport T, actualOrdinateMultiplicity T τ := by
  simpa only [actualOrdinateSupport, actualOrdinateMultiplicity, card_copies] using
    card_eq_sum_ordinateMultiplicity (copyOrdinate T)

/-- The collision count is the exact sum of squared total ordinate multiplicities. -/
theorem actualCollision_eq_sum_multiplicity_sq (T : ℝ) :
    actualCollision T = ∑ τ ∈ actualOrdinateSupport T, (actualOrdinateMultiplicity T τ) ^ 2 :=
  occurrenceCollision_eq_sum_multiplicity_sq (copyOrdinate T)

theorem actualCollision_eq_count_add_excess (T : ℝ) :
    actualCollision T = Ncount 0 T +
      ∑ τ ∈ actualOrdinateSupport T,
        actualOrdinateMultiplicity T τ * (actualOrdinateMultiplicity T τ - 1) := by
  have h := occurrenceCollision_eq_card_add_excess (copyOrdinate T)
  rw [occurrenceExcess_eq_multiplicityExcess] at h
  simpa only [actualCollision, actualOrdinateSupport, actualOrdinateMultiplicity,
    multiplicityExcess, card_copies] using h

/-- The actual collision excess is a nonnegative even integer at every finite cutoff. -/
theorem actualCollision_sub_count_even (T : ℝ) :
    Even (actualCollision T - Ncount 0 T) := by
  simpa only [actualCollision, card_copies] using
    occurrenceCollision_sub_card_even (copyOrdinate T)

/-- Exact equality excludes both horizontal pairs and analytic multiplicity. -/
theorem actualCollision_eq_count_iff (T : ℝ) :
    actualCollision T = Ncount 0 T ↔
      ∀ ρ ∈ cutoff T, ρ.re = 1 / 2 ∧ zeroMult ρ = 1 := by
  classical
  constructor
  · intro heq
    apply (copyOrdinate_injective_iff T).mp
    have hc := occurrenceCollision_eq_card_add_excess (copyOrdinate T)
    have heq' : occurrenceCollision (copyOrdinate T) = Fintype.card (Copies T) := by
      simpa only [actualCollision, card_copies] using heq
    have hexcess : occurrenceExcess (copyOrdinate T) = 0 := by omega
    intro c d hcd
    by_contra hne
    have htwo := two_le_occurrenceExcess (copyOrdinate T) hne hcd
    omega
  · intro hall
    have hinj := (copyOrdinate_injective_iff T).mpr hall
    have heq : ∀ c d : Copies T, copyOrdinate T c = copyOrdinate T d ↔ c = d :=
      fun c d => ⟨fun h => hinj h, fun h => congrArg (copyOrdinate T) h⟩
    have hc : occurrenceCollision (copyOrdinate T) = Fintype.card (Copies T) := by
      unfold occurrenceCollision
      simp_rw [heq]
      simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
        if_true, Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_id,
        Finset.card_univ]
    exact hc.trans (card_copies T)

end RiemannResearch.Analysis.ActualZeroCollisionCertificate
