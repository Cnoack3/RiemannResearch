import RiemannResearch.Analysis.MellinLogStepContinuity
import RiemannResearch.RH.ThresholdHilbertSpace

/-!
# The actual Pareto Hilbert space has no nonzero continuous log profile

Source: user-provided Hilbert--Pólya discussion, September 20, 2026.
The mathematical content is the jump obstruction, including arbitrary
changes on null sets. `FourierFirstMomentContinuity` proves the Fourier
regularity bridge, and `ParetoMellinLogFourierDomain` assembles the actual
frequency-domain obstruction. No claim about a completed self-adjoint
Hilbert--Pólya operator is made here.
-/

noncomputable section

open MeasureTheory
open RiemannResearch.Analysis.MellinLogStep

namespace RiemannResearch.RH.Pareto

/-- The real inverse-Fourier profile of a Pareto Hilbert vector in logarithmic
coordinates, with its physical integer sequence and its zero extension. -/
def paretoMellinLogProfile (f : ThresholdHilbert) : ℝ → ℝ :=
  mellinLogProfile (hilbertSequence f)

@[simp] theorem paretoMellinLogProfile_zero :
    paretoMellinLogProfile (0 : ThresholdHilbert) = 0 := by
  have hs : hilbertSequence (0 : ThresholdHilbert) = 0 :=
    map_zero hilbertSequenceLinear
  simp [paretoMellinLogProfile, hs]

/-- Every continuous a.e. representative of an actual Pareto log profile
forces the underlying Hilbert vector to vanish. -/
theorem eq_zero_of_continuous_ae_eq_paretoMellinLogProfile
    (f : ThresholdHilbert) (h : ℝ → ℝ) (hh : Continuous h)
    (heq : h =ᵐ[volume] paretoMellinLogProfile f) : f = 0 := by
  have hz : hilbertSequence f = 0 :=
    eq_zero_of_continuous_ae_eq_profile (hilbertSequence f)
      (hilbertSequence_zero f) h hh heq
  apply hilbertSequence_injective
  calc
    hilbertSequence f = 0 := hz
    _ = hilbertSequence (0 : ThresholdHilbert) := by
      funext n
      cases n <;> simp [hilbertSequence]

theorem exists_continuous_ae_eq_paretoMellinLogProfile_iff (f : ThresholdHilbert) :
    (∃ h : ℝ → ℝ, Continuous h ∧ h =ᵐ[volume] paretoMellinLogProfile f) ↔
      f = 0 := by
  constructor
  · rintro ⟨h, hh, heq⟩
    exact eq_zero_of_continuous_ae_eq_paretoMellinLogProfile f h hh heq
  · intro hf
    subst f
    refine ⟨fun _ => 0, continuous_const, ?_⟩
    simp only [paretoMellinLogProfile_zero]
    exact Filter.EventuallyEq.rfl

/-- Even the pointwise profile itself is continuous only for the zero vector. -/
theorem continuous_paretoMellinLogProfile_iff (f : ThresholdHilbert) :
    Continuous (paretoMellinLogProfile f) ↔ f = 0 := by
  constructor
  · intro hh
    exact eq_zero_of_continuous_ae_eq_paretoMellinLogProfile f
      (paretoMellinLogProfile f) hh Filter.EventuallyEq.rfl
  · intro hf
    subst f
    rw [paretoMellinLogProfile_zero]
    exact continuous_const

end RiemannResearch.RH.Pareto
