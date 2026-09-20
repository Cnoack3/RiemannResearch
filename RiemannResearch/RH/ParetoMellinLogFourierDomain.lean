import RiemannResearch.RH.ParetoMellinLogDomain
import RiemannResearch.RH.ParetoStepIsometry
import RiemannResearch.Analysis.MellinLogFrequencyDomain
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.Floor

/-!
# The actual Pareto Fourier--Mellin range avoids the frequency domain

Source: user-provided Hilbert--Pólya discussion, September 20, 2026.
This supplies the L2 provider for every vector of the actual Pareto Hilbert
space and specializes the complete jump/Fourier argument. No regularity
provider, RH hypothesis, or arithmetic approximation hypothesis is assumed.
-/

noncomputable section
open MeasureTheory Set FourierTransform
open RiemannResearch.Analysis.MellinLogStep

namespace RiemannResearch.RH.Pareto

def paretoMellinLogComplexProfile (f : ThresholdHilbert) : ℝ → ℂ :=
  mellinLogProfile (fun n => (hilbertSequence f n : ℂ))

private theorem complexProfile_indicator (f : ThresholdHilbert) :
    paretoMellinLogComplexProfile f = (Ici (0 : ℝ)).indicator
      (fun u => Real.exp (-u / 2) • (hilbertSequence f ⌊Real.exp u⌋₊ : ℂ)) := by
  funext u
  by_cases hu : 0 ≤ u <;>
    simp [paretoMellinLogComplexProfile, mellinLogProfile, logarithmicStep,
      Set.indicator, hu]

theorem paretoMellinLogComplexProfile_measurable (f : ThresholdHilbert) :
    Measurable (paretoMellinLogComplexProfile f) := by
  rw [complexProfile_indicator]
  have hseq : Measurable (fun u : ℝ => (hilbertSequence f ⌊Real.exp u⌋₊ : ℂ)) :=
    Complex.measurable_ofReal.comp
      ((measurable_of_countable (hilbertSequence f)).comp
        (Nat.measurable_floor.comp Real.measurable_exp))
  apply Measurable.indicator _ measurableSet_Ici
  exact (Real.measurable_exp.comp (measurable_id.neg.div_const 2)).smul hseq

private theorem complexProfile_norm_sq (f : ThresholdHilbert) :
    (fun u => ‖paretoMellinLogComplexProfile f u‖ ^ 2) =
      (Ici (0 : ℝ)).indicator
        (fun u => hilbertSequence f ⌊Real.exp u⌋₊ ^ 2 * Real.exp (-u)) := by
  funext u
  by_cases hu : 0 ≤ u
  · have hs : Real.exp (-u / 2) ^ 2 = Real.exp (-u) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [Set.indicator_of_mem (show u ∈ Ici (0 : ℝ) from hu)]
    simp only [paretoMellinLogComplexProfile, mellinLogProfile, logarithmicStep,
      if_pos hu, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Complex.norm_real, mul_pow, sq_abs, hs]
    ring
  · simp [paretoMellinLogComplexProfile, mellinLogProfile, logarithmicStep,
      Set.indicator, hu]

/-- The whole Pareto Hilbert space has square-integrable logarithmic profiles. -/
theorem paretoMellinLogComplexProfile_memLp (f : ThresholdHilbert) :
    MemLp (paretoMellinLogComplexProfile f) 2 := by
  apply (memLp_two_iff_integrable_sq_norm
    (paretoMellinLogComplexProfile_measurable f).aestronglyMeasurable).mpr
  rw [complexProfile_norm_sq]
  apply (integrable_indicator_iff measurableSet_Ici).mpr
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  have hstep := paretoStepEnergy_integrable (hilbertSequence f)
    (hilbertSequence_square_summable f)
  have hchange := (integrableOn_comp_exp_Ioi
    (fun x : ℝ => hilbertSequence f ⌊x⌋₊ ^ 2 / x ^ 2) 0).mpr
    (by simpa only [Real.exp_zero] using hstep)
  have heq : (fun u : ℝ => Real.exp u •
      (hilbertSequence f ⌊Real.exp u⌋₊ ^ 2 / Real.exp u ^ 2)) =
      (fun u => hilbertSequence f ⌊Real.exp u⌋₊ ^ 2 * Real.exp (-u)) := by
    funext u
    rw [smul_eq_mul, Real.exp_neg]
    field_simp [Real.exp_ne_zero]
  rw [heq] at hchange
  exact hchange

/-- The unitary L2 Fourier representative of an actual Pareto vector.
Frequency normalization differs from the critical-line parameter by `2π`. -/
def paretoMellinLogFourier (f : ThresholdHilbert) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  𝓕 ((paretoMellinLogComplexProfile_memLp f).toLp (paretoMellinLogComplexProfile f))

/-- The literal multiplication-by-frequency domain intersects the actual
Pareto Mellin image only at zero. -/
theorem eq_zero_of_paretoMellinLogFourier_frequency_memLp (f : ThresholdHilbert)
    (hFreq : MemLp (fun t : ℝ => (t : ℂ) * paretoMellinLogFourier f t) 2) :
    f = 0 := by
  have hc : (fun n => (hilbertSequence f n : ℂ)) = 0 :=
    eq_zero_of_profile_frequency_memLp (fun n => (hilbertSequence f n : ℂ))
      (by simp) (paretoMellinLogComplexProfile_memLp f) hFreq
  apply hilbertSequence_injective
  have hs0 : hilbertSequence (0 : ThresholdHilbert) = 0 :=
    map_zero hilbertSequenceLinear
  rw [hs0]
  funext n
  exact Complex.ofReal_eq_zero.mp (congrFun hc n)

end RiemannResearch.RH.Pareto
