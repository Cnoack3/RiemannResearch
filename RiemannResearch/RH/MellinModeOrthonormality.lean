import RiemannResearch.RH.ParetoMellinIsometry
import RiemannResearch.RH.MellinFrequencyRegularization
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Actual orthonormal Mellin features on the frequency line

Source: user-requested Mellin DPP construction, September 20, 2026.
The substitution calculation follows `ArithmeticPlancherelProof`; the
cross-inner-product result is supplied by `ParetoMellinIsometry`.
The features below are actual convergent Mellin integrals of residue
Gram--Schmidt modes. No orthonormality assumption is introduced.
-/

noncomputable section
open MeasureTheory Set FourierTransform
open RiemannResearch.Analysis.MellinLogStep

namespace RiemannResearch.RH.Pareto

theorem paretoMellinLogComplexProfile_integrable_of_bounded (f : ThresholdHilbert)
    {C : ℝ} (hC : ∀ k, |hilbertSequence f k| ≤ C) :
    Integrable (paretoMellinLogComplexProfile f) := by
  have he : paretoMellinLogComplexProfile f = (Ici (0 : ℝ)).indicator
      (fun u => (hilbertSequence f ⌊Real.exp u⌋₊ : ℂ) *
        (Real.exp (-u / 2) : ℂ)) := by
    funext u
    by_cases hu : 0 ≤ u <;>
      simp [paretoMellinLogComplexProfile, mellinLogProfile, logarithmicStep,
        Set.indicator, hu, Complex.real_smul, mul_comm]
  rw [he]
  apply (integrable_indicator_iff measurableSet_Ici).mpr
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  have hi : IntegrableOn (fun u : ℝ => Real.exp (-u / 2)) (Ioi 0) := by
    convert! integrableOn_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) 0 using 1
    funext u
    congr 1
    ring
  have hm : Measurable (fun u : ℝ => (hilbertSequence f ⌊Real.exp u⌋₊ : ℂ) *
      (Real.exp (-u / 2) : ℂ)) := by
    exact (Complex.continuous_ofReal.measurable.comp
      ((measurable_of_countable (hilbertSequence f)).comp
        (Nat.measurable_floor.comp Real.measurable_exp))).mul
      (Complex.continuous_ofReal.measurable.comp
        (Real.measurable_exp.comp (measurable_id.neg.div_const 2)))
  apply (hi.const_mul C).mono' hm.aestronglyMeasurable
  filter_upwards [] with u
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right (hC _) (Real.exp_nonneg _)

private theorem logarithmic_mellin_factor (u ξ : ℝ) :
    (Real.exp u : ℂ) * (Real.exp u : ℂ) ^
        (-MellinFrequency.criticalPoint (2 * Real.pi * ξ) - 1) =
      Complex.exp (((-2 * Real.pi * u * ξ : ℝ) : ℂ) * Complex.I) *
        (Real.exp (-u / 2) : ℂ) := by
  rw [Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero u)),
    ← Complex.ofReal_log (Real.exp_nonneg u), Real.log_exp,
    Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  unfold MellinFrequency.criticalPoint
  push_cast
  ring

/-- The actual ordinary Fourier integral equals the Mellin integral, with the
exact angular-frequency change `t = 2πξ`. -/
theorem paretoMellinLogComplexProfile_fourier (f : ThresholdHilbert) (ξ : ℝ) :
    𝓕 (paretoMellinLogComplexProfile f) ξ =
      paretoMellin f (MellinFrequency.criticalPoint (2 * Real.pi * ξ)) := by
  rw [Real.fourier_real_eq_integral_exp_smul, paretoMellin_eq_step_integral]
  calc
    _ = ∫ u in Ici (0 : ℝ),
        Complex.exp (((-2 * Real.pi * u * ξ : ℝ) : ℂ) * Complex.I) •
          paretoMellinLogComplexProfile f u := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro u hu
      have hu' : ¬ 0 ≤ u := hu
      simp [paretoMellinLogComplexProfile, mellinLogProfile, logarithmicStep, hu']
    _ = ∫ u in Ioi (0 : ℝ),
        Complex.exp (((-2 * Real.pi * u * ξ : ℝ) : ℂ) * Complex.I) •
          paretoMellinLogComplexProfile f u := integral_Ici_eq_integral_Ioi
    _ = ∫ u in Ioi (0 : ℝ), Real.exp u •
        ((hilbertSequence f ⌊Real.exp u⌋₊ : ℂ) *
          (Real.exp u : ℂ) ^
            (-MellinFrequency.criticalPoint (2 * Real.pi * ξ) - 1)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      have hu0 : 0 < u := hu
      simp only [paretoMellinLogComplexProfile, mellinLogProfile,
        logarithmicStep, if_pos hu0.le, smul_eq_mul, Complex.real_smul]
      have h := logarithmic_mellin_factor u ξ
      linear_combination -(hilbertSequence f ⌊Real.exp u⌋₊ : ℂ) * h
    _ = _ := by
      simpa only [Real.exp_zero] using integral_comp_exp_Ioi
        (fun x : ℝ => (hilbertSequence f ⌊x⌋₊ : ℂ) *
          (x : ℂ) ^ (-MellinFrequency.criticalPoint (2 * Real.pi * ξ) - 1)) 0

theorem paretoMellinLogFourier_ae_eq_of_bounded (f : ThresholdHilbert)
    {C : ℝ} (hC : ∀ k, |hilbertSequence f k| ≤ C) :
    (fun ξ => paretoMellinLogFourier f ξ) =ᵐ[volume]
      (fun ξ => paretoMellin f (MellinFrequency.criticalPoint (2 * Real.pi * ξ))) := by
  exact (RiemannResearch.Analysis.fourier_toLp_ae_eq_of_integrable
    (paretoMellinLogComplexProfile_integrable_of_bounded f hC)
    (paretoMellinLogComplexProfile_memLp f)).trans
      (Filter.Eventually.of_forall (paretoMellinLogComplexProfile_fourier f))

namespace MellinFrequency
open CoefficientStabilization

/-- A concrete Mellin feature, in ordinary Fourier coordinates. -/
def fourierModeFeature (j : ℕ) (ξ : ℝ) : ℂ :=
  modeFeature j (2 * Real.pi * ξ)

theorem fourierModeFeature_continuous (j : ℕ) : Continuous (fourierModeFeature j) :=
  (modeFeature_continuous j).comp (continuous_const.mul continuous_id)

theorem fourierModeFeature_ae (j : ℕ) :
    (fun ξ => paretoMellinLogFourier (residueMode j) ξ) =ᵐ[volume]
      fourierModeFeature j := by
  obtain ⟨C, hC⟩ := residueMode_sequence_bounded j
  exact paretoMellinLogFourier_ae_eq_of_bounded (residueMode j) hC

theorem fourierModeFeature_memLp (j : ℕ) : MemLp (fourierModeFeature j) 2 volume :=
  (memLp_congr_ae (fourierModeFeature_ae j)).mp
    (Lp.memLp (paretoMellinLogFourier (residueMode j)))

/-- The full cross-Gram identity for the actual Mellin features on the whole line. -/
theorem fourierModeFeature_gram (i j : ℕ) :
    (∫ ξ, star (fourierModeFeature i ξ) * fourierModeFeature j ξ) =
      if i = j then (1 : ℂ) else 0 := by
  calc
    _ = inner ℂ (paretoMellinLogFourier (residueMode i))
        (paretoMellinLogFourier (residueMode j)) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [fourierModeFeature_ae i, fourierModeFeature_ae j] with ξ hi hj
      rw [hi, hj]
      simp [RCLike.inner_apply, mul_comm]
    _ = (inner ℝ (residueMode i) (residueMode j) : ℂ) :=
      paretoMellinLogFourier_inner _ _
    _ = _ := by
      rw [(orthonormal_iff_ite.mp residueMode_orthonormal) i j]
      split_ifs <;> simp

/-- Actual transformed residue modes as vectors of complex L². -/
def mellinFourierMode (j : ℕ) : Lp ℂ 2 (volume : Measure ℝ) :=
  paretoMellinLogFourier (residueMode j)

theorem mellinFourierMode_orthonormal : Orthonormal ℂ mellinFourierMode := by
  rw [orthonormal_iff_ite]
  intro i j
  change inner ℂ (paretoMellinLogFourier (residueMode i))
    (paretoMellinLogFourier (residueMode j)) = _
  rw [paretoMellinLogFourier_inner,
    (orthonormal_iff_ite.mp residueMode_orthonormal) i j]
  split_ifs <;> simp

/-- The same Gram identity in angular-frequency notation, with the exact
Lebesgue density `1/(2π)`. -/
theorem modeFeature_angular_gram (i j : ℕ) :
    (1 / (2 * Real.pi) : ℝ) •
      (∫ t, star (modeFeature i t) * modeFeature j t) =
        if i = j then (1 : ℂ) else 0 := by
  have hs := Measure.integral_comp_mul_left
    (fun t => star (modeFeature i t) * modeFeature j t) (2 * Real.pi)
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  rw [abs_of_pos (inv_pos.mpr hpi)] at hs
  simpa only [fourierModeFeature, one_div] using hs.symm.trans (fourierModeFeature_gram i j)

end MellinFrequency
end RiemannResearch.RH.Pareto
