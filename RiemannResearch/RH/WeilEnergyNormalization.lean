import RiemannResearch.RH.WeilExtension
import RiemannResearch.RH.WeilCorrelationAdmissibility

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Exact gamma displacement normalization of the infinite arithmetic form

Source: the user-provided Nyman--Weil note, section 2, and Suzuki,
https://arxiv.org/html/2606.09096v1, section 1.1.

The gamma regulator is converted to its displacement expression using the
proved integral `log 2 + pi / 2`. All pole, arithmetic, and diagonal terms
remain present. This is an arithmetic identity, not a zero-side explicit formula.
-/

open MeasureTheory Set Filter

namespace RiemannResearch.RH.SignedWeilCorrelation

noncomputable section

theorem integrable_weilGammaKernel_regulator :
    Integrable (fun t => weilGammaKernel t * (1 - weilRegulator t))
      positiveMeasure := by
  apply (integrable_archimedeanCorrection.const_mul (1 / 2 : ℝ)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [archimedeanCorrection_eq_kernel (show 0 < t from ht)]
  ring

theorem integral_weilGammaKernel_regulator :
    (∫ t, weilGammaKernel t * (1 - weilRegulator t) ∂positiveMeasure) =
      (Real.log 2 + Real.pi / 2) / 2 := by
  have h := integral_weilGammaKernel_regulator_correction
  have he : (fun t => 2 * weilGammaKernel t * (1 - weilRegulator t)) =
      fun t => 2 * (weilGammaKernel t * (1 - weilRegulator t)) := by
    funext t
    ring
  rw [he, integral_const_mul] at h
  change 2 * (∫ t, weilGammaKernel t * (1 - weilRegulator t) ∂positiveMeasure) =
    Real.log 2 + Real.pi / 2 at h
  linarith

/-- The exact regulated gamma integral, with its convergent displacement
integral and evaluated diagonal correction. -/
theorem integral_weilGammaKernel_regulated_eq_displacement
    (C : ℝ → ℝ) (hCc : Continuous C) (K : ℝ) (hK : 0 ≤ K)
    (hLip : ∀ t, 0 < t → |C t - C 0| ≤ K * t) :
    (∫ t, weilGammaKernel t * (C t - weilRegulator t * C 0) ∂positiveMeasure) =
      -(∫ t, weilGammaKernel t * (C 0 - C t) ∂positiveMeasure) +
        C 0 * ((Real.log 2 + Real.pi / 2) / 2) := by
  have hi := integrable_weilGammaKernel_sub_zero C hCc K hK hLip
  have hj := integrable_weilGammaKernel_regulator.const_mul (C 0)
  have he : (fun t => weilGammaKernel t * (C t - weilRegulator t * C 0)) =
      (fun t => weilGammaKernel t * (C t - C 0) +
        C 0 * (weilGammaKernel t * (1 - weilRegulator t))) := by
    funext t
    ring
  rw [he]
  rw [integral_add hi hj, integral_const_mul, integral_weilGammaKernel_regulator]
  have hn : (fun t => weilGammaKernel t * (C t - C 0)) =
      fun t => -(weilGammaKernel t * (C 0 - C t)) := by
    funext t
    ring
  rw [hn, integral_neg]

/-- Exact infinite arithmetic energy expression. In particular, the checked
diagonal displacement adds `log 2 + pi / 2` to the original constant. -/
theorem infinitePrimePowerCorrelationValue_eq_energy
    (c : ℝ) (C : ℝ → ℝ) (hCc : Continuous C) (K : ℝ) (hK : 0 ≤ K)
    (hLip : ∀ t, 0 < t → |C t - C 0| ≤ K * t) :
    infinitePrimePowerCorrelationValue c C =
      2 * (∫ t, weilPoleKernel t * C t ∂positiveMeasure) -
        2 * (∑' n : ℕ, primePowerWeight n * C (Real.log n)) -
        (c + Real.log 2 + Real.pi / 2) * C 0 +
        2 * (∫ t, weilGammaKernel t * (C 0 - C t) ∂positiveMeasure) := by
  unfold infinitePrimePowerCorrelationValue
  rw [integral_weilGammaKernel_regulated_eq_displacement C hCc K hK hLip]
  ring

open RiemannResearch.Analysis

/-- The normalization applies to actual correlations of smooth
superexponential tests; its gamma integrability is discharged. -/
theorem infinitePrimePowerCorrelationValue_realAutocorrelation_eq_energy
    (c : ℝ) {f : ℝ → ℂ}
    (hf : SuperexponentialDecay f) (hdf : SuperexponentialDecay (deriv f))
    (hfd : Differentiable ℝ f) :
    infinitePrimePowerCorrelationValue c (realAutocorrelation f) =
      2 * (∫ t, weilPoleKernel t * realAutocorrelation f t ∂positiveMeasure) -
        2 * (∑' n : ℕ, primePowerWeight n * realAutocorrelation f (Real.log n)) -
        (c + Real.log 2 + Real.pi / 2) * realAutocorrelation f 0 +
        2 * (∫ t, weilGammaKernel t *
          (realAutocorrelation f 0 - realAutocorrelation f t) ∂positiveMeasure) := by
  obtain ⟨K, hK⟩ := hf.exists_crossCorrelation_lipschitz hf hdf hfd hfd.continuous
  have hcorr (t : ℝ) : (crossCorrelation f f t).re = realAutocorrelation f t := by rfl
  have hCc : Continuous (realAutocorrelation f) :=
    Complex.continuous_re.comp hK.continuous
  apply infinitePrimePowerCorrelationValue_eq_energy c _ hCc K K.coe_nonneg
  intro t ht
  have hreal : |realAutocorrelation f t - realAutocorrelation f 0| ≤
      ‖crossCorrelation f f t - crossCorrelation f f 0‖ := by
    simpa only [Complex.sub_re, hcorr] using
      Complex.abs_re_le_norm (crossCorrelation f f t - crossCorrelation f f 0)
  exact hreal.trans (by
    simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_pos ht] using hK.dist_le_mul t 0)

end
end RiemannResearch.RH.SignedWeilCorrelation
