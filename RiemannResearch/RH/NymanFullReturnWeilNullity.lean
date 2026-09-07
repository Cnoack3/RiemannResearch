import RiemannResearch.RH.NymanWeilNullity
import RiemannResearch.Analysis.BilateralLaplaceTranslation

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Full-return arithmetic nullity, including the actual normalization scalar

The general spectral-nullity implication below is applied immediately to
the actual arithmetic return. Its transform zeros are proved by the exact
conductor-zeta factorization, and all test-class providers are discharged.
-/

open MeasureTheory
open MeasureTheory.BilateralLaplace
open RiemannResearch.Analysis

namespace RiemannResearch.RH.SignedWeilCorrelation

theorem integral_weilPoleKernel_realAutocorrelation_eq_zero
    {f : ℝ → ℂ} (hf : SmoothSuperexponentialDecay f)
    (h0 : centeredTransform f 0 = 0) (h1 : centeredTransform f 1 = 0) :
    (∫ t, weilPoleKernel t * realAutocorrelation f t ∂positiveMeasure) = 0 := by
  have hC := smoothSuperexponentialDecay_realAutocorrelation hf
  have hc0 : centeredTransform (fun t => (realAutocorrelation f t : ℂ)) 0 = 0 := by
    exact realAutocorrelation_transform_zero hf.decay hf.deriv.decay
      (hf.1.differentiable (by simp)) 0 h0 (by simpa only [sub_zero] using h1)
  have hc1 : centeredTransform (fun t => (realAutocorrelation f t : ℂ)) 1 = 0 := by
    exact realAutocorrelation_transform_zero hf.decay hf.deriv.decay
      (hf.1.differentiable (by simp)) 1 h1 (by simpa only [sub_self] using h0)
  have ha : (1 / 2 : ℂ) - Complex.I * (Complex.I / 2) = 1 := by
    calc _ = (1 - Complex.I ^ 2) / 2 := by ring
         _ = 1 := by simp [Complex.I_sq]
  have hb : (1 / 2 : ℂ) - Complex.I * (-Complex.I / 2) = 0 := by
    calc _ = (1 + Complex.I ^ 2) / 2 := by ring
         _ = 0 := by simp [Complex.I_sq]
  have heven (t : ℝ) : ((realAutocorrelation f (-t) : ℂ)).re =
      ((realAutocorrelation f t : ℂ)).re := by
    simp only [Complex.ofReal_re, realAutocorrelation_neg]
  have hp := re_paperFT_pole_pair hC.decay hC.1.continuous heven
  simp only [WeilExplicitFormula.paperFT_eq_centeredTransform, ha, hb, hc0, hc1,
    add_zero, Complex.zero_re, Complex.ofReal_re] at hp
  linarith

theorem infinitePrimePowerCorrelationValue_eq_zero_of_transform_zeros
    {f : ℝ → ℂ} (hf : SmoothSuperexponentialDecay f)
    (hz : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      centeredTransform f s = 0) :
    infinitePrimePowerCorrelationValue
      (Real.eulerMascheroniConstant + Real.log (4 * Real.pi))
      (realAutocorrelation f) = 0 := by
  have hC := smoothSuperexponentialDecay_realAutocorrelation hf
  have hc (s : ℂ) (hs : riemannZeta s = 0) (h0 : 0 < s.re) (h1 : s.re < 1) :
      centeredTransform (fun t => (realAutocorrelation f t : ℂ)) s = 0 := by
    apply realAutocorrelation_transform_zero hf.decay hf.deriv.decay
      (hf.1.differentiable (by simp)) s (hz s hs h0 h1)
    apply hz (1 - s) (riemannZeta_one_sub_eq_zero_of_strip hs h0 h1)
    · simp only [Complex.sub_re, Complex.one_re]
      linarith
    · simp only [Complex.sub_re, Complex.one_re]
      linarith
  have hterm (ρ : Zeta23.zetaZeroConfig.carrier) :
      Zeta23.paperFT (fun t => (realAutocorrelation f t : ℂ)) (Zeta23.gammaOf ρ) = 0 := by
    have hρ : riemannZeta (ρ : ℂ) = 0 ∧ 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := ρ.property
    rw [WeilExplicitFormula.paperFT_gammaOf_eq_centeredTransform]
    apply hc (1 - (ρ : ℂ))
      (riemannZeta_one_sub_eq_zero_of_strip hρ.1 hρ.2.1 hρ.2.2)
    · simp only [Complex.sub_re, Complex.one_re]
      linarith [hρ.2.2]
    · simp only [Complex.sub_re, Complex.one_re]
      linarith [hρ.2.1]
  have heven (t : ℝ) : ((realAutocorrelation f (-t) : ℂ)).re =
      ((realAutocorrelation f t : ℂ)).re := by
    simp only [Complex.ofReal_re, realAutocorrelation_neg]
  have hEF := actual_noncompact_Weil_explicit_formula_of_smooth hC heven
  simpa only [hterm, mul_zero, tsum_zero, Complex.zero_re, Complex.ofReal_re] using hEF.symm

end RiemannResearch.RH.SignedWeilCorrelation

namespace RiemannResearch.RH

/-- Both actual pole moments vanish after any real scalar normalization. -/
theorem integral_weilPoleKernel_smul_poleCancellation_nymanFullReturn_eq_zero
    (n : ℕ) [NeZero n] {u : ℝ → ℂ} {a b : ℝ}
    (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (ha : ∀ x < a, u x = 0) (hb : ∀ x > b, u x = 0) (c : ℝ) :
    (∫ t, SignedWeilCorrelation.weilPoleKernel t *
      SignedWeilCorrelation.realAutocorrelation
        (c • poleCancellationOperator (nymanFullReturn n u)) t
      ∂SignedWeilCorrelation.positiveMeasure) = 0 := by
  have hG := (smoothSuperexponentialDecay_nymanFullReturn hu ha hb n).poleCancellationOperator
  have hp := centeredTransform_poleCancellation_nymanFullReturn_polar n hu ha hb
  apply SignedWeilCorrelation.integral_weilPoleKernel_realAutocorrelation_eq_zero (hG.const_smul c)
  · change centeredTransform
      (fun y => (c : ℂ) * poleCancellationOperator (nymanFullReturn n u) y) 0 = 0
    rw [centeredTransform_const_mul, hp.1, mul_zero]
  · change centeredTransform
      (fun y => (c : ℂ) * poleCancellationOperator (nymanFullReturn n u) y) 1 = 0
    rw [centeredTransform_const_mul, hp.2, mul_zero]

/-- The actual full-return channel has zero value for the complete arithmetic
Weil form, for every real normalization scalar. -/
theorem infinitePrimePowerCorrelationValue_smul_poleCancellation_nymanFullReturn_eq_zero
    (n : ℕ) [NeZero n] {u : ℝ → ℂ} {a b : ℝ}
    (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (ha : ∀ x < a, u x = 0) (hb : ∀ x > b, u x = 0) (c : ℝ) :
    SignedWeilCorrelation.infinitePrimePowerCorrelationValue
      (Real.eulerMascheroniConstant + Real.log (4 * Real.pi))
      (SignedWeilCorrelation.realAutocorrelation
        (c • poleCancellationOperator (nymanFullReturn n u))) = 0 := by
  have hG := (smoothSuperexponentialDecay_nymanFullReturn hu ha hb n).poleCancellationOperator
  apply SignedWeilCorrelation.infinitePrimePowerCorrelationValue_eq_zero_of_transform_zeros
    (hG.const_smul c)
  intro s hz h0 h1
  have hs : s ≠ 1 := by intro h; subst s; norm_num at h1
  change centeredTransform
    (fun y => (c : ℂ) * poleCancellationOperator (nymanFullReturn n u) y) s = 0
  rw [centeredTransform_const_mul,
    centeredTransform_poleCancellation_nymanFullReturn_zero n hu ha hb hs hz, mul_zero]

theorem infinitePrimePowerCorrelationValue_poleCancellation_nymanFullReturn_eq_zero
    (n : ℕ) [NeZero n] {u : ℝ → ℂ} {a b : ℝ}
    (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (ha : ∀ x < a, u x = 0) (hb : ∀ x > b, u x = 0) :
    SignedWeilCorrelation.infinitePrimePowerCorrelationValue
      (Real.eulerMascheroniConstant + Real.log (4 * Real.pi))
      (SignedWeilCorrelation.realAutocorrelation
        (poleCancellationOperator (nymanFullReturn n u))) = 0 := by
  simpa only [one_smul] using
    infinitePrimePowerCorrelationValue_smul_poleCancellation_nymanFullReturn_eq_zero n hu ha hb 1

end RiemannResearch.RH
