import RiemannResearch.RH.WeilSpectralPairing
import RiemannResearch.RH.RiemannHypothesisStrip

/-!
# Positivity of the actual arithmetic Weil diagonal under RH

Source: user-provided layer-cake continuation, sections 21, 25, and 38.
The arithmetic-to-zero-side adapter is already proved in WeilSpectralPairing;
it is not a new premise here. RH is an explicit hypothesis, not a conclusion.
The test class is exactly SmoothSuperexponentialDecay, not the piecewise
linear hat class. Extension to hats requires its own analytic argument.
-/

open MeasureTheory
open MeasureTheory.BilateralLaplace
open RiemannResearch.Analysis
open scoped ComplexConjugate

namespace RiemannResearch.RH.SignedWeilCorrelation

theorem arithmeticWeilPairing_self_re_nonneg_of_RH
    (hRH : RiemannHypothesis) {f : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) :
    0 ≤ (arithmeticWeilPairing f f).re := by
  rw [arithmeticWeilPairing_eq_zero_sum hf hf]
  have hs := (summable_norm_arithmeticWeilPairing_zero_terms hf hf).of_norm
  rw [show (∑' ρ : Zeta23.zetaZeroConfig.carrier,
      (Zeta23.zeroMult ρ : ℂ) * conj (centeredTransform f (1 - conj (ρ : ℂ))) *
        centeredTransform f (ρ : ℂ)).re =
      ∑' ρ : Zeta23.zetaZeroConfig.carrier,
        ((Zeta23.zeroMult ρ : ℂ) * conj (centeredTransform f (1 - conj (ρ : ℂ))) *
          centeredTransform f (ρ : ℂ)).re from Complex.reCLM.map_tsum hs]
  apply tsum_nonneg
  intro ρ
  have hline : (ρ : ℂ).re = 1 / 2 :=
    (riemannHypothesis_iff_strip_zeros_on_line.mp hRH) ρ
      ρ.property.1 ρ.property.2.1 ρ.property.2.2
  have hfix : 1 - conj (ρ : ℂ) = (ρ : ℂ) := by
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
      linarith
    · simp
  rw [hfix]
  have heq (z : ℂ) : ((Zeta23.zeroMult ρ : ℂ) * conj z * z).re =
      (Zeta23.zeroMult ρ : ℝ) * Complex.normSq z := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.natCast_re,
      Complex.natCast_im, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
    ring
  rw [heq]
  exact mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)

/-- The actual completed arithmetic form, with its pole and prime terms,
is nonnegative under RH on the already-supported smooth test class. -/
theorem infinitePrimePowerCorrelationValue_nonneg_of_RH
    (hRH : RiemannHypothesis) {f : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) :
    0 ≤ infinitePrimePowerCorrelationValue
      (Real.eulerMascheroniConstant + Real.log (4 * Real.pi))
      (realAutocorrelation f) := by
  have heq := congrArg Complex.re (arithmeticWeilPairing_self_eq hf)
  simp only [Complex.ofReal_re] at heq
  rw [← heq]
  exact arithmeticWeilPairing_self_re_nonneg_of_RH hRH hf

end RiemannResearch.RH.SignedWeilCorrelation
