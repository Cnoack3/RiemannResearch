import RiemannResearch.RH.NymanPrimeSquareCompensation
import RiemannResearch.RH.NymanBroadFamily

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-! # Exact compensation for the specified normalized broad Nyman family -/

open MeasureTheory
open RiemannResearch.Analysis

namespace RiemannResearch.RH

theorem smoothSuperexponentialDecay_nymanNormalizedBroadTest_of_neZero
    (n : ℕ) [NeZero n] {φ : ℝ → ℝ} {a b R : ℝ}
    (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (ha : ∀ x < a, φ x = 0) (hb : ∀ x > b, φ x = 0) (hR : 0 < R) :
    SmoothSuperexponentialDecay (nymanNormalizedBroadTest n φ R) := by
  have hG := smoothSuperexponentialDecay_nymanFullReturn (contDiff_nymanBroadPotential hφ R)
    (nymanBroadPotential_zero_below ha hR) (nymanBroadPotential_zero_above hb hR) n
  exact hG.poleCancellationOperator.const_smul _

theorem infinitePrimePowerCorrelationValue_nymanNormalizedBroadTest_eq_zero
    (n : ℕ) [NeZero n] {φ : ℝ → ℝ} {a b R : ℝ}
    (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (ha : ∀ x < a, φ x = 0) (hb : ∀ x > b, φ x = 0) (hR : 0 < R) :
    SignedWeilCorrelation.infinitePrimePowerCorrelationValue
      (Real.eulerMascheroniConstant + Real.log (4 * Real.pi))
      (SignedWeilCorrelation.realAutocorrelation (nymanNormalizedBroadTest n φ R)) = 0 := by
  exact infinitePrimePowerCorrelationValue_smul_poleCancellation_nymanFullReturn_eq_zero n
    (contDiff_nymanBroadPotential hφ R) (nymanBroadPotential_zero_below ha hR)
    (nymanBroadPotential_zero_above hb hR) _

/-- Every prime, square, higher-power, and gamma contribution is retained for
the actual normalized broad test, before taking the large-window limit. -/
theorem primeCorrelationSector_nymanNormalizedBroadTest_compensation
    (n : ℕ) [NeZero n] {φ : ℝ → ℝ} {a b R : ℝ}
    (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (ha : ∀ x < a, φ x = 0) (hb : ∀ x > b, φ x = 0) (hR : 0 < R) :
    let C := SignedWeilCorrelation.realAutocorrelation (nymanNormalizedBroadTest n φ R)
    SignedWeilCorrelation.primeCorrelationSector C =
      -primeSquareSector C 1 +
      (Real.eulerMascheroniConstant + Real.log (4 * Real.pi) + Real.log 2 + Real.pi / 2 +
        SignedWeilCorrelation.higherPrimePowerDiagonal) * C 0 -
      SignedWeilCorrelation.higherPrimePowerDisplacementCorrection C -
      2 * (∫ t, SignedWeilCorrelation.weilGammaKernel t * (C 0 - C t)
        ∂SignedWeilCorrelation.positiveMeasure) := by
  exact primeCorrelationSector_smul_poleCancellation_nymanFullReturn_compensation n
    (contDiff_nymanBroadPotential hφ R) (nymanBroadPotential_zero_below ha hR)
    (nymanBroadPotential_zero_above hb hR) _

end RiemannResearch.RH
