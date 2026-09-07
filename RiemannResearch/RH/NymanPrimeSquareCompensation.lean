import RiemannResearch.RH.NymanFullReturnWeilNullity
import RiemannResearch.RH.PrimePowerSectorDecomposition

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Complete prime--square compensation for the actual Nyman return

This is an identity of the actual infinite prime, square, and higher-power
series and the actual spatial gamma integral. Absolute summability, full
arithmetic Weil nullity, and polar nullity are supplied by proved providers.
The final theorem assumes only a compact smooth seed and a conductor.
-/

open MeasureTheory
open scoped BigOperators
open RiemannResearch.Analysis

namespace RiemannResearch.RH.SignedWeilCorrelation

/-- The prime sector uses precisely the exponent-one von Mangoldt terms. -/
noncomputable def primeCorrelationSector (C : ℝ → ℝ) : ℝ :=
  -2 * ∑' p : ℕ, if p.Prime then Real.log p / Real.sqrt p * C (Real.log p) else 0

/-- The complete third-and-higher-power diagonal constant. -/
noncomputable def higherPrimePowerDiagonal : ℝ :=
  2 * ∑' pj : ℕ × ℕ, PrimeCompensationLimits.higherPrimePowerWeight pj.1 pj.2

/-- Every higher-power displacement correction, including all primes and all
exponents at least three. -/
noncomputable def higherPrimePowerDisplacementCorrection (C : ℝ → ℝ) : ℝ :=
  2 * ∑' pj : ℕ × ℕ, PrimeCompensationLimits.higherPrimePowerWeight pj.1 pj.2 *
    (C 0 - C (PrimeCompensationLimits.higherPrimePowerDisplacement pj.1 pj.2))

theorem higherPrimePowerSector_eq_diagonal_add_displacement (C : ℝ → ℝ)
    (hC : Summable (fun n : ℕ => primePowerWeight n * C (Real.log n))) :
    (-2 * ∑' pj : ℕ × ℕ, PrimeCompensationLimits.higherPrimePowerWeight pj.1 pj.2 *
      C (PrimeCompensationLimits.higherPrimePowerDisplacement pj.1 pj.2)) =
    -higherPrimePowerDiagonal * C 0 + higherPrimePowerDisplacementCorrection C := by
  have hw := PrimeCompensationLimits.summable_higherPrimePowerWeight.mul_right (C 0)
  have hc := PrimeCompensationLimits.summable_higherPrimePowerTerm_of_summable C hC
  have he : (fun pj : ℕ × ℕ => PrimeCompensationLimits.higherPrimePowerWeight pj.1 pj.2 *
      (C 0 - C (PrimeCompensationLimits.higherPrimePowerDisplacement pj.1 pj.2))) =
      (fun pj : ℕ × ℕ => PrimeCompensationLimits.higherPrimePowerWeight pj.1 pj.2 * C 0 -
        PrimeCompensationLimits.higherPrimePowerWeight pj.1 pj.2 *
          C (PrimeCompensationLimits.higherPrimePowerDisplacement pj.1 pj.2)) := by
    funext pj
    ring
  unfold higherPrimePowerDisplacementCorrection higherPrimePowerDiagonal
  rw [he, hw.tsum_sub hc, tsum_mul_right]
  ring

/-- Exact compensation with all signed higher-power and gamma corrections
retained. This analytic interface is discharged for the actual return below. -/
theorem primeCorrelationSector_eq_compensation_of_nullity
    {f : ℝ → ℂ} (hf : SmoothSuperexponentialDecay f)
    (hQ : infinitePrimePowerCorrelationValue
      (Real.eulerMascheroniConstant + Real.log (4 * Real.pi)) (realAutocorrelation f) = 0)
    (hP : (∫ t, weilPoleKernel t * realAutocorrelation f t ∂positiveMeasure) = 0) :
    primeCorrelationSector (realAutocorrelation f) =
      -primeSquareSector (realAutocorrelation f) 1 +
      (Real.eulerMascheroniConstant + Real.log (4 * Real.pi) + Real.log 2 + Real.pi / 2 +
        higherPrimePowerDiagonal) * realAutocorrelation f 0 -
      higherPrimePowerDisplacementCorrection (realAutocorrelation f) -
      2 * (∫ t, weilGammaKernel t *
        (realAutocorrelation f 0 - realAutocorrelation f t) ∂positiveMeasure) := by
  have hs := summable_realAutocorrelation_primePowerTerm hf.decay hf.1.continuous
  have hsplit := PrimeCompensationLimits.primePowerSeries_eq_prime_add_square_add_higher
    (realAutocorrelation f) hs
  have hhigher := higherPrimePowerSector_eq_diagonal_add_displacement
    (realAutocorrelation f) hs
  have he := infinitePrimePowerCorrelationValue_realAutocorrelation_eq_energy
    (Real.eulerMascheroniConstant + Real.log (4 * Real.pi)) hf.decay hf.deriv.decay
    (hf.1.differentiable (by simp))
  rw [hQ, hP, hsplit] at he
  unfold primeCorrelationSector primeSquareSector
  simp only [div_one]
  linarith

end RiemannResearch.RH.SignedWeilCorrelation

namespace RiemannResearch.RH

/-- The complete prime--square compensation identity for an actual arithmetic
return, including any real normalization scalar. No Q=0 assumption remains. -/
theorem primeCorrelationSector_smul_poleCancellation_nymanFullReturn_compensation
    (n : ℕ) [NeZero n] {u : ℝ → ℂ} {a b : ℝ}
    (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (ha : ∀ x < a, u x = 0) (hb : ∀ x > b, u x = 0) (c : ℝ) :
    let C := SignedWeilCorrelation.realAutocorrelation
      (c • poleCancellationOperator (nymanFullReturn n u))
    SignedWeilCorrelation.primeCorrelationSector C =
      -primeSquareSector C 1 +
      (Real.eulerMascheroniConstant + Real.log (4 * Real.pi) + Real.log 2 + Real.pi / 2 +
        SignedWeilCorrelation.higherPrimePowerDiagonal) * C 0 -
      SignedWeilCorrelation.higherPrimePowerDisplacementCorrection C -
      2 * (∫ t, SignedWeilCorrelation.weilGammaKernel t * (C 0 - C t)
        ∂SignedWeilCorrelation.positiveMeasure) := by
  have hG := (smoothSuperexponentialDecay_nymanFullReturn hu ha hb n).poleCancellationOperator
  exact SignedWeilCorrelation.primeCorrelationSector_eq_compensation_of_nullity (hG.const_smul c)
    (infinitePrimePowerCorrelationValue_smul_poleCancellation_nymanFullReturn_eq_zero n hu ha hb c)
    (integral_weilPoleKernel_smul_poleCancellation_nymanFullReturn_eq_zero n hu ha hb c)

end RiemannResearch.RH
