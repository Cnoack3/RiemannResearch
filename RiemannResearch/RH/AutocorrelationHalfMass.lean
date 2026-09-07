import RiemannResearch.Analysis.SuperexponentialDecay
import RiemannResearch.Analysis.EvenIntegralHalfLine
import RiemannResearch.Analysis.BilateralLaplaceCorrelation
import RiemannResearch.RH.SignedWeilCorrelation
import RiemannResearch.RH.SuperexponentialSquareProfile
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Actual autocorrelation reflection and half-line mass

Reflection is proved by translation of the actual integral. The half-line
factor one-half follows from that symmetry and integrability, with the origin
handled by complementary Iic/Ioi sets. The total mass provider is separate.
-/

open MeasureTheory Set
namespace RiemannResearch.Analysis

/-- Reflection of an actual autocorrelation is complex conjugation. -/
theorem crossCorrelation_self_neg (f : ℝ → ℂ) (t : ℝ) :
    crossCorrelation f f (-t) = star (crossCorrelation f f t) := by
  unfold crossCorrelation
  change (∫ y : ℝ, f (y + -t) * star (f y)) =
    (starRingEnd ℂ) (∫ y : ℝ, f (y + t) * star (f y))
  rw [← integral_conj]
  calc
    _ = ∫ y : ℝ, f y * star (f (y + t)) := by
      rw [← integral_add_right_eq_self (fun y : ℝ => f (y + -t) * star (f y)) t]
      apply integral_congr_ae
      exact ae_of_all _ (fun y => by simp only [add_neg_cancel_right])
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun y => by simp only [map_mul, starRingEnd_apply,
        star_star, mul_comm])

end RiemannResearch.Analysis

namespace RiemannResearch.RH.SignedWeilCorrelation

/-- The project's actual real autocorrelation is even. -/
theorem realAutocorrelation_neg (f : ℝ → ℂ) (t : ℝ) :
    realAutocorrelation f (-t) = realAutocorrelation f t := by
  change (Analysis.crossCorrelation f f (-t)).re = (Analysis.crossCorrelation f f t).re
  rw [Analysis.crossCorrelation_self_neg]
  rfl

/-- The positive-half mass equals half the full actual real autocorrelation mass. -/
theorem integral_realAutocorrelation_Ioi (f : ℝ → ℂ)
    (hi : Integrable (realAutocorrelation f)) :
    (∫ t in Ioi 0, realAutocorrelation f t) = (∫ t, realAutocorrelation f t) / 2 :=
  Analysis.integral_Ioi_zero_eq_half_of_even _ hi (realAutocorrelation_neg f)

/-- The actual full real autocorrelation mass is the squared complex norm of
the integral of the test. The Fubini and integrability providers are concrete. -/
theorem integral_realAutocorrelation_eq_normSq (f : ℝ → ℂ)
    (hf : Analysis.SuperexponentialDecay f) (hfc : Continuous f) :
    (∫ t, realAutocorrelation f t) = Complex.normSq (∫ y, f y) := by
  have hfi : Integrable f := by
    simpa [BilateralLaplace.kernel] using
      BilateralLaplace.integrable_integrand (hf.hasExponentialMoments hfc) 0
  have hi := BilateralLaplace.integrable_crossCorrelation hfc hfc hfi hfi
  change (∫ t, (Analysis.crossCorrelation f f t).re) = _
  have hre : (∫ t, (Analysis.crossCorrelation f f t).re) =
      (∫ t, Analysis.crossCorrelation f f t).re := integral_re hi
  rw [hre, BilateralLaplace.integral_crossCorrelation
    (hf.hasExponentialMoments hfc) (hf.hasExponentialMoments hfc) hfc hfc]
  simp only [Complex.mul_conj, Complex.ofReal_re]

/-- Exact positive-half mass, including the one-half factor used by the square
main term. No assumed autocorrelation identity occurs. -/
theorem integral_realAutocorrelation_Ioi_eq_normSq (f : ℝ → ℂ)
    (hf : Analysis.SuperexponentialDecay f) (hfc : Continuous f) :
    (∫ t in Ioi 0, realAutocorrelation f t) = Complex.normSq (∫ y, f y) / 2 := by
  have hfi : Integrable f := by
    simpa [BilateralLaplace.kernel] using
      BilateralLaplace.integrable_integrand (hf.hasExponentialMoments hfc) 0
  have hi := BilateralLaplace.integrable_crossCorrelation hfc hfc hfi hfi
  rw [integral_realAutocorrelation_Ioi f hi.re,
    integral_realAutocorrelation_eq_normSq f hf hfc]

/-- Real projection preserves the actual autocorrelation decay. -/
theorem superexponential_realAutocorrelation (f : ℝ → ℂ)
    (hf : Analysis.SuperexponentialDecay f) (hfc : Continuous f) :
    Analysis.SuperexponentialDecay (realAutocorrelation f) := by
  intro a ha
  obtain ⟨A, hA, hbound⟩ := hf.crossCorrelation hf hfc hfc a ha
  refine ⟨A, hA, ?_⟩
  intro t
  change ‖(Analysis.crossCorrelation f f t).re‖ ≤ _
  rw [Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm _).trans (hbound t)

/-- The exact square main coefficient for an actual autocorrelation. Its C¹
regularity and derivative decay are explicit; all arithmetic convergence,
the complete signed discrepancy, and the one-half mass factor are proved. -/
theorem primeSquareSector_realAutocorrelation_exact (f : ℝ → ℂ)
    (hf : Analysis.SuperexponentialDecay f) (hfc : Continuous f)
    (hCd : Differentiable ℝ (realAutocorrelation f))
    (hCc' : Continuous (deriv (realAutocorrelation f)))
    (hCs' : Analysis.SuperexponentialDecay (deriv (realAutocorrelation f)))
    {R : ℝ} (hR : 0 < R) :
    primeSquareSector (realAutocorrelation f) R =
      -(R / 2) * Complex.normSq (∫ y, f y) +
      (4 / R) * ∫ x in Ioi 1,
        deriv (realAutocorrelation f) (2 * Real.log x / R) *
          primeSquareDiscrepancy x / x := by
  rw [primeSquareSector_exact_of_superexponential _ hCd hCc'
    (superexponential_realAutocorrelation f hf hfc) hCs' hR,
    integral_realAutocorrelation_Ioi_eq_normSq f hf hfc]
  ring

end RiemannResearch.RH.SignedWeilCorrelation
