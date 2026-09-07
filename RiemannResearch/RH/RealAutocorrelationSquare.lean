import RiemannResearch.Analysis.CrossCorrelationDerivative
import RiemannResearch.RH.AutocorrelationHalfMass

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Square identities for actual smooth decaying tests

The C¹ regularity and derivative decay of the actual real autocorrelation are
conclusions of C² regularity and superexponential decay of the test and its
first two derivatives. This discharges the correlation-level calculus inputs
of the exact noncompact square formula.
-/

open MeasureTheory Set
open RiemannResearch.Analysis
namespace RiemannResearch.RH.SignedWeilCorrelation

/-- Differentiation of the actual real autocorrelation under its integral. -/
theorem hasDerivAt_realAutocorrelation {f : ℝ → ℂ}
    (hf : SuperexponentialDecay f) (hdf : SuperexponentialDecay (deriv f))
    (hfd : Differentiable ℝ f) (hdfc : Continuous (deriv f)) (t : ℝ) :
    HasDerivAt (realAutocorrelation f) (crossCorrelation (deriv f) f t).re t := by
  have hd := hf.hasDerivAt_crossCorrelation hf hdf hfd hdfc hfd.continuous t
  convert Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd using 1 <;> rfl

/-- Concrete C² decay assumptions on f supply C¹ regularity and
superexponential derivative decay of its actual real autocorrelation. -/
theorem realAutocorrelation_calculus_providers {f : ℝ → ℂ}
    (hf : SuperexponentialDecay f) (hdf : SuperexponentialDecay (deriv f))
    (hddf : SuperexponentialDecay (deriv (deriv f)))
    (hfd : Differentiable ℝ f) (hfdd : Differentiable ℝ (deriv f)) :
    Differentiable ℝ (realAutocorrelation f) ∧
    Continuous (deriv (realAutocorrelation f)) ∧
    SuperexponentialDecay (deriv (realAutocorrelation f)) := by
  have hd (t : ℝ) := hasDerivAt_realAutocorrelation hf hdf hfd hfdd.continuous t
  have he : deriv (realAutocorrelation f) =
      (fun t => (crossCorrelation (deriv f) f t).re) := by
    funext t
    exact (hd t).deriv
  refine ⟨fun t => (hd t).differentiableAt, ?_, ?_⟩
  · obtain ⟨K, hK⟩ := hdf.exists_crossCorrelation_lipschitz hf hddf hfdd hfd.continuous
    rw [he]
    exact Complex.continuous_re.comp hK.continuous
  · rw [he]
    intro a ha
    obtain ⟨A, hA, hbound⟩ := hdf.crossCorrelation hf hfdd.continuous hfd.continuous a ha
    refine ⟨A, hA, ?_⟩
    intro t
    rw [Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (hbound t)

/-- Complete noncompact prime-square identity for an actual C² test with
superexponentially decaying first two derivatives. All correlation regularity,
mass, series convergence, improper limits, and arithmetic discrepancy bounds
have concrete providers. -/
theorem primeSquareSector_realAutocorrelation_of_decay {f : ℝ → ℂ}
    (hf : SuperexponentialDecay f) (hdf : SuperexponentialDecay (deriv f))
    (hddf : SuperexponentialDecay (deriv (deriv f)))
    (hfd : Differentiable ℝ f) (hfdd : Differentiable ℝ (deriv f))
    {R : ℝ} (hR : 0 < R) :
    primeSquareSector (realAutocorrelation f) R =
      -(R / 2) * Complex.normSq (∫ y, f y) +
      (4 / R) * ∫ x in Ioi 1,
        deriv (realAutocorrelation f) (2 * Real.log x / R) *
          primeSquareDiscrepancy x / x := by
  obtain ⟨hCd, hCc', hCs'⟩ := realAutocorrelation_calculus_providers hf hdf hddf hfd hfdd
  exact primeSquareSector_realAutocorrelation_exact f hf hfd.continuous hCd hCc' hCs' hR

end RiemannResearch.RH.SignedWeilCorrelation
