import RiemannResearch.RH.WeilNoncompactExplicitFormula
import RiemannResearch.RH.NymanActualZeroSumNullity
import RiemannResearch.RH.RealAutocorrelationAdmissibility
import RiemannResearch.RH.AutocorrelationHalfMass

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Actual completed Nyman tests are null for the full arithmetic Weil form

The arithmetic form retains the complete von Mangoldt series, both pole
moments, the spatial gamma integral, and its exact diagonal constant.
Its equality with the actual zero sum is supplied by the proved explicit
formula and the concrete smooth cutoff limits. No nullity or identification
assumption appears in the theorem below.
-/

open MeasureTheory
open RiemannResearch.Analysis

namespace RiemannResearch.RH

/-- Full arithmetic Weil nullity of the actual completed Nyman test. The
only input assumptions are a compact smooth seed and an integer conductor. -/
theorem infinitePrimePowerCorrelationValue_nymanCompletedTest_eq_zero
    (n M : ℕ) (hn : 2 ≤ n) {v : ℝ → ℂ} {a b : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0) :
    SignedWeilCorrelation.infinitePrimePowerCorrelationValue
      (Real.eulerMascheroniConstant + Real.log (4 * Real.pi))
      (SignedWeilCorrelation.realAutocorrelation (nymanCompletedTest n M hn v)) = 0 := by
  have hG := smoothSuperexponentialDecay_nymanCompletedTest n M hn hv ha hb
  have hC := SignedWeilCorrelation.smoothSuperexponentialDecay_realAutocorrelation hG
  have heven (t : ℝ) :
      ((SignedWeilCorrelation.realAutocorrelation (nymanCompletedTest n M hn v) (-t) : ℂ)).re =
      ((SignedWeilCorrelation.realAutocorrelation (nymanCompletedTest n M hn v) t : ℂ)).re := by
    simp only [Complex.ofReal_re, SignedWeilCorrelation.realAutocorrelation_neg]
  have hEF := SignedWeilCorrelation.actual_noncompact_Weil_explicit_formula_of_smooth hC heven
  have hz := (actual_zero_sum_nymanCompletedTest_realAutocorrelation_zero n M hn hv ha hb).2
  rw [hz, Complex.zero_re] at hEF
  simpa only [Complex.ofReal_re] using hEF.symm

end RiemannResearch.RH
