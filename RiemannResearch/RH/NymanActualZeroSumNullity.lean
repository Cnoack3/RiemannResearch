import RiemannResearch.RH.NymanAutocorrelationNullity
import RiemannResearch.RH.WeilZeroSumConvergence

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# The actual zero-side sum of a completed Nyman autocorrelation is zero

The upstream Fourier sign, actual zeta-zero subtype, and analytic zero
multiplicities are retained. Every summand is proved zero, so summability
is supplied explicitly rather than inferred from a totalized tsum value.
-/

open MeasureTheory
open RiemannResearch.Analysis

namespace RiemannResearch.RH

theorem paperFT_gammaOf_nymanCompletedTest_realAutocorrelation_zero
    (n M : ℕ) (hn : 2 ≤ n) {v : ℝ → ℂ} {a b : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0)
    (ρ : Zeta23.zetaZeroConfig.carrier) :
    Zeta23.paperFT
      (fun t => (SignedWeilCorrelation.realAutocorrelation (nymanCompletedTest n M hn v) t : ℂ))
      (Zeta23.gammaOf ρ) = 0 := by
  have hρ : riemannZeta (ρ : ℂ) = 0 ∧ 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := ρ.property
  rw [WeilExplicitFormula.paperFT_gammaOf_eq_centeredTransform]
  apply realAutocorrelation_nymanCompletedTest_centeredTransform_zero n M hn hv ha hb
  · exact riemannZeta_one_sub_eq_zero_of_strip hρ.1 hρ.2.1 hρ.2.2
  · simp only [Complex.sub_re, Complex.one_re]
    linarith [hρ.2.2]
  · simp only [Complex.sub_re, Complex.one_re]
    linarith [hρ.2.1]

theorem actual_zero_sum_nymanCompletedTest_realAutocorrelation_zero
    (n M : ℕ) (hn : 2 ≤ n) {v : ℝ → ℂ} {a b : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier =>
      ‖(Zeta23.zeroMult ρ : ℂ) * Zeta23.paperFT
        (fun t => (SignedWeilCorrelation.realAutocorrelation (nymanCompletedTest n M hn v) t : ℂ))
        (Zeta23.gammaOf ρ)‖) ∧
    (∑' ρ : Zeta23.zetaZeroConfig.carrier,
      (Zeta23.zeroMult ρ : ℂ) * Zeta23.paperFT
        (fun t => (SignedWeilCorrelation.realAutocorrelation (nymanCompletedTest n M hn v) t : ℂ))
        (Zeta23.gammaOf ρ)) = 0 := by
  simp only [paperFT_gammaOf_nymanCompletedTest_realAutocorrelation_zero n M hn hv ha hb,
    mul_zero, norm_zero, summable_zero, tsum_zero, and_self]

end RiemannResearch.RH
