import RiemannResearch.Analysis.GammaLaplaceKernel
import RiemannResearch.RH.WeilExplicitFormula.ExplicitFormula

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Exact frequency-to-space transport of one digamma increment

The Fourier normalization and weighted inversion are those of the vendored
Apache-2.0 `Zeta23/ExplicitFormula.lean`, `paper_inversion` and
`integral_k_mul_weight`. Only those unconditional Fourier theorems are used;
the structure-field hypothesis `EF_lit` is not used here.

For b>0 the real digamma increment is
1/b - b/(b²+(r/2)²). Its exact spatial counterpart is the difference between
(1/b)k(0) and the integral of k(u)exp(-2b|u|).
-/

open MeasureTheory Complex
open scoped FourierTransform

namespace RiemannResearch.RH

open RiemannResearch.Analysis.GammaLaplaceKernel

theorem integrable_paperFT_mul_gammaIncrement {k : ℝ → ℂ}
    (hFk : Integrable (𝓕 k)) {b : ℝ} (hb : 0 < b) :
    Integrable (fun r : ℝ => Zeta23.paperFT k r *
      ((1 / b - b / (b ^ 2 + (r / 2) ^ 2) : ℝ) : ℂ)) := by
  have hH := Zeta23.EF.integrable_paperFT_ofReal hFk
  have hE := integrable_evenExponential (by positivity : 0 < 2 * b)
  have hB := Zeta23.EF.integrable_paperFT_mul_weightFT hFk hE
  simp_rw [integral_evenExponential_two_mul hb] at hB
  have hdiff := (hH.mul_const (1 / (b : ℂ))).sub hB
  convert hdiff using 1
  funext r
  simp only [Pi.sub_apply]
  push_cast
  ring

/-- Exact normalized integral of one real digamma increment, with all weights
and 2π factors retained. Both sides concern the actual Fourier/inverse integrals. -/
theorem integral_paperFT_mul_gammaIncrement {k : ℝ → ℂ}
    (hk : Continuous k) (hki : Integrable k) (hFk : Integrable (𝓕 k))
    {b : ℝ} (hb : 0 < b) :
    (1 / (2 * Real.pi) : ℂ) *
        (∫ r : ℝ, Zeta23.paperFT k r *
          ((1 / b - b / (b ^ 2 + (r / 2) ^ 2) : ℝ) : ℂ)) =
      (1 / (b : ℂ)) * k 0 - ∫ u : ℝ, k u * evenExponential (2 * b) u := by
  have hH := Zeta23.EF.integrable_paperFT_ofReal hFk
  have hE := integrable_evenExponential (by positivity : 0 < 2 * b)
  have hB := Zeta23.EF.integrable_paperFT_mul_weightFT hFk hE
  have hweight := Zeta23.EF.integral_k_mul_weight hk hki hFk hE
  simp_rw [integral_evenExponential_two_mul hb] at hB hweight
  have hzero := Zeta23.EF.paper_inversion hk hki hFk 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at hzero
  have hsplit :
      (fun r : ℝ => Zeta23.paperFT k r *
        ((1 / b - b / (b ^ 2 + (r / 2) ^ 2) : ℝ) : ℂ)) =
      fun r : ℝ => Zeta23.paperFT k r * (1 / (b : ℂ)) -
        Zeta23.paperFT k r * ((b : ℂ) / ((b : ℂ) ^ 2 + ((r : ℂ) / 2) ^ 2)) := by
    funext r
    push_cast
    ring
  rw [hsplit, integral_sub (hH.mul_const (1 / (b : ℂ))) hB,
    Zeta23.EF.cintegral_mul_const]
  calc
    _ = (1 / (b : ℂ)) *
        ((1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, Zeta23.paperFT k r) -
      (1 / (2 * Real.pi) : ℂ) *
        ∫ r : ℝ, Zeta23.paperFT k r *
          ((b : ℂ) / ((b : ℂ) ^ 2 + ((r : ℂ) / 2) ^ 2)) := by ring
    _ = _ := by rw [← hzero, ← hweight]

end RiemannResearch.RH
