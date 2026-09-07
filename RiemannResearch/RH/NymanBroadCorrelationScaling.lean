import RiemannResearch.RH.NymanBroadKernelEnergy
import RiemannResearch.RH.NymanBroadCorrelationBounds

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-! # Exact change of scale between the arithmetic and profile correlations -/

open MeasureTheory
namespace RiemannResearch.RH
open RiemannResearch.Analysis

/-- Exact pointwise half-density expression for the normalized arithmetic test. -/
theorem nymanNormalizedBroadTest_eq_profile (n : ℕ) (hn : 0 < n)
    {φ : ℝ → ℝ} {a b R : ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (ha : ∀ x < a, φ x = 0) (hb : ∀ x > b, φ x = 0) (hR : 0 < R)
    (y : ℝ) :
    nymanNormalizedBroadTest n φ R y =
      (((Real.sqrt R)⁻¹ * nymanBroadProfile n φ R (y / R) : ℝ) : ℂ) := by
  have h := nymanNormalizedBroadTest_scaled_eq n hn hφ ha hb hR (y / R)
  have hy : R * (y / R) = y := by field_simp [hR.ne']
  rw [hy] at h
  have hs : (Real.sqrt R : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hR).ne'
  calc
    _ = (Real.sqrt R : ℂ)⁻¹ *
        ((Real.sqrt R : ℂ) * nymanNormalizedBroadTest n φ R y) := by
      rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]
    _ = _ := by rw [h]; push_cast; rfl

/-- The actual autocorrelation of the normalized arithmetic test equals
the actual broad-profile correlation at displacement t/R. The Jacobian
exactly cancels the square of the half-density amplitude. -/
theorem realAutocorrelation_nymanNormalizedBroadTest (n : ℕ) (hn : 0 < n)
    {φ : ℝ → ℝ} {a b R : ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (ha : ∀ x < a, φ x = 0) (hb : ∀ x > b, φ x = 0) (hR : 0 < R)
    (t : ℝ) :
    SignedWeilCorrelation.realAutocorrelation (nymanNormalizedBroadTest n φ R) t =
      nymanBroadCorrelation n φ R (t / R) := by
  let B := nymanBroadProfile n φ R
  have hprod (y : ℝ) :
      nymanNormalizedBroadTest n φ R (y + t) * star (nymanNormalizedBroadTest n φ R y) =
      (((1 / R) * (B (y / R + t / R) * B (y / R)) : ℝ) : ℂ) := by
    rw [nymanNormalizedBroadTest_eq_profile n hn hφ ha hb hR,
      nymanNormalizedBroadTest_eq_profile n hn hφ ha hb hR]
    simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
    congr 1
    rw [add_div]
    have hs : ((Real.sqrt R)⁻¹) ^ 2 = R⁻¹ := by
      rw [inv_pow, Real.sq_sqrt hR.le]
    change (Real.sqrt R)⁻¹ * B (y / R + t / R) *
      ((Real.sqrt R)⁻¹ * B (y / R)) = _
    calc
      _ = ((Real.sqrt R)⁻¹) ^ 2 * (B (y / R + t / R) * B (y / R)) := by ring
      _ = _ := by rw [hs]; ring
  change (∫ y : ℝ, nymanNormalizedBroadTest n φ R (y + t) *
    star (nymanNormalizedBroadTest n φ R y)).re = _
  simp_rw [hprod]
  rw [integral_complex_ofReal]
  simp only [Complex.ofReal_re]
  rw [integral_const_mul]
  have hscale : (∫ y : ℝ, B (y / R + t / R) * B (y / R)) =
      R * ∫ x : ℝ, B (x + t / R) * B x := by
    have h := Measure.integral_comp_div (fun x : ℝ => B (x + t / R) * B x) R
    simpa only [abs_of_pos hR, smul_eq_mul] using h
  rw [hscale]
  rw [nymanBroadCorrelation_eq_realKernel]
  change (1 / R) * (R * ∫ x : ℝ, B (x + t / R) * B x) =
    ∫ x : ℝ, B (x + t / R) * B x
  field_simp [hR.ne']

end RiemannResearch.RH
