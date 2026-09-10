import RiemannResearch.Analysis.ComplexTentIntegral

/- Source: user-provided FourierBridgeUniformSignedEnergy20260910.md, Section 2.
This module defines the actual Mellin integrals; periodized Fourier reconstruction
is a separate obligation. -/
import RiemannResearch.RH.DyadicResidueBinaryLogMean

/-!
# Actual dyadic tent Mellin coefficients

These coefficients are defined by the actual integral. Their identification
as coefficients of the infinite periodization is a separate obligation.
-/

noncomputable section

open MeasureTheory RiemannResearch.Analysis

namespace RiemannResearch.RH.Pareto

/-- Integer frequencies for the circle of circumference `log 2`. -/
def dyadicLogFrequency (h : ℤ) : ℝ := 2 * Real.pi * h / Real.log 2

@[simp] theorem dyadicLogFrequency_zero : dyadicLogFrequency 0 = 0 := by
  simp [dyadicLogFrequency]

theorem dyadicLogFrequency_ne_zero {h : ℤ} (hh : h ≠ 0) :
    dyadicLogFrequency h ≠ 0 := by
  unfold dyadicLogFrequency
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      (by exact_mod_cast hh))
    (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))

/-- The normalized Mellin integral of the actual root tent at the actual dyadic frequency. -/
def dyadicTentMellinCoefficient (i : ℕ) (h : ℤ) : ℂ :=
  (Real.log 2 : ℂ)⁻¹ *
    ∫ x in (2 * (i + 1) : ℝ)..2 * (i + 1) + 2,
      (rootTent (2 * (i + 1)) x : ℂ) *
        (x : ℂ) ^ (-Complex.I * (dyadicLogFrequency h : ℂ) - 1)

/-- The closed form for every nonzero mode, with no Fourier-limit assumption. -/
theorem dyadicTentMellinCoefficient_ne_zero_mode (i : ℕ) {h : ℤ} (hh : h ≠ 0) :
    dyadicTentMellinCoefficient i h =
      (Real.log 2 : ℂ)⁻¹ *
        ((((2 * (i + 1) : ℝ) : ℂ) ^ (-Complex.I * (dyadicLogFrequency h : ℂ) + 1) -
          2 * (((2 * (i + 1) + 1 : ℝ) : ℂ) ^
            (-Complex.I * (dyadicLogFrequency h : ℂ) + 1)) +
          (((2 * (i + 1) + 2 : ℝ) : ℂ) ^
            (-Complex.I * (dyadicLogFrequency h : ℂ) + 1))) /
          ((-Complex.I * (dyadicLogFrequency h : ℂ)) *
            (-Complex.I * (dyadicLogFrequency h : ℂ) + 1))) := by
  unfold dyadicTentMellinCoefficient
  rw [integral_rootTent_fourier_kernel (by positivity) (dyadicLogFrequency_ne_zero hh)]

/-- The zero mode is the normalized actual binary logarithmic boundary. -/
theorem dyadicTentMellinCoefficient_zero_mode (i : ℕ) :
    dyadicTentMellinCoefficient i 0 =
      (dyadicBinaryBoundaryLog i : ℂ) / (Real.log 2 : ℂ) := by
  unfold dyadicTentMellinCoefficient
  simp only [dyadicLogFrequency_zero, Complex.ofReal_zero, mul_zero, zero_sub]
  rw [integral_rootTent_cpow_neg_one (by positivity)]
  unfold dyadicBinaryBoundaryLog
  simp only [div_eq_mul_inv]
  ring

/-- The normalization constant recovers the existing actual binary residue coordinate. -/
theorem log_two_mul_dyadicTentMellinCoefficient_zero (i : ℕ) :
    (Real.log 2 : ℂ) * dyadicTentMellinCoefficient i 0 =
      (dyadicBoundaryCoordinate (hilbertResidue 2 (by norm_num)) i : ℂ) := by
  have hlog : (Real.log 2 : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  rw [dyadicTentMellinCoefficient_zero_mode,
    dyadicBoundaryCoordinate_residue_two_eq_log]
  field_simp

end RiemannResearch.RH.Pareto


/-! Explicit inverse-square decay for the actual dyadic tent coefficients. -/

noncomputable section

open MeasureTheory RiemannResearch.Analysis

namespace RiemannResearch.RH.Pareto

/-- For every fixed tent, its actual Mellin coefficients have inverse-square decay. -/
theorem norm_dyadicTentMellinCoefficient_le_inv_sq (i : ℕ) {h : ℤ} (hh : h ≠ 0) :
    ‖dyadicTentMellinCoefficient i h‖ ≤
      (4 * (2 * (i + 1) + 1 : ℝ) * Real.log 2 / (2 * Real.pi) ^ 2) /
        (h : ℝ) ^ 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcast : (h : ℝ) ≠ 0 := by exact_mod_cast hh
  have hbound := norm_integral_rootTent_fourier_kernel_le
    (a := (2 * (i + 1) : ℝ)) (by positivity) (dyadicLogFrequency_ne_zero hh)
  rw [dyadicTentMellinCoefficient, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hlog]
  calc
    (Real.log 2)⁻¹ *
        ‖∫ x in (2 * (i + 1) : ℝ)..2 * (i + 1) + 2,
          (rootTent (2 * (i + 1)) x : ℂ) *
            (x : ℂ) ^ (-Complex.I * (dyadicLogFrequency h : ℂ) - 1)‖ ≤
      (Real.log 2)⁻¹ *
        (4 * (2 * (i + 1) + 1 : ℝ) / (dyadicLogFrequency h) ^ 2) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hlog.le)
    _ = _ := by
      unfold dyadicLogFrequency
      field_simp [hlog.ne', Real.pi_ne_zero, hcast]

end RiemannResearch.RH.Pareto
