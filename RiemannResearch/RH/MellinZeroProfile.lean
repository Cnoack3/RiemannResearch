import RiemannResearch.Analysis.NonnegativeDeficit
import RiemannResearch.RH.MellinCoordinateDefect

/-!
# Explicit zero profiles and a proved Cauchy defect lower bound

Source: ArithmeticProjectionDPPDraft20260921.md (2026-09-21), Section 7.
The exact finite profile is identified with the real/imaginary Mellin
functionals of the cutoff heads. Their existing zeta-zero distance bound
proves domination with constant (2 Re(rho)-1)/2. This weaker constant is
sufficient for the RH test and requires no unproved domination provider.
The sharp rank-one constant and the infinite analytic profile arguments
remain distinct formalization obligations.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators ENNReal

namespace RiemannResearch.RH.Pareto.CoordinateMellin
open CoefficientStabilization IntegerDPP MellinFrequency
open RiemannResearch.Analysis.NonnegativeDeficit

/-- The exact explicit finite zero-mode profile in the draft. -/
def zeroProfilePartial (ρ : ℂ) (M : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.range M,
    star (cellTransform n ρ) * coordinateFeature n t /
      (Real.sqrt (paretoWeight n) : ℂ)

def zeroProfile (ρ : ℂ) (t : ℝ) : ℂ :=
  ∑' n, star (cellTransform n ρ) * coordinateFeature n t /
      (Real.sqrt (paretoWeight n) : ℂ)

/-- Series expression for the sharp constant; its summability and norm
identification are not asserted here. The test uses the proved Cauchy bound. -/
def zeroNormSq (ρ : ℂ) : ℝ :=
  ∑' n, ‖cellTransform n ρ‖ ^ 2 / paretoWeight n

def zeroProfileDensity (ρ : ℂ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (((2 * ρ.re - 1) / 2) * ‖zeroProfile ρ t‖ ^ 2)

def zeroProfilePartialDensity (ρ : ℂ) (M : ℕ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (((2 * ρ.re - 1) / 2) * ‖zeroProfilePartial ρ M t‖ ^ 2)

def zeroWindowMass (ρ : ℂ) (I : Set ℝ) : ℝ≥0∞ :=
  ∫⁻ t in I, zeroProfileDensity ρ t ∂frequencyMeasure

theorem zeroProfilePartial_continuous (ρ : ℂ) (M : ℕ) :
    Continuous (zeroProfilePartial ρ M) := by
  unfold zeroProfilePartial
  exact continuous_finsetSum _ fun n _ =>
    (continuous_const.mul (coordinateFeature_continuous n)).div_const _

theorem zeroProfilePartialDensity_measurable (ρ : ℂ) (M : ℕ) :
    Measurable (zeroProfilePartialDensity ρ M) :=
  (((zeroProfilePartial_continuous ρ M).norm.pow 2).const_mul _).measurable.ennreal_ofReal

theorem countingBasis_mellin_of_pos (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    paretoMellin (countingBasis n) s = cellTransform n s / (Real.sqrt (paretoWeight n) : ℂ) := by
  have h := cellTransform_eq_point_mellin_of_pos n s hs
  rw [paretoPoint_eq_sqrt_smul_countingBasis, paretoMellin_smul, Complex.real_smul] at h
  rw [h]
  exact (mul_div_cancel_left₀ _
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (paretoWeight_pos n)).ne')).symm

theorem zeroProfilePartial_eq_functionals (ρ : ℂ) (hρ : (1 / 2 : ℝ) < ρ.re)
    (M : ℕ) (t : ℝ) :
    zeroProfilePartial ρ M t =
      star (paretoMellin (headReal M t) ρ) +
        Complex.I * star (paretoMellin (headImag M t) ρ) := by
  have hr : paretoMellin (headReal M t) ρ =
      ∑ n ∈ Finset.range M, ((coordinateFeature n t).re : ℂ) *
        paretoMellin (countingBasis n) ρ := by
    change paretoMellinContinuous ρ hρ (headReal M t) = _
    rw [headReal, map_sum]
    simp only [map_smul, Complex.real_smul]
    rfl
  have hi : paretoMellin (headImag M t) ρ =
      ∑ n ∈ Finset.range M, ((coordinateFeature n t).im : ℂ) *
        paretoMellin (countingBasis n) ρ := by
    change paretoMellinContinuous ρ hρ (headImag M t) = _
    rw [headImag, map_sum]
    simp only [map_smul, Complex.real_smul]
    rfl
  rw [hr, hi]
  simp only [Complex.star_def, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  unfold zeroProfilePartial
  apply Finset.sum_congr rfl
  intro n hn
  rw [countingBasis_mellin_of_pos n ρ (by linarith)]
  simp only [map_mul, Complex.conj_ofReal]
  have hz := Complex.re_add_im (coordinateFeature n t)
  calc
    _ = (((coordinateFeature n t).re : ℂ) + ((coordinateFeature n t).im : ℂ) * Complex.I) *
      star (cellTransform n ρ) / (Real.sqrt (paretoWeight n) : ℂ) := by rw [hz]; ring
    _ = _ := by
      simp only [Complex.star_def, div_eq_mul_inv, map_mul, map_inv₀, Complex.conj_ofReal]
      ring

/-- A concrete Cauchy lower bound for the full defect, without a Riesz
vector or profile-domination provider. Its constant is deliberately weaker
than the sharp rank-one constant in the informal draft. -/
theorem zeroProfilePartial_cauchy_bound (ρ : ℂ) (hρ : (1 / 2 : ℝ) < ρ.re)
    (hρ1 : ρ ≠ 1) (hz : riemannZeta ρ = 0) (M : ℕ) (t : ℝ) :
    ((2 * ρ.re - 1) / 2) * ‖zeroProfilePartial ρ M t‖ ^ 2 ≤ diagonalDefect M t := by
  have hr := closedSpace_mellin_distance_sq_lower_bound ρ hρ hρ1 hz
    (headReal M t) (closedSpace.starProjection (headReal M t))
    (closedSpace.starProjection_apply_mem _)
  have hi := closedSpace_mellin_distance_sq_lower_bound ρ hρ hρ1 hz
    (headImag M t) (closedSpace.starProjection (headImag M t))
    (closedSpace.starProjection_apply_mem _)
  have hn : ‖zeroProfilePartial ρ M t‖ ≤
      ‖paretoMellin (headReal M t) ρ‖ + ‖paretoMellin (headImag M t) ρ‖ := by
    rw [zeroProfilePartial_eq_functionals ρ hρ]
    simpa only [norm_star, norm_mul, Complex.norm_I, one_mul] using
      norm_add_le (star (paretoMellin (headReal M t) ρ))
        (Complex.I * star (paretoMellin (headImag M t) ρ))
  have hn2 : ‖zeroProfilePartial ρ M t‖ ^ 2 ≤
      2 * (‖paretoMellin (headReal M t) ρ‖ ^ 2 + ‖paretoMellin (headImag M t) ρ‖ ^ 2) := by
    nlinarith [norm_nonneg (zeroProfilePartial ρ M t),
      norm_nonneg (paretoMellin (headReal M t) ρ), norm_nonneg (paretoMellin (headImag M t) ρ),
      sq_nonneg (‖paretoMellin (headReal M t) ρ‖ - ‖paretoMellin (headImag M t) ρ‖)]
  have hc : 0 ≤ 2 * ρ.re - 1 := by linarith
  have hm := mul_le_mul_of_nonneg_left hn2 hc
  change _ ≤ ‖headReal M t - closedSpace.starProjection (headReal M t)‖ ^ 2 +
    ‖headImag M t - closedSpace.starProjection (headImag M t)‖ ^ 2
  nlinarith


/-- Fatou converts the actual pointwise profile bound and convergence into
the lower bound on the actual unscaled window deficit. -/
theorem zeroWindowMass_le_liminf (ρ : ℂ) (I : Set ℝ)
    (hρ : (1 / 2 : ℝ) < ρ.re) (hρ1 : ρ ≠ 1) (hz : riemannZeta ρ = 0)
    (hconv : ∀ t, Tendsto (fun M => zeroProfilePartial ρ M t) atTop
      (𝓝 (zeroProfile ρ t))) :
    zeroWindowMass ρ I ≤ Filter.liminf (fun M => windowDeficit M I) atTop := by
  apply integral_le_liminf_of_dominated_profile (frequencyMeasure.restrict I)
    (zeroProfilePartialDensity ρ) (zeroProfileDensity ρ)
    (fun M => windowDeficit M I)
  · exact zeroProfilePartialDensity_measurable ρ
  · intro t
    exact ENNReal.tendsto_ofReal (((hconv t).norm.pow 2).const_mul _)
  · intro M
    exact lintegral_mono fun t => ENNReal.ofReal_le_ofReal
      (zeroProfilePartial_cauchy_bound ρ hρ hρ1 hz M t)

end RiemannResearch.RH.Pareto.CoordinateMellin
