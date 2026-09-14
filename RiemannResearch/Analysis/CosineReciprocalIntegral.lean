import RiemannResearch.Analysis.FourierL1L2Plancherel
import RiemannResearch.Analysis.EvenIntegralHalfLine
import RiemannResearch.RH.ParetoCompressedMellinNorm
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! The positive cosine integral, evaluated using ordinary-integral Plancherel
for the indicator of the unit interval. No conditional Dirichlet integral is used. -/

noncomputable section
open MeasureTheory Set
open scoped FourierTransform
namespace RiemannResearch.Analysis

private def cosineQuotient (u : ℝ) : ℝ := (1 - Real.cos u) / u ^ 2

private theorem cosineQuotient_nonneg (u : ℝ) : 0 ≤ cosineQuotient u :=
  div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (sq_nonneg _)

private theorem cosineQuotient_le (u : ℝ) :
    cosineQuotient u ≤ 4 * (1 + u ^ 2)⁻¹ := by
  by_cases hu : u = 0
  · simp [cosineQuotient, hu]
  have hu2 : 0 < u ^ 2 := sq_pos_of_ne_zero hu
  have hd : 0 < 1 + u ^ 2 := by positivity
  by_cases hs : u ^ 2 ≤ 1
  · have hq : cosineQuotient u ≤ 1 / 2 := by
      rw [cosineQuotient, div_le_iff₀ hu2]
      have h := RiemannResearch.RH.Pareto.CompressedMellin.one_sub_cos_le_half_square u
      linarith
    have hc : (1 : ℝ) / 2 ≤ 4 / (1 + u ^ 2) := by
      rw [le_div_iff₀ hd]
      nlinarith
    simpa only [div_eq_mul_inv] using hq.trans hc
  · have hq : cosineQuotient u ≤ 2 / u ^ 2 := by
      apply div_le_div_of_nonneg_right _ hu2.le
      linarith [Real.neg_one_le_cos u]
    have hc : 2 / u ^ 2 ≤ 4 / (1 + u ^ 2) := by
      rw [div_le_div_iff₀ hu2 hd]
      linarith
    simpa only [div_eq_mul_inv] using hq.trans hc

private theorem cosineQuotient_integrable : Integrable cosineQuotient := by
  apply (integrable_inv_one_add_sq.const_mul 4).mono'
    ((measurable_const.sub Real.measurable_cos).div (measurable_id.pow_const 2)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun u => by
    change ‖cosineQuotient u‖ ≤ 4 * (1 + u ^ 2)⁻¹
    rw [Real.norm_eq_abs, abs_of_nonneg (cosineQuotient_nonneg u)]
    exact cosineQuotient_le u)

private def unitBox : ℝ → ℂ := (Ioc (0 : ℝ) 1).indicator (fun _ => 1)

private theorem unitBox_memLp (p : ENNReal) : MemLp unitBox p := by
  apply memLp_indicator_const p measurableSet_Ioc
  exact Or.inr (by simp)

private theorem unitBox_fourier (ξ : ℝ) (hξ : ξ ≠ 0) :
    𝓕 unitBox ξ =
      (Complex.exp (-2 * Real.pi * ξ * Complex.I) - 1) /
        (-2 * Real.pi * ξ * Complex.I) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have he : (fun x : ℝ => Complex.exp (↑(-2 * Real.pi * x * ξ) * Complex.I) • unitBox x) =
      (Ioc (0 : ℝ) 1).indicator
        (fun x => Complex.exp ((-2 * Real.pi * ξ * Complex.I) * (x : ℂ))) := by
    funext x
    by_cases hx : x ∈ Ioc (0 : ℝ) 1
    · simp only [unitBox, indicator_of_mem hx, smul_eq_mul, mul_one]
      congr 1
      push_cast
      ring
    · simp [unitBox, hx]
  have hc : (-2 * Real.pi * ξ * Complex.I : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
      · exact_mod_cast hξ
    · exact Complex.I_ne_zero
  rw [he, integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_exp_mul_complex hc]
  simp

private theorem unitBox_fourier_norm_sq (ξ : ℝ) (hξ : ξ ≠ 0) :
    ‖𝓕 unitBox ξ‖ ^ 2 = 2 * cosineQuotient (2 * Real.pi * ξ) := by
  rw [unitBox_fourier ξ hξ, norm_div, div_pow]
  have hp : ‖Complex.exp (-2 * Real.pi * ξ * Complex.I) - 1‖ ^ 2 =
      2 * (1 - Real.cos (2 * Real.pi * ξ)) := by
    have h := RiemannResearch.RH.Pareto.CompressedMellin.norm_phase_difference_sq
      1 1 (-(2 * Real.pi * ξ)) 0
    have hphase : Complex.I * ((-(2 * Real.pi * ξ) : ℝ) : ℂ) =
        -2 * Real.pi * ξ * Complex.I := by
      push_cast
      ring
    rw [hphase] at h
    calc
      _ = (1 : ℝ) ^ 2 + 1 ^ 2 - 2 * 1 * 1 *
          Real.cos (-(2 * Real.pi * ξ) - 0) := by
        simpa only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, mul_zero,
          Complex.exp_zero] using h
      _ = _ := by rw [sub_zero, Real.cos_neg]; ring
  have hd : ‖(-2 * Real.pi * ξ * Complex.I : ℂ)‖ ^ 2 = (2 * Real.pi * ξ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  rw [hp, hd]
  simp only [cosineQuotient]
  ring

private theorem integral_cosineQuotient : (∫ u, cosineQuotient u) = Real.pi := by
  have hb : (∫ x, ‖unitBox x‖ ^ 2) = 1 := by
    have he : (fun x => ‖unitBox x‖ ^ 2) = (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) := by
      funext x
      by_cases hx : x ∈ Ioc (0 : ℝ) 1 <;> simp [unitBox, hx]
    rw [he, integral_indicator measurableSet_Ioc]
    simp
  have hp := integral_norm_sq_fourier_of_integrable
    (memLp_one_iff_integrable.mp (unitBox_memLp 1)) (unitBox_memLp 2)
  rw [hb] at hp
  have he : (∫ ξ, ‖𝓕 unitBox ξ‖ ^ 2) =
      ∫ ξ, 2 * cosineQuotient (ξ * (2 * Real.pi)) := by
    apply integral_congr_ae
    filter_upwards [show ∀ᵐ ξ : ℝ, ξ ≠ 0 from volume.ae_ne 0] with ξ hξ
    rw [unitBox_fourier_norm_sq ξ hξ]
    congr 2
    ring
  rw [he, integral_const_mul, Measure.integral_comp_mul_right] at hp
  have hpi : 0 < 2 * Real.pi := by positivity
  simp only [smul_eq_mul, abs_of_pos (inv_pos.mpr hpi)] at hp
  field_simp [ne_of_gt hpi] at hp
  nlinarith

/-- Exact absolutely convergent positive cosine integral. -/
theorem integral_one_sub_cos_div_sq_Ioi :
    (∫ u in Ioi (0 : ℝ), (1 - Real.cos u) / u ^ 2) = Real.pi / 2 := by
  change (∫ u in Ioi (0 : ℝ), cosineQuotient u) = _
  rw [integral_Ioi_zero_eq_half_of_even cosineQuotient cosineQuotient_integrable
    (by intro u; simp [cosineQuotient]), integral_cosineQuotient]

/-- Reciprocal-coordinate version needed for dominated convergence of the
scaled actual cosine-deficit step densities. -/
theorem integral_one_sub_cos_inv_Ioi :
    (∫ x in Ioi (0 : ℝ), 1 - Real.cos (1 / x)) = Real.pi / 2 := by
  have hd : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun x : ℝ => x⁻¹) (-(x ^ 2)⁻¹) (Ioi 0) x := by
    intro x hx
    exact (hasDerivAt_inv (ne_of_gt hx)).hasDerivWithinAt
  have hi : Set.InjOn (fun x : ℝ => x⁻¹) (Ioi 0) :=
    inv_injective.injOn
  have him : (fun x : ℝ => x⁻¹) '' Ioi (0 : ℝ) = Ioi 0 := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change 0 < y⁻¹
      exact inv_pos.mpr (show 0 < y from hy)
    · intro hx
      refine ⟨x⁻¹, ?_, inv_inv x⟩
      change 0 < x⁻¹
      exact inv_pos.mpr (show 0 < x from hx)
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hi
    (fun x : ℝ => 1 - Real.cos (1 / x))
  rw [him] at h
  calc
    _ = ∫ x in Ioi (0 : ℝ), |-(x ^ 2)⁻¹| • (1 - Real.cos (1 / x⁻¹)) := h
    _ = ∫ x in Ioi (0 : ℝ), (1 - Real.cos x) / x ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      simp [abs_of_nonneg (inv_nonneg.mpr (sq_nonneg x)), smul_eq_mul,
        div_eq_mul_inv, mul_comm]
    _ = _ := integral_one_sub_cos_div_sq_Ioi

end RiemannResearch.Analysis
