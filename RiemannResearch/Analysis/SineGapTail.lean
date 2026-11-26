import RiemannResearch.Analysis.MontgomeryPositiveGapDensity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The oscillatory correction to the integrated sine-square kernel on a
positive ray. Integration by parts exposes the endpoint and an absolutely
integrable reciprocal-cube remainder. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace RiemannResearch.Analysis.SineGapTail

/-- The exact endpoint term and reciprocal-cube correction. -/
theorem sinc_sq_tail_parts {q : ℝ} (hq : 0 < q) :
    (∫ x in Ioi q, Real.sinc (Real.pi*x)^2) - 1/(2*Real.pi^2*q) =
      1/(2*Real.pi^2) * (Real.sin (2*Real.pi*q)/(2*Real.pi*q^2) -
        (2/(2*Real.pi)) * ∫ x in Ioi q, Real.sin (2*Real.pi*x) / x^3) := by
  let a := 2*Real.pi
  have ha : 0 < a := by positivity
  let c := fun x : ℝ => Real.cos (a*x) / x^2
  let s := fun x : ℝ => Real.sin (a*x) / x^3
  let F := fun x : ℝ => Real.sin (a*x) / (a*x^2)
  have hi2 : IntegrableOn (fun x : ℝ => (x^2)⁻¹) (Ioi q) := by
    simpa using integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hq
  have hi3 : IntegrableOn (fun x : ℝ => (x^3)⁻¹) (Ioi q) := by
    simpa using integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hq
  have hc : IntegrableOn c (Ioi q) := by
    refine hi2.mono' ((Real.measurable_cos.comp (measurable_const.mul measurable_id)).div
      (measurable_id.pow_const 2)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    change ‖Real.cos (a*x)/x^2‖ ≤ (x^2)⁻¹
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg x), ← one_div]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (sq_nonneg _)
  have hs : IntegrableOn s (Ioi q) := by
    refine hi3.mono' ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).div
      (measurable_id.pow_const 3)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    have hx' : 0 < x := hq.trans hx
    change ‖Real.sin (a*x)/x^3‖ ≤ (x^3)⁻¹
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hx' 3), ← one_div]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (pow_pos hx' 3).le
  have hd (x : ℝ) (hx : x ∈ Ici q) : HasDerivAt F (c x - (2/a)*s x) x := by
    have hx' : 0 < x := hq.trans_le hx
    have h1 := ((hasDerivAt_id x).const_mul a).sin
    have h2 := ((hasDerivAt_id x).pow 2).const_mul a
    have hdv := h1.fun_div h2 (mul_ne_zero ha.ne' (pow_ne_zero 2 hx'.ne'))
    apply hdv.congr_deriv
    dsimp [c, s, id]
    field_simp [ha.ne', hx'.ne'] <;> ring
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hmaj : Tendsto (fun x : ℝ => (1/a) * (x⁻¹)^2) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.pow 2).const_mul (1/a)
    apply squeeze_zero_norm' _ hmaj
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    change |Real.sin (a*x) / (a*x^2)| ≤ _
    rw [abs_div, abs_of_pos (mul_pos ha (sq_pos_of_pos hx))]
    calc
      _ ≤ 1 / (a*x^2) := div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)
      _ = _ := by field_simp [ha.ne', hx.ne'] <;> ring
  have hpart := integral_Ioi_of_hasDerivAt_of_tendsto' hd (hc.sub (hs.const_mul (2/a))) hlim
  rw [integral_sub hc (hs.const_mul (2/a)), integral_const_mul, zero_sub] at hpart
  have hinv : (∫ x in Ioi q, (x^2)⁻¹) = q⁻¹ := by
    have h := integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hq
    rw [show (-2 : ℝ) + 1 = -1 by norm_num] at h
    simpa [Real.rpow_neg hq.le] using h
  have he : (∫ x in Ioi q, Real.sinc (Real.pi*x)^2) =
      ∫ x in Ioi q, 1/(2*Real.pi^2) * ((x^2)⁻¹ - c x) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx' : 0 < x := hq.trans hx
    dsimp only [c, a]
    rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hx'.ne'),
      show 2 * Real.pi * x = 2 * (Real.pi * x) by ring, Real.cos_two_mul_eq_one_sub]
    field_simp [Real.pi_ne_zero, hx'.ne'] <;> ring
  rw [he, integral_const_mul, integral_sub hi2 hc, hinv]
  change _ = 1/(2*Real.pi^2) * (F q - (2/a) * ∫ x in Ioi q, s x)
  have hcval : (∫ x in Ioi q, c x) = -F q + (2/a) * ∫ x in Ioi q, s x := by linarith only [hpart]
  rw [hcval]
  ring

/-- Quantitative reciprocal-square error in the sine-kernel tail for every
strictly positive threshold. -/
theorem sinc_sq_tail_error_le {q : ℝ} (hq : 0 < q) :
    |(∫ x in Ioi q, Real.sinc (Real.pi*x)^2) - 1/(2*Real.pi^2*q)| ≤ 1/(2*Real.pi^3*q^2) := by
  let a := 2*Real.pi
  have ha : 0 < a := by positivity
  have hi3 : IntegrableOn (fun x : ℝ => (x^3)⁻¹) (Ioi q) := by
    simpa using integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hq
  have hm : ∀ᵐ x ∂volume.restrict (Ioi q), ‖Real.sin (a*x) / x^3‖ ≤ (x^3)⁻¹ := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    have hx' : 0 < x := hq.trans hx
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hx' 3), ← one_div]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (pow_pos hx' 3).le
  have hb := norm_integral_le_of_norm_le hi3 hm
  have h3 := integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hq
  rw [show (-3 : ℝ) + 1 = -2 by norm_num] at h3
  have he : (∫ x in Ioi q, (x^3)⁻¹) = 1/(2*q^2) := by
    have h3' : (∫ x in Ioi q, (x^3)⁻¹) = -(q^2)⁻¹ / (-2) := by simpa using h3
    rw [h3']
    ring
  rw [Real.norm_eq_abs, he] at hb
  rw [sinc_sq_tail_parts hq, abs_mul, abs_of_pos (by positivity : 0 < 1/(2*Real.pi^2))]
  change (1/(2*Real.pi^2)) * |Real.sin (a*q)/(a*q^2) - (2/a) *
    ∫ x in Ioi q, Real.sin (a*x)/x^3| ≤ _
  have h1 : |Real.sin (a*q)/(a*q^2)| ≤ 1/(a*q^2) := by
    rw [abs_div, abs_of_pos (mul_pos ha (sq_pos_of_pos hq))]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)
  have h2 := abs_sub (Real.sin (a*q)/(a*q^2)) ((2/a)*(∫ x in Ioi q, Real.sin (a*x)/x^3))
  rw [abs_mul, abs_of_pos (div_pos (by norm_num : (0:ℝ)<2) ha)] at h2
  calc
    _ ≤ 1/(2*Real.pi^2) * (1/(a*q^2) + (2/a) * (1/(2*q^2))) :=
      mul_le_mul_of_nonneg_left (h2.trans (add_le_add h1
        (mul_le_mul_of_nonneg_left hb (by positivity)))) (by positivity)
    _ = _ := by dsimp [a]; field_simp [Real.pi_ne_zero, hq.ne']; ring

end RiemannResearch.Analysis.SineGapTail
