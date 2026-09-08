import RiemannResearch.RH.ParetoHiddenConditioning
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The rescaled hidden-noise profile

Analytic components of §6 of the noise-to-signal report: the derivative estimate,
the exact difference quotient, pointwise convergence, and an integrable majorant.
-/

open scoped BigOperators
open Filter MeasureTheory
namespace RiemannResearch.RH.Pareto
noncomputable section

def hiddenConditioningDerivative (x : ℝ) : ℝ :=
  (Real.exp x + 1 - x * Real.exp x) / (Real.exp x + 1)^2

def hiddenConditioningRescaled (n : ℕ) (x : ℝ) : ℝ :=
  (n : ℝ) / x * (hiddenConditioningProfile ((1 + 2 / (n : ℝ)) * x) -
    hiddenConditioningProfile x)

def hiddenConditioningIntegrand (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (x / (n : ℝ)) * hiddenConditioningRescaled n x ^ 2

theorem hiddenConditioningDerivative_abs_le {x : ℝ} (hx : 0 ≤ x) :
    |hiddenConditioningDerivative x| ≤ (1 + x) * Real.exp (-x) := by
  have he : 0 < Real.exp x := Real.exp_pos x
  have he1 : 0 < Real.exp x + 1 := by positivity
  have hsplit : hiddenConditioningDerivative x =
      1 / (Real.exp x + 1) - x * Real.exp x / (Real.exp x + 1)^2 := by
    unfold hiddenConditioningDerivative
    field_simp
    <;> ring
  have ha : 1 / (Real.exp x + 1) ≤ 1 / Real.exp x := by
    exact one_div_le_one_div_of_le he (by linarith)
  have hb : x * Real.exp x / (Real.exp x + 1)^2 ≤ x / Real.exp x := by
    apply (div_le_div_iff₀ (sq_pos_of_pos he1) he).2
    nlinarith [sq_nonneg (Real.exp x), mul_nonneg hx he.le]
  rw [hsplit]
  calc
    _ ≤ |1 / (Real.exp x + 1)| + |x * Real.exp x / (Real.exp x + 1)^2| := abs_sub _ _
    _ = 1 / (Real.exp x + 1) + x * Real.exp x / (Real.exp x + 1)^2 := by
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    _ ≤ 1 / Real.exp x + x / Real.exp x := add_le_add ha hb
    _ = _ := by rw [Real.exp_neg]; ring

theorem hiddenConditioningRescaled_tendsto {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => hiddenConditioningRescaled n x) atTop
      (nhds (2 * hiddenConditioningDerivative x)) := by
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hstep : Tendsto (fun n : ℕ => 2 * x / (n : ℝ)) atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [div_eq_mul_inv, mul_zero] using hi.const_mul (2 * x)
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      exact div_pos (by positivity) hn'
  have hderiv : HasDerivAt hiddenConditioningProfile (hiddenConditioningDerivative x) x :=
    hiddenConditioningProfile_hasDerivAt x
  have hs := (hderiv.tendsto_slope_zero_right.comp hstep).const_mul 2
  apply hs.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  change 2 * ((2 * x / (n : ℝ))⁻¹ *
    (hiddenConditioningProfile (x + 2 * x / (n : ℝ)) - hiddenConditioningProfile x)) = _
  unfold hiddenConditioningRescaled
  have he : x + 2 * x / (n : ℝ) = (1 + 2 / (n : ℝ)) * x := by ring
  rw [he]
  field_simp
  <;> ring

theorem hiddenConditioningIntegrand_tendsto {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => hiddenConditioningIntegrand n x) atTop
      (nhds (4 * hiddenConditioningDerivative x ^ 2)) := by
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have he : Tendsto (fun n : ℕ => Real.exp (x / (n : ℝ))) atTop (nhds 1) := by
    simpa only [div_eq_mul_inv, mul_zero, Real.exp_zero, Function.comp_def] using
      Real.continuous_exp.continuousAt.tendsto.comp (hi.const_mul x)
  have hh := he.mul ((hiddenConditioningRescaled_tendsto hx).pow 2)
  simpa only [hiddenConditioningIntegrand, mul_pow, one_mul, show (2 : ℝ)^2 = 4 by norm_num]
    using hh

/-- A uniform mean-value bound that retains the full profile difference. -/
theorem hiddenConditioningProfile_sub_bound {x r : ℝ}
    (hx : 0 ≤ x) (hr1 : 1 ≤ r) (hr3 : r ≤ 3) :
    |hiddenConditioningProfile (r * x) - hiddenConditioningProfile x| ≤
      (1 + 3 * x) * Real.exp (-x) * ((r - 1) * x) := by
  have hxrx : x ≤ r * x := by nlinarith
  have hb (y : ℝ) (hy : y ∈ Set.Ico x (r * x)) :
      ‖hiddenConditioningDerivative y‖ ≤ (1 + 3 * x) * Real.exp (-x) := by
    rw [Real.norm_eq_abs]
    calc
      _ ≤ (1 + y) * Real.exp (-y) := hiddenConditioningDerivative_abs_le (hx.trans hy.1)
      _ ≤ (1 + 3 * x) * Real.exp (-x) := by
        apply mul_le_mul
        · nlinarith [hy.2, mul_le_mul_of_nonneg_right hr3 hx]
        · exact Real.exp_le_exp.mpr (by linarith [hy.1])
        · exact (Real.exp_pos _).le
        · positivity
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := hiddenConditioningProfile) (f' := hiddenConditioningDerivative)
    (fun y _ => (hiddenConditioningProfile_hasDerivAt y).hasDerivWithinAt) hb (r * x)
    (show r * x ∈ Set.Icc x (r * x) from ⟨hxrx, le_rfl⟩)
  rw [Real.norm_eq_abs] at h
  convert h using 1 <;> ring

theorem hiddenConditioningRescaled_abs_le {n : ℕ} (hn : 1 ≤ n)
    {x : ℝ} (hx : 0 < x) :
    |hiddenConditioningRescaled n x| ≤ 2 * (1 + 3 * x) * Real.exp (-x) := by
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hr : 1 + 2 / (n : ℝ) ≤ 3 := by
    have h : 2 / (n : ℝ) ≤ 2 := (div_le_iff₀ hn0).2 (by linarith)
    linarith
  have h := hiddenConditioningProfile_sub_bound hx.le
    (show 1 ≤ 1 + 2 / (n : ℝ) from le_add_of_nonneg_right (by positivity)) hr
  unfold hiddenConditioningRescaled
  rw [abs_mul, abs_of_nonneg (div_nonneg hn0.le hx.le)]
  calc
    _ ≤ (n : ℝ) / x *
      ((1 + 3 * x) * Real.exp (-x) * (((1 + 2 / (n : ℝ)) - 1) * x)) :=
      mul_le_mul_of_nonneg_left h (div_nonneg hn0.le hx.le)
    _ = _ := by
      field_simp
      <;> ring

/-- A single exponentially decaying majorant works for every n ≥ 1. -/
theorem hiddenConditioningIntegrand_le {n : ℕ} (hn : 1 ≤ n)
    {x : ℝ} (hx : 0 < x) :
    |hiddenConditioningIntegrand n x| ≤ 4 * (1 + 3 * x)^2 * Real.exp (-x) := by
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hsq : hiddenConditioningRescaled n x ^ 2 ≤
      (2 * (1 + 3 * x) * Real.exp (-x))^2 := by
    apply sq_le_sq.mpr
    rw [abs_of_nonneg (show 0 ≤ 2 * (1 + 3 * x) * Real.exp (-x) by positivity)]
    exact hiddenConditioningRescaled_abs_le hn hx
  unfold hiddenConditioningIntegrand
  rw [abs_of_nonneg (by positivity)]
  calc
    _ ≤ Real.exp x * (2 * (1 + 3 * x) * Real.exp (-x))^2 := by
      apply mul_le_mul
      · apply Real.exp_le_exp.mpr
        exact (div_le_iff₀ hn0).2 (by nlinarith)
      · exact hsq
      · exact sq_nonneg _
      · exact (Real.exp_pos _).le
    _ = _ := by
      rw [Real.exp_neg]
      have he : Real.exp x ≠ 0 := ne_of_gt (Real.exp_pos x)
      field_simp
      <;> ring

theorem hiddenConditioning_majorant_integrable :
    IntegrableOn (fun x : ℝ => 4 * (1 + 3 * x)^2 * Real.exp (-x)) (Set.Ioi 0) := by
  have h0 : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Set.Ioi 0) := by
    simpa using (integrableOn_rpow_mul_exp_neg_rpow
      (s := (0 : ℝ)) (p := (1 : ℝ)) (by norm_num) (by norm_num))
  have h1 : IntegrableOn (fun x : ℝ => x * Real.exp (-x)) (Set.Ioi 0) := by
    simpa using (integrableOn_rpow_mul_exp_neg_rpow
      (s := (1 : ℝ)) (p := (1 : ℝ)) (by norm_num) (by norm_num))
  have h2 : IntegrableOn (fun x : ℝ => x^2 * Real.exp (-x)) (Set.Ioi 0) := by
    simpa only [Real.rpow_one, Real.rpow_two] using (integrableOn_rpow_mul_exp_neg_rpow
      (s := (2 : ℝ)) (p := (1 : ℝ)) (by norm_num) (by norm_num))
  have he : (fun x : ℝ => 4 * (1 + 3 * x)^2 * Real.exp (-x)) =
      (fun x => (4 * Real.exp (-x) + 24 * (x * Real.exp (-x))) +
        36 * (x^2 * Real.exp (-x))) := by funext x; ring
  rw [he]
  exact ((h0.const_mul 4).add (h1.const_mul 24)).add (h2.const_mul 36)

theorem hiddenConditioningIntegrand_measurable (n : ℕ) :
    Measurable (hiddenConditioningIntegrand n) := by
  have hp : Continuous hiddenConditioningProfile :=
    continuous_iff_continuousAt.mpr (fun x =>
      (hiddenConditioningProfile_hasDerivAt x).continuousAt)
  have hr : Measurable (hiddenConditioningRescaled n) := by
    unfold hiddenConditioningRescaled
    exact (measurable_const.div measurable_id).mul
      ((hp.measurable.comp (measurable_const.mul measurable_id)).sub hp.measurable)
  unfold hiddenConditioningIntegrand
  exact (Real.continuous_exp.measurable.comp
    (measurable_id.div measurable_const)).mul (hr.pow_const 2)

/-- Dominated convergence is discharged for the actual profile integrals.
The separate change of variables and the exact beta-integral constant are not
assumptions of this theorem. -/
theorem hiddenConditioning_integral_tendsto :
    Tendsto (fun n : ℕ => ∫ x : ℝ in Set.Ioi 0, hiddenConditioningIntegrand n x) atTop
      (nhds (4 * ∫ x : ℝ in Set.Ioi 0, hiddenConditioningDerivative x ^ 2)) := by
  have h : Tendsto
      (fun n : ℕ => ∫ x : ℝ in Set.Ioi 0, hiddenConditioningIntegrand n x) atTop
      (nhds (∫ x : ℝ in Set.Ioi 0, 4 * hiddenConditioningDerivative x ^ 2)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun x : ℝ => 4 * (1 + 3 * x)^2 * Real.exp (-x))
    · exact Filter.Eventually.of_forall (fun n =>
        (hiddenConditioningIntegrand_measurable n).aestronglyMeasurable)
    · filter_upwards [eventually_ge_atTop 1] with n hn
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      simpa only [Real.norm_eq_abs] using hiddenConditioningIntegrand_le hn hx
    · exact hiddenConditioning_majorant_integrable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact hiddenConditioningIntegrand_tendsto hx
  simpa only [integral_const_mul] using h

end
end RiemannResearch.RH.Pareto
