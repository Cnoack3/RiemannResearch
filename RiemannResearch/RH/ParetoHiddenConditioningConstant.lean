import RiemannResearch.RH.ParetoHiddenConditioningSubstitution
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Exact reduction of the limiting constant to the Fermi integral

An explicit primitive replaces differentiation of the beta integral.  Every
boundary value and integrability statement in the reduction is proved.
-/

open scoped BigOperators
open Filter MeasureTheory
namespace RiemannResearch.RH.Pareto
noncomputable section

def hiddenFermiWeight (x : ℝ) : ℝ := 1 / (Real.exp x + 1)

theorem hiddenFermiWeight_hasDerivAt (x : ℝ) :
    HasDerivAt hiddenFermiWeight
      (hiddenFermiWeight x ^ 2 - hiddenFermiWeight x) x := by
  have h := ((Real.hasDerivAt_exp x).add_const 1).inv
    (show Real.exp x + 1 ≠ 0 by positivity)
  convert h using 1 <;>
    first
    | rfl
    | (funext y; simp [hiddenFermiWeight, one_div])
    | (unfold hiddenFermiWeight; field_simp <;> ring)

theorem hiddenConditioningDerivative_eq_fermi (x : ℝ) :
    hiddenConditioningDerivative x = hiddenFermiWeight x +
      x * (hiddenFermiWeight x ^ 2 - hiddenFermiWeight x) := by
  unfold hiddenConditioningDerivative hiddenFermiWeight
  field_simp
  <;> ring

def hiddenConditioningPrimitive (x : ℝ) : ℝ :=
  ((2 / 3 : ℝ) * x - (1 / 2 : ℝ) * x ^ 2) * hiddenFermiWeight x ^ 2 +
    ((1 / 3 : ℝ) * x ^ 2) * hiddenFermiWeight x ^ 3 +
    ((1 / 3 : ℝ) * (x + 1)) * hiddenFermiWeight x

theorem hiddenConditioningPrimitive_hasDerivAt (x : ℝ) :
    HasDerivAt hiddenConditioningPrimitive
      (hiddenConditioningDerivative x ^ 2 - hiddenConditioningProfile x / 3) x := by
  have hg := hiddenFermiWeight_hasDerivAt x
  have h1 : HasDerivAt (fun y : ℝ => (2 / 3 : ℝ) * y - (1 / 2 : ℝ) * y^2)
      ((2 / 3 : ℝ) - x) x := by
    exact (((hasDerivAt_id x).const_mul (2 / 3 : ℝ)).sub
      (((hasDerivAt_id x).pow 2).const_mul (1 / 2 : ℝ))).congr_deriv (by simp only [id_eq]; ring)
  have h2 : HasDerivAt (fun y : ℝ => (1 / 3 : ℝ) * y^2) ((2 / 3 : ℝ) * x) x := by
    exact (((hasDerivAt_id x).pow 2).const_mul (1 / 3 : ℝ)).congr_deriv
      (by simp only [id_eq]; ring)
  have h3 : HasDerivAt (fun y : ℝ => (1 / 3 : ℝ) * (y + 1)) (1 / 3 : ℝ) x := by
    simpa using ((hasDerivAt_id x).add_const 1).const_mul (1 / 3 : ℝ)
  have h := ((h1.mul (hg.pow 2)).add (h2.mul (hg.pow 3))).add (h3.mul hg)
  apply h.congr_deriv
  rw [hiddenConditioningDerivative_eq_fermi]
  have hp : hiddenConditioningProfile x = x * hiddenFermiWeight x := by
    simp [hiddenConditioningProfile, hiddenFermiWeight, div_eq_mul_inv]
  rw [hp]
  simp only [Pi.pow_apply]
  ring

theorem hiddenConditioningPrimitive_zero : hiddenConditioningPrimitive 0 = 1 / 6 := by
  norm_num [hiddenConditioningPrimitive, hiddenFermiWeight]

theorem hiddenConditioningPrimitive_tendsto_zero :
    Tendsto hiddenConditioningPrimitive atTop (nhds 0) := by
  have hh (k : ℕ) : Tendsto (fun x : ℝ => x^k * hiddenFermiWeight x) atTop (nhds 0) := by
    simpa [hiddenFermiWeight, div_eq_mul_inv] using
      Real.tendsto_div_pow_mul_exp_add_atTop 1 1 k (by norm_num)
  have hg : Tendsto hiddenFermiWeight atTop (nhds 0) := by simpa using hh 0
  have h1 : Tendsto (fun x : ℝ => x * hiddenFermiWeight x) atTop (nhds 0) := by
    simpa using hh 1
  have h2 := hh 2
  have h := (((((h1.mul hg).const_mul (2 / 3 : ℝ)).sub
    ((h2.mul hg).const_mul (1 / 2 : ℝ))).add
    ((h2.mul (hg.pow 2)).const_mul (1 / 3 : ℝ))).add
    (h1.const_mul (1 / 3 : ℝ))).add (hg.const_mul (1 / 3 : ℝ))
  have he : hiddenConditioningPrimitive = fun x : ℝ =>
      (((((2 / 3 : ℝ) * ((x * hiddenFermiWeight x) * hiddenFermiWeight x)) -
       ((1 / 2 : ℝ) * ((x^2 * hiddenFermiWeight x) * hiddenFermiWeight x))) +
       ((1 / 3 : ℝ) * ((x^2 * hiddenFermiWeight x) * hiddenFermiWeight x^2))) +
       ((1 / 3 : ℝ) * (x * hiddenFermiWeight x))) +
       ((1 / 3 : ℝ) * hiddenFermiWeight x) := by
    funext x
    unfold hiddenConditioningPrimitive
    ring
  rw [he]
  simpa using h

theorem hiddenConditioningProfile_integrable :
    IntegrableOn hiddenConditioningProfile (Set.Ioi 0) := by
  have hi : IntegrableOn (fun x : ℝ => x * Real.exp (-x)) (Set.Ioi 0) := by
    simpa using (integrableOn_rpow_mul_exp_neg_rpow
      (s := (1 : ℝ)) (p := (1 : ℝ)) (by norm_num) (by norm_num))
  have hc : Continuous hiddenConditioningProfile := continuous_iff_continuousAt.mpr
    (fun x => (hiddenConditioningProfile_hasDerivAt x).continuousAt)
  apply hi.mono' hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change 0 < x at hx
  rw [Real.norm_eq_abs, hiddenConditioningProfile, abs_of_nonneg (by positivity)]
  have hd : 1 / (Real.exp x + 1) ≤ 1 / Real.exp x :=
    one_div_le_one_div_of_le (Real.exp_pos x) (by linarith [Real.exp_pos x])
  rw [Real.exp_neg]
  simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hd hx.le

theorem hiddenConditioningDerivative_sq_integrable :
    IntegrableOn (fun x : ℝ => hiddenConditioningDerivative x ^ 2) (Set.Ioi 0) := by
  have hc : Continuous hiddenConditioningDerivative := by
    unfold hiddenConditioningDerivative
    exact (((Real.continuous_exp.add continuous_const).sub
      (continuous_id.mul Real.continuous_exp)).div
      ((Real.continuous_exp.add continuous_const).pow 2) (fun x => by positivity))
  apply hiddenConditioning_majorant_integrable.mono' (hc.pow 2).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change 0 < x at hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have he : 0 ≤ Real.exp (-x) := (Real.exp_pos _).le
  have he1 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hsq : hiddenConditioningDerivative x ^ 2 ≤ ((1 + x) * Real.exp (-x))^2 := by
    apply sq_le_sq.mpr
    rw [abs_of_nonneg (show 0 ≤ (1 + x) * Real.exp (-x) by positivity)]
    exact hiddenConditioningDerivative_abs_le hx.le
  have hp : (1 + x)^2 ≤ 4 * (1 + 3 * x)^2 := by nlinarith
  have hq : Real.exp (-x)^2 ≤ Real.exp (-x) := by nlinarith
  calc
    _ ≤ ((1 + x) * Real.exp (-x))^2 := hsq
    _ = (1 + x)^2 * Real.exp (-x)^2 := by ring
    _ ≤ (4 * (1 + 3 * x)^2) * Real.exp (-x) :=
      mul_le_mul hp hq (sq_nonneg _) (by positivity)
    _ = _ := by ring

/-- Exact evaluation of the derivative energy in terms of one Fermi integral.
The boundary contribution 1/6 is retained explicitly. -/
theorem hiddenConditioning_derivative_energy_eq_fermi :
    (∫ x : ℝ in Set.Ioi 0, hiddenConditioningDerivative x ^ 2) =
      (∫ x : ℝ in Set.Ioi 0, hiddenConditioningProfile x) / 3 - 1 / 6 := by
  have hi := hiddenConditioningDerivative_sq_integrable.sub
    (hiddenConditioningProfile_integrable.div_const 3)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x _ => hiddenConditioningPrimitive_hasDerivAt x) hi
    hiddenConditioningPrimitive_tendsto_zero
  rw [hiddenConditioningPrimitive_zero] at h
  rw [integral_sub hiddenConditioningDerivative_sq_integrable
    (hiddenConditioningProfile_integrable.div_const 3), integral_div] at h
  linarith

end
end RiemannResearch.RH.Pareto
