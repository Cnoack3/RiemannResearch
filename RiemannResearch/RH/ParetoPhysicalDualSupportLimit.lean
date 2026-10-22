import RiemannResearch.RH.ParetoPhysicalDualProjection
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Unconditional convergence of the actual physical-dual support approximation.
Source: user-provided support-error argument in the manuscript. -/
noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.CoefficientStabilization

theorem physical_support_log_budget_tendsto_zero :
    Tendsto (fun n : ℕ =>
      (2 * Real.log (((n + 1 : ℕ) : ℝ) + 1) ^ 2 + 1) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
  have hone : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have htwo : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 2))
      atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (s := 1) 2 (by norm_num)).tendsto_div_nhds_zero
    simp only [Real.rpow_two, Real.rpow_one] at h
    exact h.comp htwo
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hone
  have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h := ((hlog.const_mul 2).mul (hc.add hinv)).add hinv
  simp only [mul_zero, zero_mul, zero_add] at h
  apply h.congr'
  filter_upwards [] with n
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  push_cast
  field_simp [h1, h2]
  ring

theorem physicalDualProjectionResidual_norm_sq_tendsto_zero :
    Tendsto (fun n => ‖physicalDualProjectionResidual n‖ ^ 2) atTop (𝓝 0) := by
  exact squeeze_zero (fun n => sq_nonneg _) physicalDualProjectionResidual_log_bound
    physical_support_log_budget_tendsto_zero

theorem physicalDualProjectionResidual_norm_tendsto_zero :
    Tendsto (fun n => ‖physicalDualProjectionResidual n‖) atTop (𝓝 0) := by
  have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp
    physicalDualProjectionResidual_norm_sq_tendsto_zero
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using h

end RiemannResearch.RH.Pareto.CoefficientStabilization
