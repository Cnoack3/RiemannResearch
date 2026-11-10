/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MontgomeryHorizontalBessel
import Mathlib.Topology.Algebra.Order.Field
/-! # Horizontal budget criteria for raw Montgomery form factors
These are conditional transfer theorems. Vanishing of the actual one-point
budget is an explicit hypothesis, not a proved zero-density statement.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryHorizontalBessel
open MontgomeryHorizontalTransfer MontgomeryFormFactor

theorem horizontalDefect_nonneg {T : ℝ} (hT : 1 < T) (α : ℝ) :
    0 ≤ horizontalDefect T α := by
  have ht : 0 < T := by linarith
  have hl : 0 < Real.log T := Real.log_pos hT
  unfold horizontalDefect defectIntegral
  exact div_nonneg (integral_nonneg (fun s => by positivity)) (by positivity)

theorem horizontalDefect_tendsto_zero (α : ℝ → ℝ)
    (hbudget : Tendsto (fun T => horizontalBudget T (α T * Real.log T) / T)
      atTop (nhds 0)) :
    Tendsto (fun T => horizontalDefect T (α T)) atTop (nhds 0) := by
  obtain ⟨C,hC,hbound⟩ := exists_horizontalDefect_le_budget
  have hb : Tendsto (fun T => C*horizontalBudget T (α T * Real.log T) / T)
      atTop (nhds 0) := by
    simpa only [mul_zero, mul_div_assoc] using hbudget.const_mul C
  apply squeeze_zero' ?_ ?_ hb
  · filter_upwards [eventually_ge_atTop (9 : ℝ)] with T hT
    exact horizontalDefect_nonneg (by linarith) _
  · filter_upwards [eventually_ge_atTop (9 : ℝ)] with T hT
    exact hbound T (α T) hT

theorem sqrt_horizontal_difference_tendsto_zero (α : ℝ → ℝ)
    (hbudget : Tendsto (fun T => horizontalBudget T (α T * Real.log T) / T)
      atTop (nhds 0)) :
    Tendsto (fun T => |Real.sqrt (sharpFormFactor T (α T))-
      Real.sqrt (formFactor T (α T))|) atTop (nhds 0) := by
  have hh := (Real.continuous_sqrt.tendsto 0).comp
    (horizontalDefect_tendsto_zero α hbudget)
  simp only [Real.sqrt_zero] at hh
  exact squeeze_zero (fun T => abs_nonneg _) (fun T => sqrt_horizontal_error T (α T)) hh

/-- A vanishing horizontal budget transfers any nonnegative finite complex
form-factor limit, at fixed or varying frequencies, to the actual raw pairs. -/
theorem raw_limit_of_budget (α : ℝ → ℝ) {l : ℝ} (hl : 0 ≤ l)
    (hbudget : Tendsto (fun T => horizontalBudget T (α T * Real.log T) / T)
      atTop (nhds 0))
    (hsharp : Tendsto (fun T => sharpFormFactor T (α T)) atTop (nhds l)) :
    Tendsto (fun T => formFactor T (α T)) atTop (nhds l) := by
  have hh := (Real.continuous_sqrt.tendsto 0).comp
    (horizontalDefect_tendsto_zero α hbudget)
  simp only [Real.sqrt_zero] at hh
  have hs := (Real.continuous_sqrt.tendsto l).comp hsharp
  have hr : Tendsto (fun T => Real.sqrt (formFactor T (α T)))
      atTop (nhds (Real.sqrt l)) := by
    have hlow := hs.sub hh
    have hupp := hs.add hh
    simp only [sub_zero, add_zero] at hlow hupp
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hupp
    · intro T
      have h := (abs_le.mp (sqrt_horizontal_error T (α T))).2
      change Real.sqrt (sharpFormFactor T (α T)) - Real.sqrt (horizontalDefect T (α T)) ≤
        Real.sqrt (formFactor T (α T))
      linarith
    · intro T
      have h := (abs_le.mp (sqrt_horizontal_error T (α T))).1
      change Real.sqrt (formFactor T (α T)) ≤ Real.sqrt (sharpFormFactor T (α T)) +
        Real.sqrt (horizontalDefect T (α T))
      linarith
  have hp := hr.pow 2
  rw [Real.sq_sqrt hl] at hp
  apply hp.congr'
  filter_upwards [eventually_ge_atTop (9 : ℝ)] with T hT
  exact Real.sq_sqrt (formFactor_nonneg (by linarith) (α T))

/-- A fixed-window exponential-moment hypothesis suffices for moving-frequency
transfer. Both analytic asymptotic inputs remain explicit. -/
theorem raw_limit_of_exponentialMoment (α : ℝ → ℝ) (A : ℝ)
    (hα : ∀ᶠ T in atTop, |α T| ≤ A) {l : ℝ} (hl : 0 ≤ l)
    (hmoment : Tendsto (fun T =>
      (1+(A*Real.log T)^2)*exponentialMoment T (A*Real.log T) / T) atTop (nhds 0))
    (hsharp : Tendsto (fun T => sharpFormFactor T (α T)) atTop (nhds l)) :
    Tendsto (fun T => formFactor T (α T)) atTop (nhds l) := by
  apply raw_limit_of_budget α hl ?_ hsharp
  apply squeeze_zero' ?_ ?_ hmoment
  · filter_upwards [eventually_ge_atTop (9 : ℝ)] with T hT
    exact div_nonneg (horizontalBudget_nonneg _ _) (by linarith)
  · filter_upwards [eventually_ge_atTop (9 : ℝ), hα] with T hT ha
    have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    have hu : |α T * Real.log T| ≤ A*Real.log T := by
      rw [abs_mul, abs_of_nonneg hlog]
      exact mul_le_mul_of_nonneg_right ha hlog
    exact div_le_div_of_nonneg_right (horizontalBudget_le_exponentialMoment T _ _ hu)
      (by linarith)

end RiemannResearch.Analysis.MontgomeryHorizontalBessel
