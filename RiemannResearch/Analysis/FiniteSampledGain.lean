/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteWeightedSampling
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Certified signed gains from finite weighted samples

Source: user-directed zero-phase sampling continuation, 21 October 2026;
independent elementary derivation of signed source and denominator certificates.
The intended RH consumer is a genuine new squarefree-legal direction screened
against the previous legal space in the complete Q metric.

The exact signed identity is retained before any estimate. A sampled source
produces a useful certificate only after subtracting a rigorous discrepancy
budget. Neither the existence of a positive margin nor its cofinal accumulation
is proved here. All finite weights represent the caller's complete objective.

-/
noncomputable section

namespace RiemannResearch.Analysis.FiniteSampledGain

open FiniteWeightedSampling

variable {α : Type*}

/-- Exact signed source error, allowing a change `u` in the old approximant.
True screening removes the last term exactly. -/
theorem shifted_source_error_exact (s : Finset α) (w q r u z : α → ℝ) :
    form s (fun a => w a * q a) (fun a => r a - u a) z - form s w r z =
      form s w (fun a => (q a - 1) * (r a - u a)) z - form s w u z := by
  have h := sampled_form_sub_exact s w q (fun a => r a - u a) z
  have htrue := form_sub_left s w r u z
  linarith

/-- If `u` lies in the old trial space and `z` is truly screened, their pairing
vanishes. Thus the sampled residual has precisely the same true source. -/
theorem screened_source_eq (s : Finset α) (w r u z : α → ℝ)
    (hscreen : form s w u z = 0) :
    form s w (fun a => r a - u a) z = form s w r z := by
  rw [form_sub_left, hscreen, sub_zero]

/-- The nonnegative sampled source margin is bounded by the true source. -/
theorem source_margin_le_abs {b sampledSource error : ℝ}
    (herror : |sampledSource - b| ≤ error) :
    max 0 (|sampledSource| - error) ≤ |b| := by
  have hupper : |sampledSource| ≤ error + |b| := by
    apply abs_le.mpr
    constructor
    · linarith [(abs_le.mp herror).1, neg_abs_le b]
    · linarith [(abs_le.mp herror).2, le_abs_self b]
  exact max_le (abs_nonneg b) (by linarith)


/-- Generic source-and-denominator certificate. The scale is normally `1-δ`.
Positivity of scale is needed for a positive certificate, not for this inequality.
-/
theorem gain_lower_bound_of_source_error
    {b sampledSource trueEnergy sampledEnergy error scale : ℝ}
    (henergy : 0 < trueEnergy) (hsampledEnergy : 0 < sampledEnergy)
    (herror : |sampledSource - b| ≤ error)
    (hcomparison : scale * trueEnergy ≤ sampledEnergy) :
    scale * (max 0 (|sampledSource| - error)) ^ 2 / sampledEnergy ≤
      b ^ 2 / trueEnergy := by
  have hmargin := source_margin_le_abs herror
  have hmargin_nonneg : 0 ≤ max 0 (|sampledSource| - error) := le_max_left _ _
  have hsquare : (max 0 (|sampledSource| - error)) ^ 2 ≤ b ^ 2 := by
    nlinarith [sq_abs b]
  apply (div_le_div_iff₀ hsampledEnergy henergy).2
  calc
    scale * (max 0 (|sampledSource| - error)) ^ 2 * trueEnergy =
        (max 0 (|sampledSource| - error)) ^ 2 * (scale * trueEnergy) := by ring
    _ ≤ (max 0 (|sampledSource| - error)) ^ 2 * sampledEnergy :=
      mul_le_mul_of_nonneg_left hcomparison (sq_nonneg _)
    _ ≤ b ^ 2 * sampledEnergy :=
      mul_le_mul_of_nonneg_right hsquare hsampledEnergy.le

/-- A square budget avoids introducing square roots into a finite certificate. -/
theorem abs_source_error_le_of_sq_budget
    {b sampledSource error discrepancy residualEnergy directionEnergy : ℝ}
    (herror : 0 ≤ error)
    (hform : (sampledSource - b) ^ 2 ≤
      discrepancy ^ 2 * residualEnergy * directionEnergy)
    (hbudget : discrepancy ^ 2 * residualEnergy * directionEnergy ≤ error ^ 2) :
    |sampledSource - b| ≤ error := by
  have hsquare : (sampledSource - b) ^ 2 ≤ error ^ 2 := hform.trans hbudget
  nlinarith [sq_abs (sampledSource - b), abs_nonneg (sampledSource - b)]

/-- Convert an entirely sampled squared budget to the true-metric budget.
The parameter `scale` is `1-δ`, which must be positive. -/
theorem true_budget_le_of_sampled_budget
    {scale discrepancy residualEnergy directionEnergy sampledResidual sampledDirection error : ℝ}
    (hscale : 0 < scale)
    (hresidual : 0 ≤ residualEnergy) (hdirection : 0 ≤ directionEnergy)
    (hresidualComparison : scale * residualEnergy ≤ sampledResidual)
    (hdirectionComparison : scale * directionEnergy ≤ sampledDirection)
    (hbudget : discrepancy ^ 2 * sampledResidual * sampledDirection ≤
      scale ^ 2 * error ^ 2) :
    discrepancy ^ 2 * residualEnergy * directionEnergy ≤ error ^ 2 := by
  have hsampledResidual : 0 ≤ sampledResidual :=
    (mul_nonneg hscale.le hresidual).trans hresidualComparison
  have hproduct := mul_le_mul hresidualComparison hdirectionComparison
    (mul_nonneg hscale.le hdirection) hsampledResidual
  have hweighted := mul_le_mul_of_nonneg_left hproduct (sq_nonneg discrepancy)
  have hscaleSquare : 0 < scale ^ 2 := sq_pos_of_pos hscale
  apply (mul_le_mul_iff_left₀ hscaleSquare).mp
  nlinarith [hweighted, hbudget]

/-- Complete finite-metric gain certificate from the true-energy error budget. -/
theorem sampled_gain_lower_bound (s : Finset α) (w q r z : α → ℝ)
    (δ error : ℝ) (hδ : δ < 1) (herror : 0 ≤ error)
    (hw : ∀ a ∈ s, 0 ≤ w a) (hq : ∀ a ∈ s, |q a - 1| ≤ δ)
    (hz : 0 < energy s w z)
    (hbudget : δ ^ 2 * energy s w r * energy s w z ≤ error ^ 2) :
    (1 - δ) * (max 0 (|form s (fun a => w a * q a) r z| - error)) ^ 2 /
        energy s (fun a => w a * q a) z ≤
      (form s w r z) ^ 2 / energy s w z := by
  have hcomparison := (sampled_energy_comparison s w q z δ hw hq).1
  have hsampledEnergy : 0 < energy s (fun a => w a * q a) z :=
    (mul_pos (sub_pos.mpr hδ) hz).trans_le hcomparison
  have hsource := abs_source_error_le_of_sq_budget herror
    (sampled_form_sub_sq_le s w q r z δ hw hq) hbudget
  exact gain_lower_bound_of_source_error hz hsampledEnergy hsource hcomparison

/-- Both the source and its error budget may be computed in the sampled metric.
Every infinite tail is retained when the finite weights are complete Q cells. -/
theorem sampled_gain_lower_bound_of_sampled_budget
    (s : Finset α) (w q r z : α → ℝ) (δ error : ℝ)
    (hδ : δ < 1) (herror : 0 ≤ error)
    (hw : ∀ a ∈ s, 0 ≤ w a) (hq : ∀ a ∈ s, |q a - 1| ≤ δ)
    (hz : 0 < energy s w z)
    (hbudget : δ ^ 2 * energy s (fun a => w a * q a) r *
        energy s (fun a => w a * q a) z ≤ (1 - δ) ^ 2 * error ^ 2) :
    (1 - δ) * (max 0 (|form s (fun a => w a * q a) r z| - error)) ^ 2 /
        energy s (fun a => w a * q a) z ≤
      (form s w r z) ^ 2 / energy s w z := by
  apply sampled_gain_lower_bound s w q r z δ error hδ herror hw hq hz
  exact true_budget_le_of_sampled_budget (sub_pos.mpr hδ)
    (energy_nonneg s w r hw) (energy_nonneg s w z hw)
    (sampled_energy_comparison s w q r δ hw hq).1
    (sampled_energy_comparison s w q z δ hw hq).1 hbudget

/-- If the direction is screened in the true metric, replacing the true old
optimizer by any other old-space approximant adds no source displacement error.
The finite sampling budget is applied to the actual sampled residual `r-u`.
-/
theorem screened_sampled_gain_lower_bound
    (s : Finset α) (w q r u z : α → ℝ) (δ error : ℝ)
    (hδ : δ < 1) (herror : 0 ≤ error)
    (hw : ∀ a ∈ s, 0 ≤ w a) (hq : ∀ a ∈ s, |q a - 1| ≤ δ)
    (hz : 0 < energy s w z) (hscreen : form s w u z = 0)
    (hbudget : δ ^ 2 * energy s (fun a => w a * q a) (fun a => r a - u a) *
        energy s (fun a => w a * q a) z ≤ (1 - δ) ^ 2 * error ^ 2) :
    (1 - δ) *
        (max 0 (|form s (fun a => w a * q a) (fun a => r a - u a) z| - error)) ^ 2 /
        energy s (fun a => w a * q a) z ≤
      (form s w r z) ^ 2 / energy s w z := by
  have h := sampled_gain_lower_bound_of_sampled_budget s w q
    (fun a => r a - u a) z δ error hδ herror hw hq hz hbudget
  rw [screened_source_eq s w r u z hscreen] at h
  exact h

end RiemannResearch.Analysis.FiniteSampledGain
