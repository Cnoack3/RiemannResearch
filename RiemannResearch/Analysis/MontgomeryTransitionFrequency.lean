/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroLoglogRate
import RiemannResearch.Analysis.MontgomeryLoglogTransfer
import RiemannResearch.Analysis.MontgomeryHorizontalLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The transition of the raw Montgomery form factor

At phase frequency `(log log T + c) / 2`, the leading term of the complex
form factor tends to `exp (-c)`. The shrinking-frequency comparison carries
that value to the actual ordinates. The analytic input is the corrected
complex-zero estimate of Baluyot, Goldston, Suriajaya and Turnage-Butterbaugh,
equation (3.5) for positive ordinates up to T, https://arxiv.org/abs/2501.14545.
The theorem takes that estimate as an explicit hypothesis.
-/

noncomputable section
open Filter Set
open scoped Topology

namespace RiemannResearch.Analysis.MontgomeryHorizontalBessel
open ActualZeroOrdinate MontgomeryHorizontalTransfer MontgomeryFormFactor

/-- Normalized form of the corrected complex-zero estimate of Baluyot, Goldston,
Suriajaya and Turnage-Butterbaugh, equation (3.5) for the cutoff (0,T].
See https://arxiv.org/abs/2501.14545. The additive error survives normalization. -/
def CorrectedComplexFormFactorEstimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ α ∈ Icc (0 : ℝ) 1,
    let spike := Real.exp (-2 * (α * Real.log T)) * Real.log T
    |sharpFormFactor T α - (spike + α)| ≤ C * (spike + 1) / Real.sqrt (Real.log T)

/-- At this frequency the leading term of the complex form factor is exp(-c). -/
def transitionFrequency (c T : ℝ) : ℝ :=
  ((Real.log (Real.log T) + c) / 2) / Real.log T

private theorem transitionFrequency_mul_log (c T : ℝ) (hT : 1 < T) :
    transitionFrequency c T * Real.log T = (Real.log (Real.log T) + c) / 2 :=
  div_mul_cancel₀ _ (Real.log_pos hT).ne'

private theorem loglog_pow_div_log_tendsto_zero (n : ℕ) :
    Tendsto (fun T : ℝ => (Real.log (Real.log T)) ^ n / Real.log T) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
  apply h.congr'
  filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0] with T hT
  simp only [Function.comp_def, Real.exp_neg, Real.exp_log hT, div_eq_mul_inv]

private theorem transitionFrequency_tendsto_zero (c : ℝ) :
    Tendsto (transitionFrequency c) atTop (𝓝 0) := by
  have h := (((loglog_pow_div_log_tendsto_zero 1).add
    ((loglog_pow_div_log_tendsto_zero 0).const_mul c)).div_const 2)
  simpa only [mul_zero, zero_add, zero_div] using h.congr
    (fun T => by unfold transitionFrequency; simp only [pow_one, pow_zero]; ring)

private theorem transitionFrequency_rate (c : ℝ) :
    Tendsto (fun T => (transitionFrequency c T * Real.log T) ^ 2 * horizontalLogRate T)
      atTop (𝓝 0) := by
  have h := ((((loglog_pow_div_log_tendsto_zero 4).add
      ((loglog_pow_div_log_tendsto_zero 3).const_mul (2 * c))).add
      ((loglog_pow_div_log_tendsto_zero 2).const_mul (c ^ 2))).div_const 4)
  simp only [mul_zero, zero_add, zero_div] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  rw [transitionFrequency_mul_log c T hT]
  unfold horizontalLogRate
  ring

/-- The published complex-zero estimate is the sole analytic hypothesis for
this limit of the raw ordinates. The frequency tends to zero. -/
theorem raw_transition_limit_of_corrected_complex_estimate
    (hMT : CorrectedComplexFormFactorEstimate) (c : ℝ) :
    Tendsto (fun T => formFactor T (transitionFrequency c T)) atTop (𝓝 (Real.exp (-c))) := by
  obtain ⟨C, hC, hbound⟩ := hMT
  have ha := transitionFrequency_tendsto_zero c
  have herror : Tendsto (fun T => sharpFormFactor T (transitionFrequency c T) -
      (Real.exp (-c) + transitionFrequency c T)) atTop (𝓝 0) := by
    have hmajor : Tendsto (fun T => C * (Real.exp (-c) + 1) / Real.sqrt (Real.log T))
        atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)
    apply squeeze_zero_norm' _ hmajor
    filter_upwards [hbound, eventually_gt_atTop (1 : ℝ),
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (-c),
      ha.eventually_le_const (by norm_num : (0 : ℝ) < 1)] with T hb hT hl hα
    change -c ≤ Real.log (Real.log T) at hl
    have hL := Real.log_pos hT
    have ha0 : 0 ≤ transitionFrequency c T :=
      div_nonneg (div_nonneg (by linarith) (by norm_num)) hL.le
    have he : Real.exp (-2 * (transitionFrequency c T * Real.log T)) * Real.log T =
        Real.exp (-c) := by
      rw [transitionFrequency_mul_log c T hT,
        show -2 * ((Real.log (Real.log T) + c) / 2) = -c - Real.log (Real.log T) by ring,
        Real.exp_sub, Real.exp_log hL, div_mul_cancel₀ _ hL.ne']
    simpa only [Real.norm_eq_abs, he] using hb (transitionFrequency c T) ⟨ha0, hα⟩
  have hmain : Tendsto (fun T => Real.exp (-c) + transitionFrequency c T)
      atTop (𝓝 (Real.exp (-c))) := by
    simpa only [add_zero] using ha.const_add (Real.exp (-c))
  apply raw_limit_of_budget _ (Real.exp_pos _).le
    (horizontalBudget_div_height_tendsto_zero_of_loglog _ (transitionFrequency_rate c))
  simpa only [sub_add_cancel, zero_add] using herror.add hmain

end RiemannResearch.Analysis.MontgomeryHorizontalBessel
