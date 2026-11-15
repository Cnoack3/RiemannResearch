/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Exact logarithmic integral and uncentered second-moment excess

Source for the intended Selberg application: Simonic, arXiv:1910.08274,
Corollary 6, https://arxiv.org/html/1910.08274v2 .
The direct elementary proof here uses log x <= x - 1 and retains the full
integrated nonnegative defect before deriving the inequality.

For f = zeta * M, a main-term-plus-error second moment controls the
logarithmic left boundary without an assumption about the signed linear
mean. It must not be mistaken for a centered error moment or for a bound
on the different quadratic detector 1 - (zeta * M - 1)^2.

Interval integrability remains explicit. Nonvanishing is required for
defect nonnegativity because Mathlib totalizes Real.log at zero.
-/

noncomputable section
open MeasureTheory

namespace Complex

/-- The exact residual between the quadratic upper bound and log norm. -/
def logSecondMomentDefect (z : ℂ) : ℝ :=
  (‖z‖ ^ 2 - 1) / 2 - Real.log ‖z‖

/-- Exact second-moment/logarithm identity with the full integrated defect. -/
theorem integral_log_norm_second_moment_exact
    {f : ℝ → ℂ} {H T : ℝ}
    (hlog : IntervalIntegrable (fun t => Real.log ‖f t‖) volume H T)
    (h2 : IntervalIntegrable (fun t => ‖f t‖ ^ 2) volume H T) :
    (∫ t in H..T, Real.log ‖f t‖) =
      ((∫ t in H..T, ‖f t‖ ^ 2) - (T - H)) / 2 -
        ∫ t in H..T, logSecondMomentDefect (f t) := by
  unfold logSecondMomentDefect
  rw [intervalIntegral.integral_sub
    ((h2.sub intervalIntegrable_const).div_const 2) hlog,
    intervalIntegral.integral_div,
    intervalIntegral.integral_sub h2 intervalIntegrable_const,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul, mul_one]
  ring


/-- Nonvanishing is essential because Real.log is totalized at zero. -/
theorem log_norm_le_half_sq_sub_one (z : ℂ) (hz : z ≠ 0) :
    Real.log ‖z‖ ≤ (‖z‖ ^ 2 - 1) / 2 := by
  have h := Real.log_le_sub_one_of_pos (sq_pos_of_pos (norm_pos_iff.mpr hz))
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith

theorem logSecondMomentDefect_nonneg (z : ℂ) (hz : z ≠ 0) :
    0 ≤ logSecondMomentDefect z :=
  sub_nonneg.mpr (log_norm_le_half_sq_sub_one z hz)

/-- Direct passage from an uncentered second moment to the left logarithmic
integral; the full interval-length main term is subtracted exactly. -/
theorem integral_log_norm_le_half_second_moment_excess
    {f : ℝ → ℂ} {H T : ℝ} (hHT : H ≤ T)
    (hne : ∀ t ∈ Set.Icc H T, f t ≠ 0)
    (hlog : IntervalIntegrable (fun t => Real.log ‖f t‖) volume H T)
    (h2 : IntervalIntegrable (fun t => ‖f t‖ ^ 2) volume H T) :
    (∫ t in H..T, Real.log ‖f t‖) ≤
      ((∫ t in H..T, ‖f t‖ ^ 2) - (T - H)) / 2 := by
  have hi : IntervalIntegrable (fun t => (‖f t‖ ^ 2 - 1) / 2) volume H T :=
    (h2.sub intervalIntegrable_const).div_const 2
  calc
    _ ≤ ∫ t in H..T, (‖f t‖ ^ 2 - 1) / 2 :=
      intervalIntegral.integral_mono_on hHT hlog hi
        (fun t ht => log_norm_le_half_sq_sub_one (f t) (hne t ht))
    _ = _ := by
      rw [intervalIntegral.integral_div,
        intervalIntegral.integral_sub h2 intervalIntegrable_const,
        intervalIntegral.integral_const]
      simp

/-- A main-term-plus-error second moment gives half that error in the
logarithmic integral, without assuming a centered moment or a linear mean. -/
theorem integral_log_norm_le_of_second_moment
    {f : ℝ → ℂ} {H T E : ℝ} (hHT : H ≤ T)
    (hne : ∀ t ∈ Set.Icc H T, f t ≠ 0)
    (hlog : IntervalIntegrable (fun t => Real.log ‖f t‖) volume H T)
    (h2 : IntervalIntegrable (fun t => ‖f t‖ ^ 2) volume H T)
    (hm : (∫ t in H..T, ‖f t‖ ^ 2) ≤ (T - H) + E) :
    (∫ t in H..T, Real.log ‖f t‖) ≤ E / 2 :=
  (integral_log_norm_le_half_second_moment_excess hHT hne hlog h2).trans (by linarith)

/-- The tangent defect at a positive mean-square scale A. Its integral
is retained exactly before the nonnegative defect is discarded in bounds. -/
noncomputable def scaledLogSecondMomentDefect (A : ℝ) (z : ℂ) : ℝ :=
  (‖z‖ ^ 2 / A - 1) / 2 + Real.log A / 2 - Real.log ‖z‖

theorem scaledLogSecondMomentDefect_nonneg {A : ℝ} (hA : 0 < A)
    (z : ℂ) (hz : z ≠ 0) : 0 ≤ scaledLogSecondMomentDefect A z := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h := Real.log_le_sub_one_of_pos (div_pos (sq_pos_of_pos hn) hA)
  rw [Real.log_div (ne_of_gt (sq_pos_of_pos hn)) (ne_of_gt hA), Real.log_pow] at h
  unfold scaledLogSecondMomentDefect
  norm_num only [Nat.cast_ofNat] at h
  linarith

/-- Exact scale-dependent logarithmic identity, including the full defect.
Setting A to one recovers the quadratic main-term subtraction. -/
theorem integral_log_norm_scaled_second_moment_exact
    {f : ℝ → ℂ} {H T : ℝ} (A : ℝ)
    (hlog : IntervalIntegrable (fun t => Real.log ‖f t‖) volume H T)
    (h2 : IntervalIntegrable (fun t => ‖f t‖ ^ 2) volume H T) :
    (∫ t in H..T, Real.log ‖f t‖) =
      (T - H) * Real.log A / 2 +
        ((∫ t in H..T, ‖f t‖ ^ 2) / A - (T - H)) / 2 -
          ∫ t in H..T, scaledLogSecondMomentDefect A (f t) := by
  unfold scaledLogSecondMomentDefect
  rw [intervalIntegral.integral_sub
    (((h2.div_const A).sub intervalIntegrable_const).div_const 2 |>.add
      intervalIntegrable_const) hlog,
    intervalIntegral.integral_add
      (((h2.div_const A).sub intervalIntegrable_const).div_const 2)
      intervalIntegrable_const,
    intervalIntegral.integral_div,
    intervalIntegral.integral_sub (h2.div_const A) intervalIntegrable_const,
    intervalIntegral.integral_div,
    intervalIntegral.integral_const, intervalIntegral.integral_const]
  simp only [smul_eq_mul, mul_one]
  ring

/-- A mean-square bound gives its logarithm, rather than its linear excess.
This is an analytic conversion; it does not supply the mean-square bound. -/
theorem integral_log_norm_le_of_mean_square_bound
    {f : ℝ → ℂ} {H T A : ℝ} (hHT : H ≤ T) (hA : 0 < A)
    (hne : ∀ t ∈ Set.Icc H T, f t ≠ 0)
    (hlog : IntervalIntegrable (fun t => Real.log ‖f t‖) volume H T)
    (h2 : IntervalIntegrable (fun t => ‖f t‖ ^ 2) volume H T)
    (hm : (∫ t in H..T, ‖f t‖ ^ 2) ≤ (T - H) * A) :
    (∫ t in H..T, Real.log ‖f t‖) ≤ (T - H) * Real.log A / 2 := by
  have hdi : IntervalIntegrable (fun t => scaledLogSecondMomentDefect A (f t)) volume H T :=
    ((((h2.div_const A).sub intervalIntegrable_const).div_const 2).add
      intervalIntegrable_const).sub hlog
  have hd : 0 ≤ ∫ t in H..T, scaledLogSecondMomentDefect A (f t) := by
    have hh := intervalIntegral.integral_mono_on hHT
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume H T) hdi
      (fun t ht => scaledLogSecondMomentDefect_nonneg hA (f t) (hne t ht))
    simpa using hh
  have hm' : (∫ t in H..T, ‖f t‖ ^ 2) / A ≤ T - H :=
    (div_le_iff₀ hA).mpr hm
  rw [integral_log_norm_scaled_second_moment_exact A hlog h2]
  linarith

end Complex

#print axioms Complex.integral_log_norm_second_moment_exact
