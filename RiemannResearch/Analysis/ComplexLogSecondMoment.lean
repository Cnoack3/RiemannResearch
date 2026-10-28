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

end Complex

#print axioms Complex.integral_log_norm_second_moment_exact
