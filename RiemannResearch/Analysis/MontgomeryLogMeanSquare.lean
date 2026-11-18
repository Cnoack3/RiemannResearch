/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The logarithmic mean square M₁ in BGSTB

The elementary M₁ estimate used between (3.4) and (3.5) in BGSTB,
https://arxiv.org/html/2501.14545v3#S3.E4. We give the exact two endpoints
and a uniform absolute error for the positive cutoff.
-/

noncomputable section
open MeasureTheory Set
namespace RiemannResearch.Analysis.MontgomeryLogMeanSquare

def logSquarePrimitive (y : ℝ) : ℝ :=
  y * (Real.log y ^ 2 - 2 * Real.log y + 2)

theorem shifted_log_continuousOn {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun t : ℝ => Real.log (t + 2)) (uIcc 0 T) := by
  apply (continuous_id.continuousOn.add continuousOn_const).log
  intro t ht
  rw [uIcc_of_le hT] at ht
  change t + 2 ≠ 0
  linarith [ht.1]

theorem shifted_log_hasDerivAt {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s : ℝ => Real.log (s + 2)) (t + 2)⁻¹ t := by
  have h : HasDerivAt (fun s : ℝ => s + 2) 1 t := (hasDerivAt_id t).add_const 2
  simpa only [one_div] using h.log (by linarith : t + 2 ≠ 0)

/-- Exact value of M₁ with the endpoint at t=0 retained. -/
theorem log_mean_square_eq {T : ℝ} (hT : 0 ≤ T) (x : ℝ) :
    (∫ t in (0 : ℝ)..T, (Real.log (t + 2) / x) ^ 2) =
      (logSquarePrimitive (T + 2) - logSquarePrimitive 2) / x ^ 2 := by
  simp_rw [div_pow]
  rw [intervalIntegral.integral_div]
  congr 1
  have hd (t : ℝ) (ht : t ∈ uIcc 0 T) :
      HasDerivAt (fun s : ℝ => logSquarePrimitive (s + 2)) (Real.log (t + 2) ^ 2) t := by
    rw [uIcc_of_le hT] at ht
    have h := shifted_log_hasDerivAt ht.1
    have hp := ((hasDerivAt_id t).add_const 2).mul (((h.pow 2).sub (h.const_mul 2)).add_const 2)
    have hn : t + 2 ≠ 0 := by linarith [ht.1]
    convert hp using 1 <;> first | rfl |
      (simp only [Pi.sub_apply, Pi.pow_apply, id_eq]; field_simp [hn]; ring)
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((shifted_log_continuousOn hT).pow 2).intervalIntegrable

private theorem log_first_moment {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, Real.log (t + 2)) = (T + 2) * Real.log (T + 2) - 2 * Real.log 2 - T := by
  let p := fun t : ℝ => (t + 2) * Real.log (t + 2) - t
  have hd (t : ℝ) (ht : t ∈ uIcc 0 T) : HasDerivAt p (Real.log (t + 2)) t := by
    rw [uIcc_of_le hT] at ht
    have h := (((hasDerivAt_id t).add_const 2).mul (shifted_log_hasDerivAt ht.1)).sub
      (hasDerivAt_id t)
    have hn : t + 2 ≠ 0 := by linarith [ht.1]
    convert h using 1 <;> first | rfl | (simp only [id_eq]; field_simp [hn]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (shifted_log_continuousOn hT).intervalIntegrable]
  dsimp [p]
  ring

/-- BGSTB's M₁ main term with the explicit constant 3 on every T ≥ 2. -/
theorem log_mean_square_error_le {T : ℝ} (hT : 2 ≤ T) (x : ℝ) :
    |(∫ t in (0 : ℝ)..T, (Real.log (t + 2) / x) ^ 2) - T * Real.log T ^ 2 / x ^ 2| ≤
      3 * T * Real.log T / x ^ 2 := by
  have ht : 0 ≤ T := by linarith
  have hL := Real.log_nonneg (show 1 ≤ T by linarith)
  have hc : IntervalIntegrable (fun t : ℝ => Real.log (t + 2)) volume 0 T :=
    (shifted_log_continuousOn ht).intervalIntegrable
  have hcs : IntervalIntegrable (fun t : ℝ => Real.log (t + 2) ^ 2) volume 0 T :=
    ((shifted_log_continuousOn ht).pow 2).intervalIntegrable
  have hl2 := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
  have hl21 : Real.log 2 ≤ 1 := by
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hL2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hT
  have hshift : Real.log (T + 2) ≤ Real.log T + Real.log 2 := by
    rw [← Real.log_mul (by linarith : T ≠ 0) (by norm_num)]
    exact Real.log_le_log (by linarith) (by linarith)
  have hu := intervalIntegral.integral_mono_on ht hcs
    (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => (Real.log T + Real.log 2) ^ 2) volume 0 T)
    (fun t ht' => (sq_le_sq₀ (Real.log_nonneg (by linarith [ht'.1])) (add_nonneg hL hl2)).mpr
      ((Real.log_le_log (by linarith [ht'.1]) (by linarith [ht'.2])).trans hshift))
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hu
  have hsq : (Real.log T + Real.log 2) ^ 2 ≤ Real.log T ^ 2 + 3 * Real.log T := by
    nlinarith only [mul_nonneg hL (sub_nonneg.mpr hl21), mul_nonneg hl2 (sub_nonneg.mpr hL2), hL]
  have hfirst : T * Real.log T - T ≤ ∫ t in (0 : ℝ)..T, Real.log (t + 2) := by
    rw [log_first_moment ht]
    have h1 := Real.log_le_log (by linarith : 0 < T) (show T ≤ T + 2 by linarith)
    have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (show 2 ≤ T + 2 by linarith)
    nlinarith only [mul_le_mul_of_nonneg_left h1 ht, h2]
  have hlo := intervalIntegral.integral_mono_on ht
    ((hc.const_mul (2 * Real.log T)).sub intervalIntegrable_const) hcs
    (fun t _ => show 2 * Real.log T * Real.log (t + 2) - Real.log T ^ 2 ≤ Real.log (t + 2) ^ 2 by
      nlinarith only [sq_nonneg (Real.log (t + 2) - Real.log T)])
  rw [intervalIntegral.integral_sub (hc.const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hlo
  simp only [sub_zero, smul_eq_mul] at hlo
  simp_rw [div_pow]
  rw [intervalIntegral.integral_div, ← sub_div, abs_div, abs_of_nonneg (sq_nonneg x)]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply abs_le.mpr
  constructor
  · have hscale := mul_le_mul_of_nonneg_left hfirst (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hL)
    nlinarith only [hlo, hscale, mul_nonneg ht hL]
  · nlinarith only [hu, mul_le_mul_of_nonneg_left hsq ht]

end RiemannResearch.Analysis.MontgomeryLogMeanSquare
