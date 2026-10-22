/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Elementary stretched exponential and logarithmic-product profiles

See `RH/MertensStretchedContinuation20260927.md` for the provider audit,
finite optimization, and scope of the result.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.Analysis

def logProductPower (β s : ℝ) : ℝ := (s * Real.log s) ^ β

theorem one_le_log_of_six_le {s : ℝ} (hs : 6 ≤ s) : 1 ≤ Real.log s := by
  have hhalf := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
  rw [Real.log_inv] at hhalf
  norm_num at hhalf
  have h4 := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (show (4 : ℝ) ≤ s by linarith)
  have he : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [he] at h4
  linarith

theorem logProductPower_mono (β : ℝ) (hβ : 0 ≤ β)
    {s T : ℝ} (hs : 1 ≤ s) (hsT : s ≤ T) :
    logProductPower β s ≤ logProductPower β T := by
  have hs0 : 0 < s := by linarith
  have hlog : Real.log s ≤ Real.log T := Real.log_le_log hs0 hsT
  apply Real.rpow_le_rpow (mul_nonneg hs0.le (Real.log_nonneg hs)) _ hβ
  exact mul_le_mul hsT hlog (Real.log_nonneg hs) (by linarith)

theorem logProductPower_lower (β : ℝ) (hβ : 0 ≤ β)
    {s : ℝ} (hs : 6 ≤ s) : s ^ β ≤ logProductPower β s := by
  have hs0 : 0 ≤ s := by linarith
  apply Real.rpow_le_rpow hs0 _ hβ
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_log_of_six_le hs) hs0

/-- The optimized profile divided by its argument decreases beyond six.
The proof only uses the tangent bound for log and 2*beta ≤ 1. -/
theorem logProductPower_div_antitone (β : ℝ) (hβ : 0 ≤ β) (hβ2 : 2 * β ≤ 1)
    {s T : ℝ} (hs : 6 ≤ s) (hsT : s ≤ T) :
    logProductPower β T / T ≤ logProductPower β s / s := by
  have hs0 : 0 < s := by linarith
  have hT0 : 0 < T := hs0.trans_le hsT
  have hls : 1 ≤ Real.log s := one_le_log_of_six_le hs
  have hlT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  let u : ℝ := T / s
  have hu1 : 1 ≤ u := (le_div_iff₀ hs0).mpr (by simpa using hsT)
  have hu0 : 0 < u := by linarith
  have huT : u * s = T := div_mul_cancel₀ _ hs0.ne'
  have hlogu := Real.log_le_sub_one_of_pos hu0
  have hlogT : Real.log T ≤ u * Real.log s := by
    have he : Real.log u = Real.log T - Real.log s := Real.log_div hT0.ne' hs0.ne'
    rw [he] at hlogu
    nlinarith [mul_nonneg (sub_nonneg.mpr hu1) (sub_nonneg.mpr hls)]
  have hprod : T * Real.log T ≤ u ^ 2 * (s * Real.log s) := by
    calc
      T * Real.log T ≤ T * (u * Real.log s) :=
        mul_le_mul_of_nonneg_left hlogT hT0.le
      _ = u ^ 2 * (s * Real.log s) := by rw [← huT]; ring
  have hpower : (u ^ 2) ^ β ≤ u := by
    calc
      (u ^ 2) ^ β = u ^ ((2 : ℝ) * β) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le]
        norm_num
      _ ≤ u ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hu1 hβ2
      _ = u := Real.rpow_one _
  have hphi : logProductPower β T ≤ u * logProductPower β s := by
    calc
      _ ≤ (u ^ 2 * (s * Real.log s)) ^ β :=
        Real.rpow_le_rpow (mul_nonneg hT0.le hlT) hprod hβ
      _ = (u ^ 2) ^ β * logProductPower β s := by
        rw [Real.mul_rpow (sq_nonneg u) (mul_nonneg hs0.le (by linarith : 0 ≤ Real.log s))]
        rfl
      _ ≤ u * logProductPower β s :=
        mul_le_mul_of_nonneg_right hpower
          (Real.rpow_nonneg (mul_nonneg hs0.le (by linarith : 0 ≤ Real.log s)) _)
  apply (div_le_div_iff₀ hT0 hs0).mpr
  have h := mul_le_mul_of_nonneg_right hphi hs0.le
  calc
    logProductPower β T * s ≤ (u * logProductPower β s) * s := h
    _ = logProductPower β s * T := by rw [← huT]; ring

theorem logProductPower_upper (β : ℝ) (hβ : 0 ≤ β)
    {s : ℝ} (hs : 6 ≤ s) : logProductPower β s ≤ s ^ (2 * β) := by
  have hs0 : 0 < s := by linarith
  have hls : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
  have hl : Real.log s ≤ s := by linarith [Real.log_le_sub_one_of_pos hs0]
  calc
    _ ≤ (s ^ 2) ^ β := Real.rpow_le_rpow (mul_nonneg hs0.le hls)
      (by nlinarith [mul_le_mul_of_nonneg_left hl hs0.le]) hβ
    _ = s ^ (2 * β) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs0.le]
      norm_num

theorem tendsto_logProductPower_atTop (β : ℝ) (hβ : 0 < β) :
    Tendsto (logProductPower β) atTop atTop := by
  have hp := tendsto_rpow_atTop hβ
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [tendsto_atTop.mp hp b, eventually_ge_atTop (6 : ℝ)] with s hb hs
  exact hb.trans (logProductPower_lower β hβ.le hs)

theorem tendsto_logProductPower_div_self (β : ℝ) (hβ : 0 ≤ β) (hβ2 : 2 * β < 1) :
    Tendsto (fun s : ℝ => logProductPower β s / s) atTop (𝓝 0) := by
  have hp : Tendsto (fun s : ℝ => s ^ (2 * β - 1)) atTop (𝓝 0) := by
    convert tendsto_rpow_neg_atTop (show 0 < 1 - 2 * β by linarith) using 1
    funext s
    congr 1
    ring
  apply squeeze_zero' _ _ hp
  · filter_upwards [eventually_ge_atTop (6 : ℝ)] with s hs
    have hs0 : 0 < s := by linarith
    exact div_nonneg (Real.rpow_nonneg
      (mul_nonneg hs0.le (Real.log_nonneg (by linarith))) _) hs0.le
  · filter_upwards [eventually_ge_atTop (6 : ℝ)] with s hs
    have hs0 : 0 < s := by linarith
    have h := div_le_div_of_nonneg_right (logProductPower_upper β hβ hs) hs0.le
    have he : s ^ (2 * β) / s = s ^ (2 * β - 1) := by
      rw [Real.rpow_sub hs0]
      simp only [Real.rpow_one]
    simpa only [he] using h

theorem logProductPower_band_shift_tendsto_zero
    (L δ : ℕ → ℝ) (hL : Tendsto L atTop atTop) (hδ : ∀ j, 0 ≤ δ j)
    (β c : ℝ) (hβ : 0 ≤ β) (hβ2 : 2 * β < 1)
    (hband : ∀ᶠ j in atTop, δ j * L j ≤ c * logProductPower β (L j)) :
    Tendsto δ atTop (𝓝 0) := by
  have hlim : Tendsto (fun j => c * (logProductPower β (L j) / L j)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using
      ((tendsto_logProductPower_div_self β hβ hβ2).comp hL).const_mul c
  apply squeeze_zero' (Eventually.of_forall hδ) _ hlim
  filter_upwards [hL.eventually (eventually_gt_atTop (0 : ℝ)), hband] with j hj hb
  have h := (le_div_iff₀ hj).mpr hb
  simpa only [mul_div_assoc] using h

/-- A fixed stretched exponential has a global inverse-square majorant.
The constant is explicit after choosing m with 2 ≤ beta*m: m!/a^m.
This is an elementary analytic estimate, with no arithmetic hypothesis. -/
theorem stretchedExp_le_inverse_square
    (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℝ, 1 ≤ s →
      Real.exp (-a * s ^ β) ≤ B / s ^ 2 := by
  obtain ⟨m, hm⟩ := exists_nat_gt (2 / β)
  have hmβ : (2 : ℝ) ≤ β * (m : ℝ) := by
    have h := (div_lt_iff₀ hβ).mp hm
    nlinarith
  refine ⟨(m.factorial : ℝ) / a ^ m, by positivity, fun s hs => ?_⟩
  have hs0 : 0 < s := by linarith
  have hp : s ^ 2 ≤ (s ^ β) ^ m := by
    calc
      s ^ 2 = s ^ (2 : ℝ) := by rw [Real.rpow_two]
      _ ≤ s ^ (β * (m : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hs hmβ
      _ = (s ^ β) ^ m := by rw [Real.rpow_mul hs0.le, Real.rpow_natCast]
  have ht : 0 ≤ a * s ^ β := mul_nonneg ha.le (Real.rpow_nonneg hs0.le _)
  have he := Real.pow_div_factorial_le_exp (a * s ^ β) ht m
  have hf : 0 < (m.factorial : ℝ) := by positivity
  have he' : (a * s ^ β) ^ m ≤ (m.factorial : ℝ) * Real.exp (a * s ^ β) := by
    have h := (div_le_iff₀ hf).mp he
    nlinarith
  have hb : a ^ m * s ^ 2 ≤ (m.factorial : ℝ) * Real.exp (a * s ^ β) := by
    calc
      a ^ m * s ^ 2 ≤ a ^ m * (s ^ β) ^ m :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = (a * s ^ β) ^ m := (mul_pow _ _ _).symm
      _ ≤ _ := he'
  rw [show -a * s ^ β = -(a * s ^ β) by ring, Real.exp_neg,
    inv_eq_one_div, div_div]
  exact (div_le_div_iff₀ (Real.exp_pos _) (by positivity)).mpr (by simpa using hb)

/-- A band at the terminal scale dominates every earlier scale when
the stretched-exponential exponent is at most one. -/
theorem linear_le_stretched_of_terminal_band
    (δ c β s T : ℝ) (hδ : 0 ≤ δ) (hc : 0 ≤ c)
    (hβ : β ≤ 1) (hs : 0 < s) (hsT : s ≤ T)
    (hband : δ * T ≤ c * T ^ β) :
    δ * s ≤ c * s ^ β := by
  have hT : 0 < T := hs.trans_le hsT
  have hδT : δ ≤ c * T ^ (β - 1) := by
    have h := (le_div_iff₀ hT).mpr hband
    have he : T ^ β / T = T ^ (β - 1) := by
      rw [Real.rpow_sub hT]
      simp only [Real.rpow_one]
    simpa only [mul_div_assoc, he] using h
  have hmono : T ^ (β - 1) ≤ s ^ (β - 1) :=
    Real.rpow_le_rpow_of_nonpos hs hsT (by linarith)
  have hδs : δ ≤ c * s ^ (β - 1) :=
    hδT.trans (mul_le_mul_of_nonneg_left hmono hc)
  have hm := mul_le_mul_of_nonneg_right hδs hs.le
  have he : s ^ (β - 1) * s = s ^ β := by
    calc
      s ^ (β - 1) * s = s ^ (β - 1) * s ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = s ^ ((β - 1) + 1) := (Real.rpow_add hs _ _).symm
      _ = s ^ β := by congr 1; ring
  simpa only [mul_assoc, he] using hm

end RiemannResearch.Analysis
