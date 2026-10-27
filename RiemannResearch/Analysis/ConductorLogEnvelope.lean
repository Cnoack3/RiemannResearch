/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scalar envelopes for a large conductor

Source: the final uniform-in-conductor step of
`SingleConductorProjectionBound.md`. All estimates are deterministic.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.Analysis.ConductorLogEnvelope

theorem two_add_log_sq_div_le_four (x : ℝ) (hx : 1 ≤ x) :
    (2 + Real.log x) ^ 2 / x ≤ 4 := by
  have hxp : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxp
  have hlog := Real.log_le_sub_one_of_pos hs
  have he : Real.log x = 2 * Real.log (Real.sqrt x) := by
    calc
      _ = Real.log ((Real.sqrt x) ^ 2) := congrArg Real.log (Real.sq_sqrt hxp.le).symm
      _ = _ := by rw [Real.log_pow]; norm_num
  have hlo : 0 ≤ 2 + Real.log x := by linarith [Real.log_nonneg hx]
  have hupper : 2 + Real.log x ≤ 2 * Real.sqrt x := by rw [he]; linarith
  have hsq := (sq_le_sq₀ hlo (by positivity : 0 ≤ 2 * Real.sqrt x)).mpr hupper
  have hbound : (2 + Real.log x) ^ 2 ≤ 4 * x := by
    nlinarith [Real.sq_sqrt hxp.le]
  exact (div_le_iff₀ hxp).mpr hbound

theorem two_add_log_mul_ratio_le (x y : ℝ) (hy : 1 ≤ y) (hyx : y ≤ x) :
    (2 + Real.log x) * (y / x) ≤ 2 + Real.log y := by
  have hyp : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hxp : 0 < x := hyp.trans_le hyx
  have hratio := Real.log_le_sub_one_of_pos (div_pos hxp hyp)
  rw [Real.log_div hxp.ne' hyp.ne'] at hratio
  have hm := mul_le_mul_of_nonneg_right hratio hyp.le
  have he : (x / y - 1) * y = x - y := by field_simp
  rw [he] at hm
  have hprod : 0 ≤ (1 + Real.log y) * (x - y) :=
    mul_nonneg (by linarith [Real.log_nonneg hy]) (sub_nonneg.mpr hyx)
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hxp).mpr
  nlinarith

theorem shifted_log_power_div_sqrt_tendsto_zero (m : ℕ) :
    Tendsto (fun d : ℕ => (6 + Real.log ((d : ℝ) + 1)) ^ m /
      Real.sqrt (d : ℝ)) atTop (𝓝 0) := by
  have hreal : Tendsto (fun x : ℝ => Real.log x ^ m / Real.sqrt x)
      atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (s := (1 : ℝ) / 2)
      (m : ℝ) (by norm_num)).tendsto_div_nhds_zero
    simpa only [Real.rpow_natCast, ← Real.sqrt_eq_rpow] using h
  have hmajor : Tendsto (fun d : ℕ => (2 : ℝ) ^ m *
      (Real.log (d : ℝ) ^ m / Real.sqrt (d : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      (hreal.comp tendsto_natCast_atTop_atTop).const_mul ((2 : ℝ) ^ m)
  have hlog : Tendsto (fun d : ℕ => Real.log (d : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hnonneg (d : ℕ) : 0 ≤
      (6 + Real.log ((d : ℝ) + 1)) ^ m / Real.sqrt (d : ℝ) := by
    have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
    have hnlog : 0 ≤ Real.log ((d : ℝ) + 1) :=
      Real.log_nonneg (by linarith)
    exact div_nonneg (pow_nonneg (by linarith) _) (Real.sqrt_nonneg _)
  apply squeeze_zero' (Eventually.of_forall hnonneg) _ hmajor
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    (tendsto_atTop.1 hlog) 7] with d hd hlogd
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdp : (0 : ℝ) < d := by linarith
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hshift : Real.log ((d : ℝ) + 1) ≤ Real.log (2 * (d : ℝ)) :=
    Real.log_le_log (by positivity) (by nlinarith only [hdR])
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hdp.ne'] at hshift
  have hb0 : 0 ≤ 6 + Real.log ((d : ℝ) + 1) := by
    have hnlog := Real.log_nonneg (show (1 : ℝ) ≤ (d : ℝ) + 1 by linarith)
    linarith
  have hbase : 6 + Real.log ((d : ℝ) + 1) ≤ 2 * Real.log (d : ℝ) := by
    linarith
  have hp : (6 + Real.log ((d : ℝ) + 1)) ^ m ≤
      (2 * Real.log (d : ℝ)) ^ m := pow_le_pow_left₀ hb0 hbase m
  calc
    _ ≤ (2 * Real.log (d : ℝ)) ^ m / Real.sqrt (d : ℝ) :=
      div_le_div_of_nonneg_right hp (Real.sqrt_nonneg _)
    _ = _ := by rw [mul_pow]; ring

end RiemannResearch.Analysis.ConductorLogEnvelope
