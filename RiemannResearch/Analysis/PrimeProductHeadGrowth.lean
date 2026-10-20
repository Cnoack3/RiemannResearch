/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.PrimeProductDyadicGrowth
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Growth of the prime-product head at every cutoff

Source: the user-directed RH/CRT continuation of 20 October 2026. The dyadic
lower rate and monotonicity of the actual finite prime product yield a lower
rate at every cutoff. The coarse squared floor-log correction is retained.
-/

noncomputable section
open scoped Topology
open Filter

namespace RiemannResearch.Analysis

/-- The floor logarithm with base 64 tends to infinity, directly from its
defining power inequality. -/
theorem nat_log64_tendsto_atTop : Tendsto (Nat.log 64) atTop atTop := by
  apply tendsto_atTop.2
  intro m
  filter_upwards [eventually_ge_atTop (64 ^ m)] with Y hY
  have hpos : 0 < (64 : ℕ) ^ m := by positivity
  have hY0 : Y ≠ 0 := by omega
  exact (Nat.le_log_iff_pow_le (by norm_num : 1 < (64 : ℕ)) hY0).2 hY

/-- Extending the dyadic lower rate to every positive cutoff costs only the
constant factor 16. -/
theorem finitePrimeProduct_log64_energy_lower (Y : ℕ) (hY : Y ≠ 0) :
    (1 / 900 : ℝ) * 4 ^ Nat.log 64 Y ≤
      finitePrimeProduct Y ^ 2 * (Y : ℝ) := by
  let m := Nat.log 64 Y
  let a := finitePrimeProduct Y
  let b := finitePrimeProduct (64 ^ (m + 1))
  let t : ℝ := ((64 ^ m : ℕ) : ℝ)
  have hlo : (64 : ℕ) ^ m ≤ Y := Nat.pow_log_le_self 64 hY
  have hhi : Y < (64 : ℕ) ^ (m + 1) := by
    simpa [m, Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by norm_num : 1 < (64 : ℕ)) Y)
  have ha : 0 ≤ a := finitePrimeProduct_nonneg Y
  have hb : 0 ≤ b := finitePrimeProduct_nonneg _
  have hba : b ≤ a := finitePrimeProduct_antitone hhi.le
  have hsq : b ^ 2 ≤ a ^ 2 := (sq_le_sq₀ hb ha).2 hba
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hloR : t ≤ (Y : ℝ) := by dsimp [t]; exact_mod_cast hlo
  have hmul₁ := mul_le_mul_of_nonneg_right hsq ht
  have hmul₂ := mul_le_mul_of_nonneg_left hloR (sq_nonneg a)
  have hrate : (4 / 225 : ℝ) * (4 : ℝ) ^ (m + 1) ≤
      b ^ 2 * ((64 ^ (m + 1) : ℕ) : ℝ) :=
    finitePrimeProduct_dyadic_energy_lower (m + 1)
  have hstep : ((64 ^ (m + 1) : ℕ) : ℝ) = 64 * t := by
    dsimp [t]
    push_cast
    rw [pow_succ]
    ring
  rw [hstep, pow_succ] at hrate
  change (1 / 900 : ℝ) * 4 ^ m ≤ a ^ 2 * (Y : ℝ)
  nlinarith [hrate, hmul₁, hmul₂]

/-- A coarse base comparison avoids real logarithms in the head estimate. -/
theorem nat_log2_le_twelve_log64 (Y : ℕ) (hY : 64 ≤ Y) :
    Nat.log 2 Y ≤ 12 * Nat.log 64 Y := by
  have hY0 : Y ≠ 0 := by omega
  let m := Nat.log 64 Y
  have hm : 1 ≤ m :=
    (Nat.le_log_iff_pow_le (by norm_num : 1 < (64 : ℕ)) hY0).2 (by simpa using hY)
  have hhi : Y < (64 : ℕ) ^ (m + 1) := by
    simpa [m, Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by norm_num : 1 < (64 : ℕ)) Y)
  have hpow : (64 : ℕ) ^ (m + 1) = 2 ^ (6 * (m + 1)) := by
    norm_num [pow_mul]
  have hlog : Nat.log 2 Y < 6 * (m + 1) :=
    (Nat.log_lt_iff_lt_pow (by norm_num : 1 < (2 : ℕ)) hY0).2 (hhi.trans_eq hpow)
  change Nat.log 2 Y ≤ 12 * m
  omega

/-- The full finite-head lower bound diverges, with the coarse floor-log error
retained. This applies to all cutoffs, not only a subsequence. -/
theorem finitePrimeProduct_head_tendsto_atTop (Z : ℝ) (hZ : 0 < Z) :
    Tendsto (fun Y : ℕ => finitePrimeProduct Y ^ 2 * (Y : ℝ) / (2 * Z) -
      (Nat.log 2 Y : ℝ) ^ 2) atTop atTop := by
  have hbase := (four_pow_sub_quadratic_tendsto_atTop
    (1 / (1800 * Z)) 144 (by positivity : (0 : ℝ) < 1 / (1800 * Z))).comp
      nat_log64_tendsto_atTop
  apply tendsto_atTop.2
  intro B
  filter_upwards [hbase.eventually (eventually_ge_atTop B),
    eventually_ge_atTop 64] with Y hbaseY hY
  have hY0 : Y ≠ 0 := by omega
  have hrate := finitePrimeProduct_log64_energy_lower Y hY0
  have hdiv := div_le_div_of_nonneg_right hrate
    (by positivity : (0 : ℝ) ≤ 2 * Z)
  have heq : (1 / 900 : ℝ) * 4 ^ Nat.log 64 Y / (2 * Z) =
      (1 / (1800 * Z)) * 4 ^ Nat.log 64 Y := by
    field_simp [ne_of_gt hZ]
    <;> ring
  rw [heq] at hdiv
  have hlog : (Nat.log 2 Y : ℝ) ≤ 12 * (Nat.log 64 Y : ℝ) := by
    exact_mod_cast nat_log2_le_twelve_log64 Y hY
  have hsq : (Nat.log 2 Y : ℝ) ^ 2 ≤ (12 * (Nat.log 64 Y : ℝ)) ^ 2 :=
    (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ Nat.log 2 Y)
      (by positivity : (0 : ℝ) ≤ 12 * (Nat.log 64 Y : ℝ))).2 hlog
  dsimp only [Function.comp_def] at hbaseY
  nlinarith [hbaseY, hdiv, hsq]

end RiemannResearch.Analysis
