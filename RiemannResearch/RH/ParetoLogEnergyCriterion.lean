/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ThresholdHilbertSpace
import RiemannResearch.Analysis.LogPowerSummability
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import RiemannResearch.RH.DampedMobiusSeed

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto

/-- Any logarithmic saving of exponent greater than one half at square-root
growth gives finite Pareto energy. Only an eventual bound is required. -/
theorem square_summable_of_eventual_sqrt_log_bound
    {f : ℕ → ℝ} {C p : ℝ} (hp : (1 / 2 : ℝ) < p)
    (hf : ∀ᶠ n : ℕ in atTop,
      |f n| ≤ C * Real.sqrt (n : ℝ) / Real.log (2 * (n : ℝ)) ^ p) :
    Summable (fun n => positiveWeight n * (f n) ^ 2) := by
  have hs := (RiemannResearch.Analysis.summable_log_power_majorant
    (p := 2 * p) (by linarith)).mul_left (C ^ 2)
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [hf, eventually_ge_atTop (1 : ℕ)] with n hn hnp
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hnp)
  have hlpos : 0 < Real.log (2 * (n : ℝ)) := Real.log_pos (by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnp
    linarith)
  have hpow : 0 < Real.log (2 * (n : ℝ)) ^ (2 * p) :=
    Real.rpow_pos_of_pos hlpos _
  have hpow2 : (Real.log (2 * (n : ℝ)) ^ p) ^ 2 =
      Real.log (2 * (n : ℝ)) ^ (2 * p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlpos.le]
    congr 1
    ring
  have hsq : (f n) ^ 2 ≤
      C ^ 2 * (n : ℝ) / Real.log (2 * (n : ℝ)) ^ (2 * p) := by
    have h := mul_self_le_mul_self (abs_nonneg (f n)) hn
    simpa only [← pow_two, sq_abs, div_pow, mul_pow,
      Real.sq_sqrt (Nat.cast_nonneg n), hpow2] using h
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _))]
  calc
    _ ≤ positiveWeight n *
        (C ^ 2 * (n : ℝ) / Real.log (2 * (n : ℝ)) ^ (2 * p)) :=
      mul_le_mul_of_nonneg_left hsq (positiveWeight_nonneg n)
    _ = C ^ 2 / (((n : ℝ) + 1) * Real.log (2 * (n : ℝ)) ^ (2 * p)) := by
      unfold positiveWeight
      field_simp [hnpos.ne', hpow.ne']
    _ ≤ C ^ 2 / ((n : ℝ) * Real.log (2 * (n : ℝ)) ^ (2 * p)) := by
      apply div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos hnpos hpow)
      nlinarith
    _ = _ := by ring

end RiemannResearch.RH.Pareto

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto

/-- The shifted logarithm from the arithmetic hyperbola estimate gives the
same finite-energy criterion. Every exponent greater than one half suffices. -/
theorem square_summable_of_eventual_sqrt_shifted_log_bound
    {f : ℕ → ℝ} {C q : ℝ} (hC : 0 ≤ C) (hq : (1 / 2 : ℝ) < q)
    (hf : ∀ᶠ n : ℕ in atTop,
      |f n| ≤ C * Real.sqrt (n : ℝ) * (6 + Real.log (n : ℝ)) ^ (-q)) :
    Summable (fun n => positiveWeight n * (f n) ^ 2) := by
  apply square_summable_of_eventual_sqrt_log_bound (C := C) hq
  filter_upwards [hf, eventually_ge_atTop (1 : ℕ)] with n hn hnp
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (Nat.zero_lt_of_lt hnp)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnp
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlpos : 0 < Real.log (2 * (n : ℝ)) :=
    Real.log_pos (by linarith)
  have hshift : Real.log (2 * (n : ℝ)) ≤ 6 + Real.log (n : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnpos.ne']
    linarith
  have hspos : 0 < 6 + Real.log (n : ℝ) := lt_of_lt_of_le hlpos hshift
  apply hn.trans
  rw [Real.rpow_neg hspos.le, ← div_eq_mul_inv]
  apply div_le_div_of_nonneg_left (mul_nonneg hC (Real.sqrt_nonneg _))
    (Real.rpow_pos_of_pos hlpos q)
  exact Real.rpow_le_rpow hlpos.le hshift (by linarith : 0 ≤ q)

/-- The actual epsilon-one-half arithmetic sequence has finite Pareto energy
under an eventual square-root bound with any shifted-log saving q > 1/2.
The estimate is the explicit arithmetic premise; its provider is separate. -/
theorem centered_dampedMobius_half_energy_of_shifted_log_bound
    (C : ℝ) {K q : ℝ} (hK : 0 ≤ K) (hq : (1 / 2 : ℝ) < q)
    (hbound : ∀ᶠ n : ℕ in atTop,
      |dampedMobiusPrefix (1 / 2) n - (n : ℝ) * C| ≤
        K * Real.sqrt (n : ℝ) * (6 + Real.log (n : ℝ)) ^ (-q)) :
    Summable (fun n => positiveWeight n *
      (dampedMobiusPrefix (1 / 2) n - (n : ℝ) * C) ^ 2) :=
  square_summable_of_eventual_sqrt_shifted_log_bound hK hq hbound

end RiemannResearch.RH.Pareto
