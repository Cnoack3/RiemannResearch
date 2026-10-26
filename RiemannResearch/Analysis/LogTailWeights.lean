/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.PowerLogProfiles
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Comparable logarithmic weights and monotone tail profiles

Source: the user-provided moving-head research handoff, 26 October 2026.
These elementary scalar comparisons have no Hilbert, squarefree, or RH
hypothesis. Increasing the fixed shift makes the auxiliary profile monotone
on every positive integer, while costing only a finite comparison constant.
-/

noncomputable section
open Filter
namespace RiemannResearch.Analysis.LogTailWeights
open RiemannResearch.Analysis

def logWeight (k N : ℕ) : ℝ := (N : ℝ) / (6 + Real.log (N : ℝ)) ^ k

theorem logWeight_pos (k N : ℕ) (hN : 0 < N) : 0 < logWeight k N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog := Real.log_nonneg hN1
  dsimp [logWeight]
  positivity

theorem logWeight_nonneg (k N : ℕ) : 0 ≤ logWeight k N := by
  by_cases hN : N = 0
  · simp [hN, logWeight]
  · exact (logWeight_pos k N (Nat.pos_of_ne_zero hN)).le

theorem logWeight_le_nat (k N : ℕ) : logWeight k N ≤ N := by
  by_cases hN : N = 0
  · simp [hN, logWeight]
  · have hN1 : (1 : ℝ) ≤ N := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hN)
    have hL : (1 : ℝ) ≤ 6 + Real.log (N : ℝ) := by
      linarith [Real.log_nonneg hN1]
    exact div_le_self (Nat.cast_nonneg N) (one_le_pow₀ hL)

/-- Monotonicity of the denominator is enough: no upper comparison between
the logarithms is required. -/
theorem logWeight_le_two_of_comparable (k N M : ℕ) (hN : 0 < N)
    (hNM : N ≤ M) (hM2N : M ≤ 2 * N) :
    logWeight k M ≤ 2 * logWeight k N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNMR : (N : ℝ) ≤ M := by exact_mod_cast hNM
  have hM2NR : (M : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hM2N
  have hlog : Real.log (N : ℝ) ≤ Real.log (M : ℝ) :=
    Real.log_le_log hNR hNMR
  have hLN : 0 < 6 + Real.log (N : ℝ) := by
    linarith [Real.log_nonneg hN1]
  have hLM : 0 < 6 + Real.log (M : ℝ) := by linarith
  have hpow : (6 + Real.log (N : ℝ)) ^ k ≤
      (6 + Real.log (M : ℝ)) ^ k :=
    pow_le_pow_left₀ hLN.le (by linarith) k
  change (M : ℝ) / (6 + Real.log (M : ℝ)) ^ k ≤
    2 * ((N : ℝ) / (6 + Real.log (N : ℝ)) ^ k)
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (pow_pos hLM k) (pow_pos hLN k)).mpr
  calc
    (M : ℝ) * (6 + Real.log (N : ℝ)) ^ k
        ≤ (2 * (N : ℝ)) * (6 + Real.log (N : ℝ)) ^ k :=
      mul_le_mul_of_nonneg_right hM2NR (pow_nonneg hLN.le k)
    _ ≤ (2 * (N : ℝ)) * (6 + Real.log (M : ℝ)) ^ k :=
      mul_le_mul_of_nonneg_left hpow (by positivity)

/-- The enlarged shift makes the profile monotone down to the first site. -/
def polylogTailProfile (k n : ℕ) : ℝ :=
  powerLogNatProfile 1 (k : ℝ) ((k : ℝ)+6) n

theorem polylogTailProfile_eq (k n : ℕ) :
    polylogTailProfile k n = (n : ℝ) / ((k : ℝ)+6+Real.log (n : ℝ))^k := by
  by_cases hn : n = 0
  · simp [hn, polylogTailProfile, powerLogNatProfile]
  · simp [polylogTailProfile, powerLogNatProfile, hn,
      Real.rpow_one, Real.rpow_natCast]

theorem polylogTailProfile_nonneg (k n : ℕ) : 0 ≤ polylogTailProfile k n :=
  powerLogNatProfile_nonneg (by positivity) n

theorem polylogTailProfile_monotone (k : ℕ) : Monotone (polylogTailProfile k) :=
  powerLogNatProfile_monotone (by positivity) (by norm_num) (by
    have hk := Nat.cast_nonneg (α := ℝ) k
    nlinarith)

theorem polylogTailProfile_le_logWeight (k n : ℕ) :
    polylogTailProfile k n ≤ logWeight k n := by
  by_cases hn : n = 0
  · simp [hn, polylogTailProfile_eq, logWeight]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hL : 0 < 6 + Real.log (n : ℝ) := by linarith [Real.log_nonneg hn1]
  rw [polylogTailProfile_eq]
  unfold logWeight
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg n) (pow_pos hL k)
  exact pow_le_pow_left₀ hL.le (by
    have hk := Nat.cast_nonneg (α := ℝ) k
    linarith) k

/-- Changing the fixed logarithmic shift costs only a finite constant. -/
theorem logWeight_le_polylogTailProfile (k n : ℕ) :
    logWeight k n ≤ ((k : ℝ)+6)^k * polylogTailProfile k n := by
  by_cases hn : n = 0
  · simp [hn, polylogTailProfile_eq, logWeight]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hl := Real.log_nonneg hn1
  have hk := Nat.cast_nonneg (α := ℝ) k
  have hL : 0 < 6 + Real.log (n : ℝ) := by linarith
  have hK : 0 < (k : ℝ)+6+Real.log (n : ℝ) := by linarith
  have hbase : (k : ℝ)+6+Real.log (n : ℝ) ≤
      ((k : ℝ)+6)*(6+Real.log (n : ℝ)) := by nlinarith
  have hp := pow_le_pow_left₀ hK.le hbase k
  rw [mul_pow] at hp
  rw [polylogTailProfile_eq]
  unfold logWeight
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (pow_pos hL k) (pow_pos hK k)).mpr
  have hm := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  nlinarith

/-- Every fixed logarithmic profile grows without bound. -/
theorem polylogTailProfile_tendsto_atTop (k : ℕ) :
    Tendsto (polylogTailProfile k) atTop atTop := by
  let c : ℝ := (k : ℝ) + 6
  have hL : Tendsto (fun n : ℕ => c + Real.log (n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop c
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have ht := ((Real.tendsto_exp_div_pow_atTop k).comp hL).const_mul_atTop
    (Real.exp_pos (-c))
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  change Real.exp (-c) *
      (Real.exp (c + Real.log (n : ℝ)) / (c + Real.log (n : ℝ)) ^ k) =
    polylogTailProfile k n
  rw [polylogTailProfile_eq]
  change Real.exp (-c) *
      (Real.exp (c + Real.log (n : ℝ)) / (c + Real.log (n : ℝ)) ^ k) =
    (n : ℝ) / (c + Real.log (n : ℝ)) ^ k
  rw [← mul_div_assoc, ← Real.exp_add,
    show -c + (c + Real.log (n : ℝ)) = Real.log (n : ℝ) by ring,
    Real.exp_log hn0]

end RiemannResearch.Analysis.LogTailWeights
