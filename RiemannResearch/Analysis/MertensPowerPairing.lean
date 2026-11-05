/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# First moments for Möbius heads under a power saving

For a uniform two-part bound on a defect, taking its pointwise minimum
before summation yields a single summable envelope. The signed pairing may
use any cofinal family of legal heads. All hypotheses on that family are
explicit. Index `n` in the series labels the physical integer `n + 1`.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.Analysis

/-- The bound from a Mertens saving of order a can be made independent of N. -/
theorem min_cutoff_power_le (N x a : ℝ) (hN : 0 < N) (hx : 0 < x) (ha : 0 < a) :
    min N (x * N ^ (-a)) ≤ x ^ (1 / (1 + a)) := by
  let p : ℝ := 1 / (1 + a)
  have hpa : p * (-a) + 1 = p := by
    dsimp [p]
    field_simp [show 1 + a ≠ 0 by positivity]
    <;> ring
  by_cases h : N ≤ x ^ p
  · exact (min_le_left _ _).trans h
  · have hpow := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hx p)
        (le_of_not_ge h) (neg_nonpos.mpr ha.le)
    calc
      min N (x * N ^ (-a)) ≤ x * N ^ (-a) := min_le_right _ _
      _ ≤ x * (x ^ p) ^ (-a) := mul_le_mul_of_nonneg_left hpow hx.le
      _ = x ^ p := by
        rw [← Real.rpow_mul hx.le, mul_comm, ← Real.rpow_add_one hx.ne', hpa]

/-- A two-part defect envelope and summability of the weighted witness suffice
for the signed pairing to tend to zero. No positivity of the witness is required. -/
theorem power_defect_pairing_tendsto_zero
    (D : ℕ → ℕ → ℝ) (v N : ℕ → ℝ) (a C : ℝ) (ha : 0 < a) (hC : 0 ≤ C)
    (hhead : ∀ n, ∀ᶠ j in atTop, D j n = 0)
    (hbound : ∀ᶠ j in atTop, 0 < N j ∧ ∀ n : ℕ,
      |D j n| ≤ C * min (N j) (((n : ℝ) + 1) * (N j) ^ (-a)))
    (hsum : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (1 / (1 + a)) * |v n|)) :
    Tendsto (fun j => ∑' n, D j n * v n) atTop (𝓝 0) := by
  have ht : Tendsto (fun j => ∑' n, D j n * v n) atTop
      (𝓝 (∑' _ : ℕ, (0 : ℝ))) := by
    apply tendsto_tsum_of_dominated_convergence (hsum.mul_left C)
    · intro n
      apply tendsto_const_nhds.congr'
      filter_upwards [hhead n] with j hj
      simp [hj]
    · filter_upwards [hbound] with j hj n
      rw [Real.norm_eq_abs, abs_mul]
      have hh := (hj.2 n).trans (mul_le_mul_of_nonneg_left
        (min_cutoff_power_le (N j) ((n : ℝ) + 1) a hj.1 (by positivity) ha) hC)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hh (abs_nonneg (v n))
  simpa using ht

/-- For v(n)=w(n+1)/(n+1)^2 the two-part bound allows every polynomial
growth exponent β < a/(1+a) for w. -/
theorem summable_power_pairing_of_growth (w : ℕ → ℝ) (a β K : ℝ)
    (ha : 0 < a) (hβ : β < a / (1 + a)) (hK : 0 ≤ K)
    (hw : ∀ n : ℕ, |w n| ≤ K * ((n : ℝ) + 1) ^ β) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (1 / (1 + a)) *
      |w n / ((n : ℝ) + 1) ^ 2|) := by
  let p : ℝ := 1 / (1 + a)
  have hden : 0 < 1 + a := by positivity
  have hcrit : a / (1 + a) = 1 - p := by
    dsimp [p]
    field_simp [hden.ne']
    <;> ring
  rw [hcrit] at hβ
  have hpow := Real.summable_nat_rpow.mpr (show p + β - 2 < -1 by linarith)
  have hadd : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (p + β - 2)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hpow
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (abs_nonneg _)) _ (hadd.mul_left K)
  intro n
  let x : ℝ := (n : ℝ) + 1
  have hx : 0 < x := by dsimp [x]; positivity
  change x ^ p * |w n / x ^ 2| ≤ K * x ^ (p + β - 2)
  rw [abs_div, abs_of_nonneg (sq_nonneg x), Real.rpow_sub hx, Real.rpow_add hx,
    Real.rpow_two]
  calc
    _ ≤ x ^ p * (K * x ^ β / x ^ 2) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hw n) (sq_nonneg x))
        (Real.rpow_nonneg hx.le _)
    _ = _ := by ring

end RiemannResearch.Analysis
