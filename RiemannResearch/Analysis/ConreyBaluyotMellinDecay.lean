/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotMellinContour
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.IntervalCases

/-!
# Uniform exponential decay of the Conrey--Baluyot weight

Source for the requested estimate: S. A. C. Baluyot,
*On the Zeros of Riemann's Zeta-function* (2017), Lemma 3.1.1(iii),
equation (3.1.4), pp. 94--95:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320 .

Here the positive-contour identity and integer Gamma values give factorial
bounds. Summing against the exponential power series proves the explicit
bound 72 exp(-1/(2 xi)) for every sigma > 1/2 and 0 < xi <= 1.
This proof avoids a separate Stirling estimate. The signed negative-contour
expansion and large-y normalization are proved in ConreyBaluyotMellinShift
and ConreyBaluyotMellinNormalization.
-/

open Complex MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace RiemannResearch.Analysis.ConreyBaluyot

private theorem quadratic_le_geometric (n : ℕ) :
    ((n : ℝ) + 1) * ((n : ℝ) + 2) ≤ 6 * (3 / 2 : ℝ) ^ n := by
  by_cases hn : n < 3
  · interval_cases n <;> norm_num
  · have hn3 : 3 ≤ n := by omega
    clear hn
    induction n, hn3 using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
        have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
        calc
          _ ≤ (3 / 2 : ℝ) * (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
            push_cast
            nlinarith
          _ ≤ (3 / 2 : ℝ) * (6 * (3 / 2 : ℝ) ^ n) :=
            mul_le_mul_of_nonneg_left ih (by norm_num)
          _ = _ := by rw [pow_succ]; ring

theorem norm_weight_le_factorial_all {σ ξ : ℝ}
    (hσ : 1 / 2 < σ) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (n : ℕ) :
    ‖weight σ ξ‖ ≤ 3 * (n + 2).factorial * ξ ^ n := by
  cases n with
  | zero =>
      have h := norm_weight_le hσ hξ
      norm_num
      linarith
  | succ n =>
      have h := norm_weight_le_factorial hσ hξ (Nat.succ_le_succ (Nat.zero_le n))
      have hp : (0 : ℝ) ≤ (n + 1 + 2).factorial * ξ ^ (n + 1) := by positivity
      simp only [Nat.succ_eq_add_one] at h ⊢
      nlinarith

/-- Uniform exponential small-argument decay, with an absolute constant. -/
theorem norm_weight_le_exp {σ ξ : ℝ}
    (hσ : 1 / 2 < σ) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    ‖weight σ ξ‖ ≤ 72 * Real.exp (-1 / (2 * ξ)) := by
  have hs : HasSum (fun n : ℕ => (1 / (2 * ξ)) ^ n / (n.factorial : ℝ))
      (Real.exp (1 / (2 * ξ))) := by
    simpa only [Real.exp_eq_exp_ℝ] using
      NormedSpace.expSeries_div_hasSum_exp (1 / (2 * ξ))
  have hterm (n : ℕ) :
      ‖weight σ ξ‖ * ((1 / (2 * ξ)) ^ n / (n.factorial : ℝ)) ≤
        3 * (((n : ℝ) + 1) * ((n : ℝ) + 2) * (1 / 2 : ℝ) ^ n) := by
    calc
      _ ≤ (3 * (n + 2).factorial * ξ ^ n) *
          ((1 / (2 * ξ)) ^ n / (n.factorial : ℝ)) := by
            exact mul_le_mul_of_nonneg_right (norm_weight_le_factorial_all hσ hξ hξ1 n)
              (by positivity)
      _ = _ := by
        have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
        simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
          div_pow, mul_pow, one_pow]
        field_simp [hξ.ne', hf]
        <;> ring
  have hgeom : HasSum (fun n : ℕ => 18 * (3 / 4 : ℝ) ^ n) 72 := by
    convert! (hasSum_geometric_of_norm_lt_one
      (by norm_num : ‖(3 / 4 : ℝ)‖ < 1)).mul_left 18 using 1 <;> norm_num
  have hterm' (n : ℕ) :
      ‖weight σ ξ‖ * ((1 / (2 * ξ)) ^ n / (n.factorial : ℝ)) ≤
        18 * (3 / 4 : ℝ) ^ n := by
    calc
      _ ≤ 3 * (((n : ℝ) + 1) * ((n : ℝ) + 2) * (1 / 2 : ℝ) ^ n) := hterm n
      _ ≤ 3 * ((6 * (3 / 2 : ℝ) ^ n) * (1 / 2 : ℝ) ^ n) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (quadratic_le_geometric n) (by positivity))
          (by norm_num)
      _ = 18 * (((3 / 2 : ℝ) * (1 / 2)) ^ n) := by rw [mul_pow]; ring
      _ = _ := by norm_num
  have hsum : ‖weight σ ξ‖ * Real.exp (1 / (2 * ξ)) ≤ 72 := by
    have hh := Summable.tsum_le_tsum hterm' (hs.mul_left ‖weight σ ξ‖).summable hgeom.summable
    rw [(hs.mul_left ‖weight σ ξ‖).tsum_eq, hgeom.tsum_eq] at hh
    exact hh
  have hh := mul_le_mul_of_nonneg_right hsum
    (Real.exp_pos (-(1 / (2 * ξ)))).le
  simpa only [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
    mul_one, neg_div] using hh


/-- Baluyot's tail bound, valid on the larger domain h >= y > 0. -/
theorem norm_weight_ratio_le_exp {σ y h : ℝ}
    (hσ : 1 / 2 < σ) (hy : 0 < y) (hyh : y ≤ h) :
    ‖weight σ (y / h)‖ ≤ 72 * Real.exp (-h / (2 * y)) := by
  have hh : 0 < h := hy.trans_le hyh
  calc
    _ ≤ 72 * Real.exp (-1 / (2 * (y / h))) :=
      norm_weight_le_exp hσ (div_pos hy hh) ((div_le_one hh).mpr hyh)
    _ = _ := by
      congr 2
      field_simp

end RiemannResearch.Analysis.ConreyBaluyot
