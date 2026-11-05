/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-!
# Approximate square-difference tests
Source: the user-directed four-criteria continuation, 4 November 2026.
The exact weighted identity is retained. For a sublinear square-recurrent
sequence, normalized weighted tests tending to zero imply vanishing differences.
The concrete RH consumer is QSquarefreeApproximateTests.
-/
noncomputable section

open Filter
open scoped Topology
namespace RiemannResearch.NumberTheory.ApproximateSquareTests
def weightedTest (h : ℕ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * h (n ^ 2) - ((n : ℝ) ^ 2 - 1) * h (n ^ 2 - 1) -
    (n : ℝ) * h n + ((n : ℝ) - 1) * h (n - 1)
theorem weightedTest_eq (h : ℕ → ℝ) (n : ℕ)
    (hs : h (n ^ 2) - h (n ^ 2 - 1) = h n - h (n - 1)) :
    weightedTest h n = h (n ^ 2) - h n + ((n : ℝ) ^ 2 - n) * (h n - h (n - 1)) := by
  unfold weightedTest
  linear_combination ((n : ℝ) ^ 2 - 1) * hs

theorem difference_tendsto_zero_of_normalized_test
    (h : ℕ → ℝ)
    (hsub : Tendsto (fun n : ℕ => h n / (n : ℝ)) atTop (𝓝 0))
    (hs : ∀ n, 2 ≤ n → h (n ^ 2) - h (n ^ 2 - 1) = h n - h (n - 1))
    (ht : Tendsto (fun n : ℕ => weightedTest h n / (n : ℝ) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => h n - h (n - 1)) atTop (𝓝 0) := by
  have hp : Tendsto (fun n : ℕ => n ^ 2) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (max b 1)] with n hn
    have hb := le_max_left b 1
    have h1 := le_max_right b 1
    nlinarith
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have hsq : Tendsto (fun n : ℕ => h (n ^ 2) / (n : ℝ) ^ 2) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_pow] using hsub.comp hp
  have hsmall : Tendsto (fun n : ℕ => h n / (n : ℝ) ^ 2) atTop (𝓝 0) := by
    have hc := hsub.mul hinv
    simp only [mul_zero] at hc
    convert hc using 1
    funext n
    ring
  have hlim := ((ht.sub hsq).add hsmall).div
    (tendsto_const_nhds.sub hinv) (by norm_num : (1 : ℝ) - 0 ≠ 0)
  simp only [sub_zero, zero_add, zero_div] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have he := weightedTest_eq h n (hs n hn)
  change (weightedTest h n / (n : ℝ) ^ 2 - h (n ^ 2) / (n : ℝ) ^ 2 +
    h n / (n : ℝ) ^ 2) / (1 - 1 / (n : ℝ)) = h n - h (n - 1)
  rw [he]
  field_simp [hn0, hn1]
  <;> ring

end RiemannResearch.NumberTheory.ApproximateSquareTests


namespace RiemannResearch.NumberTheory.ApproximateSquareTests

theorem normalized_difference_tendsto_zero (h : ℕ → ℝ)
    (hsub : Tendsto (fun n : ℕ => h n / (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (h n - h (n - 1)) / (n : ℝ)) atTop (𝓝 0) := by
  have hp : Tendsto (fun n : ℕ => n - 1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b + 1)] with n hn
    omega
  have hinv := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have hprev := (hsub.comp hp).mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hinv)
  have hh : Tendsto (fun n : ℕ => h (n - 1) / (n : ℝ)) atTop (𝓝 0) := by
    simp only [zero_mul] at hprev
    apply hprev.congr'
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
    change h (n - 1) / ((n - 1 : ℕ) : ℝ) * (1 - 1 / (n : ℝ)) =
      h (n - 1) / (n : ℝ)
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    field_simp
  simpa only [zero_sub, sub_zero, sub_div] using hsub.sub hh
end RiemannResearch.NumberTheory.ApproximateSquareTests
