/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The complete odd reciprocal-square series

Source: user-provided argument and
`RiemannResearch/RH/InfiniteSquarefreeResponseResearch20261027.md`,
for the statement and partial-fraction strategy.

The harmonic differences are paired before a `HasSum` assertion is made.
No unordered sum of the conditionally convergent alternating harmonic series
is used, and no physical tail is omitted.

-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.OddReciprocalSquare

/-- Exact finite identity, retaining both harmonic endpoints. -/
theorem paired_reciprocal_sum (n : ℕ) :
    (∑ k ∈ Finset.range n,
      (1 / (2 * (k : ℝ) + 1) - 1 / (2 * (k : ℝ) + 2))) =
      (harmonic (2 * n) : ℝ) - (harmonic n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
      rw [harmonic_succ, harmonic_succ, harmonic_succ]
      simp only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast,
        Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
      push_cast
      have h₁ : (n : ℝ) + 1 ≠ 0 := by positivity
      have h₂ : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
      have h₃ : 2 * (n : ℝ) + 2 ≠ 0 := by positivity
      have h₄ : 2 * (n : ℝ) + 1 + 1 ≠ 0 := by positivity
      field_simp [h₁, h₂, h₃, h₄]
      ring

/-- The paired, nonnegative reciprocal differences have their full infinite
sum equal to log 2. This is an unconditional `HasSum` statement. -/
theorem hasSum_paired_reciprocal :
    HasSum (fun k : ℕ =>
      1 / (2 * (k : ℝ) + 1) - 1 / (2 * (k : ℝ) + 2))
      (Real.log 2) := by
  have hnonneg (k : ℕ) :
      0 ≤ 1 / (2 * (k : ℝ) + 1) - 1 / (2 * (k : ℝ) + 2) := by
    apply sub_nonneg.mpr
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  apply (hasSum_iff_tendsto_nat_of_nonneg hnonneg _).mpr
  have hdouble : Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  have hlim :
      Tendsto (fun n : ℕ =>
        ((harmonic (2 * n) : ℝ) - Real.log (2 * n : ℕ)) -
          ((harmonic n : ℝ) - Real.log n) + Real.log 2)
        atTop (𝓝 (Real.log 2)) := by
    simpa only [Function.comp_def, sub_self, zero_add] using
      ((Real.tendsto_harmonic_sub_log.comp hdouble).sub
        Real.tendsto_harmonic_sub_log).add
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => Real.log 2) atTop (𝓝 (Real.log 2)))
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  rw [paired_reciprocal_sum]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0]
  ring

theorem paired_reciprocal_tsum :
    (∑' k : ℕ, (1 / (2 * (k : ℝ) + 1) - 1 / (2 * (k : ℝ) + 2))) =
      Real.log 2 :=
  hasSum_paired_reciprocal.tsum_eq

/-- Pointwise partial fractions. Only the already paired harmonic difference
will be summed, so no subtraction of divergent series occurs. -/
theorem reciprocal_square_partial_fraction (x : ℝ)
    (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    1 / (x ^ 2 * (x + 1) ^ 2) =
      1 / x ^ 2 + 1 / (x + 1) ^ 2 - 2 * (1 / x - 1 / (x + 1)) := by
  field_simp [hx, hx1]
  ring

/-- Evaluation with an arbitrary certified value of the complete inverse-square
series. The parameter `z` is intended to be instantiated by ζ(2). -/
theorem hasSum_odd_reciprocal_square_of_hasSum {z : ℝ}
    (hz : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) z) :
    HasSum (fun k : ℕ =>
      1 / ((2 * (k : ℝ) + 1) ^ 2 * (2 * (k : ℝ) + 2) ^ 2))
      (z - 2 * Real.log 2) := by
  let f : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) ^ 2
  have hf : HasSum f z := hz
  have he : Summable (fun k : ℕ => f (2 * k)) :=
    hf.summable.comp_injective (fun i j h => by omega)
  have ho : Summable (fun k : ℕ => f (2 * k + 1)) :=
    hf.summable.comp_injective (fun i j h => by omega)
  have hp : HasSum (fun k : ℕ => f (2 * k) + f (2 * k + 1)) z := by
    simpa only [tsum_even_add_odd he ho, hf.tsum_eq] using
      he.hasSum.add ho.hasSum
  have hterm :
      (fun k : ℕ => 1 / ((2 * (k : ℝ) + 1) ^ 2 * (2 * (k : ℝ) + 2) ^ 2)) =
      (fun k : ℕ => f (2 * k) + f (2 * k + 1) -
        2 * (1 / (2 * (k : ℝ) + 1) - 1 / (2 * (k : ℝ) + 2))) := by
    funext k
    dsimp only [f]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    have hden : 2 * (k : ℝ) + 1 + 1 = 2 * (k : ℝ) + 2 := by ring
    simpa only [hden] using
      reciprocal_square_partial_fraction (2 * (k : ℝ) + 1)
        (by positivity) (by positivity)
  rw [hterm]
  exact hp.sub (hasSum_paired_reciprocal.mul_left (2 : ℝ))

/-- The identity as a complete natural-indexed infinite series. -/
theorem odd_reciprocal_square_tsum_shifted :
    (∑' k : ℕ,
      1 / ((2 * (k : ℝ) + 1) ^ 2 * (2 * (k : ℝ) + 2) ^ 2)) =
      (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2) - 2 * Real.log 2 := by
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))
  have hs' : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).mpr hs
  exact (hasSum_odd_reciprocal_square_of_hasSum hs'.hasSum).tsum_eq

/-- The same identity using the zero-extended complete inverse-square series. -/
theorem odd_reciprocal_square_tsum :
    (∑' k : ℕ,
      1 / ((2 * (k : ℝ) + 1) ^ 2 * (2 * (k : ℝ) + 2) ^ 2)) =
      (∑' n : ℕ, 1 / (n : ℝ) ^ 2) - 2 * Real.log 2 := by
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))
  have hsum : (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2) =
      ∑' n : ℕ, 1 / (n : ℝ) ^ 2 := by
    simpa using hs.tsum_eq_zero_add.symm
  rw [odd_reciprocal_square_tsum_shifted, hsum]

end RiemannResearch.Analysis.OddReciprocalSquare
