/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteStrictTail
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Second moments from finite exponential strict tails

Source: user-provided argument of 22 October 2026. The exact layer-cake
identity retains the finite endpoint. The elementary exponential integral is
evaluated with its full endpoint term before deriving the second-moment bound.
These finite real-variable results have no zeta or RH premise.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteStrictTail

/-- Exact finite second-moment layer cake, including displacements equal to zero. -/
theorem secondMoment_eq_integral {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hx : ∀ i ∈ s, x i ∈ Icc (0 : ℝ) B) :
    (∑ i ∈ s, (x i) ^ 2) =
      ∫ t in (0 : ℝ)..B, tail s x t * (2 * t) := by
  have h := layerCake s x (fun t => t ^ 2) (fun t => 2 * t)
    (by fun_prop)
    (fun t => by
      convert (hasDerivAt_id t).pow 2 using 1 <;>
        first | rfl | simp)
    0 B hB (fun i hi => (hx i hi).2)
  have heq : badSum s x (fun t => t ^ 2) 0 = ∑ i ∈ s, (x i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only
    split_ifs with hpos
    · rfl
    · have hz : x i = 0 := le_antisymm (le_of_not_gt hpos) (hx i hi).1
      simp [hz]
  simpa only [heq, zero_pow (by norm_num : 2 ≠ 0), zero_mul, zero_add] using h

/-- Exact truncated exponential first moment, with the upper endpoint retained. -/
theorem integral_linear_exponential (a B : ℝ) (ha : 0 < a) :
    (∫ t in (0 : ℝ)..B, t * Real.exp (-a * t)) =
      (1 - (1 + a * B) * Real.exp (-a * B)) / a ^ 2 := by
  have hderiv : ∀ t : ℝ, HasDerivAt
      (fun x : ℝ => (-(a * x + 1) * Real.exp (-a * x)) / a ^ 2)
      (t * Real.exp (-a * t)) t := by
    intro t
    have h := (((hasDerivAt_id t).const_mul a).add_const 1).neg.mul
      ((Real.hasDerivAt_exp (-a * t)).comp t ((hasDerivAt_id t).const_mul (-a)))
    convert h.div_const (a ^ 2) using 1 <;>
      first
      | rfl
      | (simp only [Pi.neg_apply, Pi.mul_apply, Function.comp_apply, id_eq]
         field_simp [ne_of_gt ha]
         ring)
  have hc : Continuous (fun t : ℝ => t * Real.exp (-a * t)) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hderiv t) (hc.intervalIntegrable 0 B)]
  simp only [mul_zero, Real.exp_zero, zero_add, neg_mul, one_mul]
  ring

/-- An exponential strict tail bounds the complete finite second moment. -/
theorem secondMoment_le_exponential_tail {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (B M a : ℝ) (hB : 0 ≤ B) (hM : 0 ≤ M) (ha : 0 < a)
    (hx : ∀ i ∈ s, x i ∈ Icc (0 : ℝ) B)
    (htail : ∀ t ∈ Icc (0 : ℝ) B, tail s x t ≤ M * Real.exp (-a * t)) :
    (∑ i ∈ s, (x i) ^ 2) ≤ 2 * M / a ^ 2 := by
  rw [secondMoment_eq_integral s x B hB hx]
  calc
    _ ≤ ∫ t in (0 : ℝ)..B, (M * Real.exp (-a * t)) * (2 * t) := by
      have hc : Continuous (fun t : ℝ =>
          (M * Real.exp (-a * t)) * (2 * t)) := by fun_prop
      apply intervalIntegral.integral_mono_on hB
        (intervalIntegrable_tail_mul s x (fun t => 2 * t) (by fun_prop) 0 B)
        (hc.intervalIntegrable 0 B)
      intro t ht
      exact mul_le_mul_of_nonneg_right (htail t ht) (mul_nonneg (by norm_num) ht.1)
    _ = (2 * M) * ((1 - (1 + a * B) * Real.exp (-a * B)) / a ^ 2) := by
      rw [show (fun t : ℝ => (M * Real.exp (-a * t)) * (2 * t)) =
        (fun t : ℝ => (2 * M) * (t * Real.exp (-a * t))) by funext t; ring,
        intervalIntegral.integral_const_mul, integral_linear_exponential a B ha]
    _ ≤ 2 * M / a ^ 2 := by
      have hpos : 0 ≤ (1 + a * B) * Real.exp (-a * B) := by positivity
      have h := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (show 1 - (1 + a * B) *
          Real.exp (-a * B) ≤ 1 by linarith) (sq_nonneg a))
        (show 0 ≤ 2 * M by positivity)
      convert h using 1 <;> first | rfl | ring

end RiemannResearch.Analysis.FiniteStrictTail
