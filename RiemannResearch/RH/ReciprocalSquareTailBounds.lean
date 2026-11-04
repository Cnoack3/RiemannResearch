/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CRTTrigammaBounds
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rational enclosures for complete reciprocal-square tails

Source: the user's request to verify the residue Gram matrix numerics,
4 November 2026. The functions are the finite Bernoulli expansions through
orders seven and nine. The proof uses exact rational difference identities,
positive polynomials, finite telescoping, and passage to the full summable
series. It does not appeal to a floating-point special-function evaluator.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.ReciprocalSquareTailBounds
open CRTBlock ZetaTwoProbability

def upper (x : ℝ) : ℝ :=
  x⁻¹ + (x⁻¹)^2 / 2 + (x⁻¹)^3 / 6 - (x⁻¹)^5 / 30 + (x⁻¹)^7 / 42

def lower (x : ℝ) : ℝ := upper x - (x⁻¹)^9 / 30

theorem upper_difference (x : ℝ) (hx : 0 < x) :
    upper x - upper (x + 1) - 1 / x^2 =
      (63*x^4 + 126*x^3 + 98*x^2 + 35*x + 5) /
        (210*x^7*(x + 1)^7) := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hx1 : x + 1 ≠ 0 := by positivity
  unfold upper
  field_simp
  <;> ring

theorem lower_difference (x : ℝ) (hx : 0 < x) :
    lower x - lower (x + 1) - 1 / x^2 =
      -(175*x^6 + 525*x^5 + 709*x^4 + 543*x^3 + 247*x^2 + 63*x + 7) /
        (210*x^9*(x + 1)^9) := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hx1 : x + 1 ≠ 0 := by positivity
  unfold lower upper
  field_simp
  <;> ring

theorem square_le_upper_difference (x : ℝ) (hx : 0 < x) :
    1 / x^2 ≤ upper x - upper (x + 1) := by
  have h := upper_difference x hx
  have hp : 0 ≤ (63*x^4 + 126*x^3 + 98*x^2 + 35*x + 5) /
      (210*x^7*(x + 1)^7) := by positivity
  linarith

theorem lower_difference_le_square (x : ℝ) (hx : 0 < x) :
    lower x - lower (x + 1) ≤ 1 / x^2 := by
  have h := lower_difference x hx
  have hp : 0 ≤ (175*x^6 + 525*x^5 + 709*x^4 + 543*x^3 +
      247*x^2 + 63*x + 7) / (210*x^9*(x + 1)^9) := by positivity
  rw [neg_div] at h
  linarith

theorem upper_sub_lower (x : ℝ) :
    upper x - lower x = 1 / (30*x^9) := by
  simp only [lower, sub_sub_cancel, inv_pow, one_div, mul_inv_rev]
  ring

theorem upper_tendsto_zero (x : ℝ) :
    Tendsto (fun n : ℕ => upper ((n : ℝ) + x)) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) + x) atTop atTop :=
    tendsto_atTop_add_const_right atTop x tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => ((n : ℝ) + x)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ht
  have h := (((hi.add ((hi.pow 2).div_const 2)).add ((hi.pow 3).div_const 6)).sub
    ((hi.pow 5).div_const 30)).add ((hi.pow 7).div_const 42)
  simpa [upper] using h

theorem lower_tendsto_zero (x : ℝ) :
    Tendsto (fun n : ℕ => lower ((n : ℝ) + x)) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) + x) atTop atTop :=
    tendsto_atTop_add_const_right atTop x tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => ((n : ℝ) + x)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ht
  have h := (upper_tendsto_zero x).sub ((hi.pow 9).div_const 30)
  simpa [lower] using h

def head (x : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + x)^2

theorem head_le_upper (x : ℝ) (hx : 0 < x) (N : ℕ) :
    head x N ≤ upper x - upper ((N : ℝ) + x) := by
  induction N with
  | zero => simp [head]
  | succ N ih =>
    have h := square_le_upper_difference ((N : ℝ) + x) (by positivity)
    rw [head, Finset.sum_range_succ]
    change head x N + 1 / ((N : ℝ) + x)^2 ≤ _
    have he : ((N + 1 : ℕ) : ℝ) + x = ((N : ℝ) + x) + 1 := by
      push_cast
      ring
    rw [he]
    linarith

theorem lower_le_head (x : ℝ) (hx : 0 < x) (N : ℕ) :
    lower x - lower ((N : ℝ) + x) ≤ head x N := by
  induction N with
  | zero => simp [head]
  | succ N ih =>
    have h := lower_difference_le_square ((N : ℝ) + x) (by positivity)
    rw [head, Finset.sum_range_succ]
    change _ ≤ head x N + 1 / ((N : ℝ) + x)^2
    have he : ((N + 1 : ℕ) : ℝ) + x = ((N : ℝ) + x) + 1 := by
      push_cast
      ring
    rw [he]
    linarith

theorem trigamma_sandwich (x : ℝ) (hx : 0 < x) :
    lower x ≤ trigamma x ∧ trigamma x ≤ upper x := by
  have hs : Tendsto (head x) atTop (𝓝 (trigamma x)) := by
    rw [trigamma_eq_series hx]
    exact (reciprocalSquareSeries_summable_pos hx).hasSum.tendsto_sum_nat
  constructor
  · have h := le_of_tendsto_of_tendsto
      (tendsto_const_nhds.sub (lower_tendsto_zero x)) hs
      (Filter.Eventually.of_forall (lower_le_head x hx))
    simpa only [sub_zero] using h
  · have h := le_of_tendsto_of_tendsto hs
      (tendsto_const_nhds.sub (upper_tendsto_zero x))
      (Filter.Eventually.of_forall (head_le_upper x hx))
    simpa only [sub_zero] using h

theorem trigamma_head_shift (x : ℝ) (hx : 0 < x) (N : ℕ) :
    trigamma x = head x N + trigamma ((N : ℝ) + x) := by
  rw [trigamma_eq_series hx,
    trigamma_eq_series (show 0 < (N : ℝ) + x by positivity)]
  simpa only [head, Nat.cast_add, add_assoc] using
    ((reciprocalSquareSeries_summable_pos hx).sum_add_tsum_nat_add N).symm

theorem trigamma_head_sandwich (x : ℝ) (hx : 0 < x) (N : ℕ) :
    head x N + lower ((N : ℝ) + x) ≤ trigamma x ∧
      trigamma x ≤ head x N + upper ((N : ℝ) + x) := by
  rw [trigamma_head_shift x hx N]
  have h := trigamma_sandwich ((N : ℝ) + x) (by positivity : 0 < (N : ℝ) + x)
  exact ⟨add_le_add (le_refl _) h.1, add_le_add (le_refl _) h.2⟩

theorem zetaTwo_eq_trigamma_one : zetaTwo = trigamma 1 := by
  rw [zetaTwo_eq_nat_sum, trigamma_eq_series (by norm_num : (0 : ℝ) < 1)]
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  rw [hs.tsum_eq_zero_add]
  simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, div_zero, zero_add, Nat.cast_add, Nat.cast_one]

end RiemannResearch.RH.ReciprocalSquareTailBounds
