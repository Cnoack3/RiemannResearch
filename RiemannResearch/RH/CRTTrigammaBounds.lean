/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoDigammaDerivative

/-!
# Trigamma bounds for the exact conditional-mean CRT progression weights

Source: the prime-block CRT conversation, 18 September 2026.
The trigamma is the derivative of the actual real restriction of
`Complex.digamma`, not an uninterpreted provider. The standard positive series
is DLMF 5.15.1. All infinite sums below are proved summable first.
-/

open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.CRTBlock
noncomputable section
open Pareto

def trigamma (x : ℝ) : ℝ :=
  deriv (fun y : ℝ => (Complex.digamma (y : ℂ)).re) x

theorem reciprocalSquareSeries_summable_pos {x : ℝ} (hx : 0 < x) :
    Summable (fun k : ℕ => 1 / ((k : ℝ) + x)^2) := by
  have hs := reciprocalSquareSeries_summable (show 1 ≤ x + 1 by linarith)
  apply (summable_nat_add_iff 1).mp
  simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hs

theorem reciprocalSquareSeries_shift {x : ℝ} (hx : 0 < x) :
    reciprocalSquareSeries x = 1 / x^2 + reciprocalSquareSeries (x + 1) := by
  have h := (reciprocalSquareSeries_summable_pos hx).sum_add_tsum_nat_add 1
  simpa [reciprocalSquareSeries, Nat.cast_add, Nat.cast_one, add_assoc,
    add_comm, add_left_comm] using h.symm

/-- Extend the existing derivative identification from x > 1/2 to all x > 0. -/
theorem hasDerivAt_re_digamma_pos {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (Complex.digamma (y : ℂ)).re)
      (reciprocalSquareSeries x) x := by
  have hd := (hasDerivAt_re_digamma_reciprocalSquareSeries
    (show (1 / 2 : ℝ) < x + 1 by linarith)).comp x
      ((hasDerivAt_id x).add_const 1)
  have hi : HasDerivAt (fun y : ℝ => 1 / y) (-(1 / x^2)) x := by
    convert (hasDerivAt_id x).inv (ne_of_gt hx) using 1 <;> try rfl
    all_goals first | (funext y; simp [one_div]) | (simp [neg_div])
  have he : reciprocalSquareSeries (x + 1) - -(1 / x^2) =
      reciprocalSquareSeries x := by
    rw [reciprocalSquareSeries_shift hx]
    ring
  have hd' : HasDerivAt
      (fun y : ℝ => (Complex.digamma ((y + 1 : ℝ) : ℂ)).re - 1 / y)
      (reciprocalSquareSeries x) x := by
    convert hd.sub hi using 1 <;> try rfl
    all_goals first | (funext y; rfl) | (simpa only [mul_one] using he.symm)
  apply hd'.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
  rw [re_digamma_add_one hy]
  ring

theorem trigamma_eq_series {x : ℝ} (hx : 0 < x) :
    trigamma x = ∑' k : ℕ, 1 / ((k : ℝ) + x)^2 :=
  (hasDerivAt_re_digamma_pos hx).deriv

def progressionSquare (Q r : ℝ) : ℝ :=
  ∑' k : ℕ, 1 / (Q * (k : ℝ) + r)^2

def lKernel (t : ℝ) : ℝ := 2 / (t * (t + 1) * (t + 2))

def progressionL (Q r : ℝ) : ℝ := ∑' k : ℕ, lKernel (Q * (k : ℝ) + r)

def progressionM (Q r : ℝ) : ℝ :=
  ∑' k : ℕ, lKernel (Q * (k : ℝ) + r) / (Q * (k : ℝ) + r)

theorem square_scale (Q r k : ℝ) (hQ : Q ≠ 0) :
    1 / (Q * k + r)^2 = (1 / Q^2) * (1 / (k + r / Q)^2) := by
  have he : Q * k + r = Q * (k + r / Q) := by field_simp
  rw [he, mul_pow]
  simp [div_eq_mul_inv, mul_comm]

theorem progressionSquare_summable {Q r : ℝ} (hQ : 0 < Q) (hr : 0 < r) :
    Summable (fun k : ℕ => 1 / (Q * (k : ℝ) + r)^2) := by
  have h := (reciprocalSquareSeries_summable_pos (div_pos hr hQ)).mul_left (1 / Q^2)
  exact h.congr (fun k => (square_scale Q r k (ne_of_gt hQ)).symm)

theorem progressionSquare_eq_trigamma {Q r : ℝ} (hQ : 0 < Q) (hr : 0 < r) :
    progressionSquare Q r = trigamma (r / Q) / Q^2 := by
  simp_rw [progressionSquare, square_scale Q r _ (ne_of_gt hQ)]
  rw [tsum_mul_left, trigamma_eq_series (div_pos hr hQ)]
  ring

theorem lKernel_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ lKernel t := by
  unfold lKernel
  positivity

theorem lKernel_upper_difference {t : ℝ} (ht : 0 < t) :
    lKernel t ≤ 1 / t^2 - 1 / (t + 1)^2 := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have ht1 : t + 1 ≠ 0 := by positivity
  have ht2 : t + 2 ≠ 0 := by positivity
  have he : 1 / t^2 - 1 / (t + 1)^2 - lKernel t =
      (3 * t + 2) / (t^2 * (t + 1)^2 * (t + 2)) := by
    unfold lKernel
    field_simp
    <;> ring
  have hp : 0 ≤ (3 * t + 2) / (t^2 * (t + 1)^2 * (t + 2)) := by positivity
  linarith

theorem lKernel_lower_difference {t : ℝ} (ht : 0 < t) :
    1 / (t + 1)^2 - 1 / (t + 2)^2 ≤ lKernel t := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have ht1 : t + 1 ≠ 0 := by positivity
  have ht2 : t + 2 ≠ 0 := by positivity
  have he : lKernel t - (1 / (t + 1)^2 - 1 / (t + 2)^2) =
      (3 * t + 4) / (t * (t + 1)^2 * (t + 2)^2) := by
    unfold lKernel
    field_simp
    <;> ring
  have hp : 0 ≤ (3 * t + 4) / (t * (t + 1)^2 * (t + 2)^2) := by positivity
  linarith

theorem lKernel_le_square {t : ℝ} (ht : 0 < t) : lKernel t ≤ 1 / t^2 := by
  have h := lKernel_upper_difference ht
  have : 0 ≤ 1 / (t + 1)^2 := by positivity
  linarith

theorem progressionL_summable {Q r : ℝ} (hQ : 0 < Q) (hr : 0 < r) :
    Summable (fun k : ℕ => lKernel (Q * (k : ℝ) + r)) := by
  apply Summable.of_nonneg_of_le (fun k => lKernel_nonneg (by positivity))
    (fun k => lKernel_le_square (by positivity))
  exact progressionSquare_summable hQ hr

/-- Two-sided bounds in the actual trigamma, retaining the first progression atom. -/
theorem progressionL_trigamma_sandwich {Q r : ℝ} (hQ : 0 < Q) (hr : 0 < r) :
    (trigamma ((r + 1) / Q) - trigamma ((r + 2) / Q)) / Q^2 ≤ progressionL Q r ∧
    progressionL Q r ≤ (trigamma (r / Q) - trigamma ((r + 1) / Q)) / Q^2 := by
  have hs0 := progressionSquare_summable hQ hr
  have hs1 := progressionSquare_summable hQ (show 0 < r + 1 by positivity)
  have hs2 := progressionSquare_summable hQ (show 0 < r + 2 by positivity)
  have hl := progressionL_summable hQ hr
  have he (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
      (∑' k : ℕ, (1 / (Q * (k : ℝ) + a)^2 - 1 / (Q * (k : ℝ) + b)^2)) =
        (trigamma (a / Q) - trigamma (b / Q)) / Q^2 := by
    rw [(progressionSquare_summable hQ ha).tsum_sub
      (progressionSquare_summable hQ hb)]
    change progressionSquare Q a - progressionSquare Q b = _
    rw [progressionSquare_eq_trigamma hQ ha, progressionSquare_eq_trigamma hQ hb,
      sub_div]
  constructor
  · rw [← he (r + 1) (r + 2) (by positivity) (by positivity)]
    apply Summable.tsum_le_tsum _ (hs1.sub hs2) hl
    intro k
    simpa only [add_assoc] using lKernel_lower_difference
      (show 0 < Q * (k : ℝ) + r by positivity)
  · rw [← he r (r + 1) hr (by positivity)]
    apply Summable.tsum_le_tsum _ hl (hs0.sub hs1)
    intro k
    simpa only [add_assoc] using lKernel_upper_difference
      (show 0 < Q * (k : ℝ) + r by positivity)

theorem progressionM_summable {Q r : ℝ} (hQ : 0 < Q) (hr : 0 < r) :
    Summable (fun k : ℕ => lKernel (Q * (k : ℝ) + r) / (Q * (k : ℝ) + r)) := by
  apply Summable.of_nonneg_of_le (fun k => div_nonneg (lKernel_nonneg (by positivity))
    (by positivity))
  · intro k
    exact div_le_div_of_nonneg_left (lKernel_nonneg (by positivity)) hr
      (le_add_of_nonneg_left (mul_nonneg (le_of_lt hQ) (Nat.cast_nonneg k)))
  · exact (progressionL_summable hQ hr).div_const r

theorem progressionM_le_L_div {Q r : ℝ} (hQ : 0 < Q) (hr : 0 < r) :
    progressionM Q r ≤ progressionL Q r / r := by
  unfold progressionM progressionL
  rw [← tsum_div_const]
  apply Summable.tsum_le_tsum _ (progressionM_summable hQ hr)
    ((progressionL_summable hQ hr).div_const r)
  intro k
  exact div_le_div_of_nonneg_left (lKernel_nonneg (by positivity)) hr
    (le_add_of_nonneg_left (mul_nonneg (le_of_lt hQ) (Nat.cast_nonneg k)))

end
end RiemannResearch.RH.CRTBlock
