/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Rational certificates for complete inverse-square progression tails

Source: independently developed telescoping proof in the user-requested
complete-Q energy audit, 18 October 2026. The rational step identities retain
their exact positive and negative remainders; summation and limits certify
the complete infinite series. The RH audit uses positive rescaling after a
finite progression prefix. No special-function numerical value is assumed.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.InverseSquareTailCertificates
open Filter
open scoped Topology
def upper (x : ℝ) : ℝ := 1/x + (1/x)^2/2 + (1/x)^3/6
def lower (x : ℝ) : ℝ := upper x - (1/x)^5/30
theorem upper_step (x : ℝ) (hx : 0 < x) :
    upper x - upper (x+1) - 1/x^2 = 1/(6*x^3*(x+1)^3) := by
  unfold upper
  field_simp
  ring
theorem lower_step (x : ℝ) (hx : 0 < x) :
    lower x - lower (x+1) - 1/x^2 =
      -(5*x^2+5*x+1)/(30*x^5*(x+1)^5) := by
  unfold lower upper
  field_simp
  ring
theorem finite_upper (x : ℝ) (hx : 0 < x) (n : ℕ) :
    (∑ k ∈ Finset.range n, 1/(x+(k:ℝ))^2) ≤ upper x - upper (x+(n:ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hp : 0 < x+(n:ℝ) := by positivity
    have hs := upper_step (x+(n:ℝ)) hp
    have hr : 0 ≤ 1/(6*(x+(n:ℝ))^3*(x+(n:ℝ)+1)^3) := by positivity
    push_cast
    rw [← add_assoc]
    linarith
theorem finite_lower (x : ℝ) (hx : 0 < x) (n : ℕ) :
    lower x - lower (x+(n:ℝ)) ≤ ∑ k ∈ Finset.range n, 1/(x+(k:ℝ))^2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hp : 0 < x+(n:ℝ) := by positivity
    have hs := lower_step (x+(n:ℝ)) hp
    have hr : -(5*(x+(n:ℝ))^2+5*(x+(n:ℝ))+1)/
      (30*(x+(n:ℝ))^5*(x+(n:ℝ)+1)^5) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg
        · have : 0 ≤ 5*(x+(n:ℝ))^2+5*(x+(n:ℝ))+1 := by positivity
          linarith
        · positivity
    push_cast
    rw [← add_assoc]
    linarith
theorem tail_summable (x : ℝ) (hx : 1 ≤ x) :
    Summable (fun n : ℕ => 1/(x+(n:ℝ))^2) := by
  apply Summable.of_nonneg_of_le (fun n => by positivity) _
    ((summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))))
  intro n
  have h : (0 : ℝ) < (n:ℝ)+1 := by positivity
  have hle : (n:ℝ)+1 ≤ x+(n:ℝ) := by linarith
  have hs : ((n:ℝ)+1)^2 ≤ (x+(n:ℝ))^2 := by nlinarith
  exact one_div_le_one_div_of_le (by positivity) (by simpa using hs)
theorem upper_tendsto_zero (x : ℝ) (hx : 0 < x) :
    Tendsto (fun n : ℕ => upper (x+(n:ℝ))) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => x+(n:ℝ)) atTop atTop := by
    apply Filter.tendsto_atTop_mono _ tendsto_natCast_atTop_atTop
    intro n
    linarith
  have hi := ht.const_div_atTop (1 : ℝ)
  simpa only [upper, zero_pow (by norm_num : 2 ≠ 0),
    zero_pow (by norm_num : 3 ≠ 0), zero_div, add_zero] using
    (hi.add ((hi.pow 2).div_const 2)).add ((hi.pow 3).div_const 6)
theorem lower_tendsto_zero (x : ℝ) (hx : 0 < x) :
    Tendsto (fun n : ℕ => lower (x+(n:ℝ))) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => x+(n:ℝ)) atTop atTop := by
    apply Filter.tendsto_atTop_mono _ tendsto_natCast_atTop_atTop
    intro n
    linarith
  have hi := ht.const_div_atTop (1 : ℝ)
  simpa only [lower, zero_pow (by norm_num : 5 ≠ 0), zero_div, sub_zero] using
    (upper_tendsto_zero x hx).sub ((hi.pow 5).div_const 30)
theorem complete_tail_bounds (x : ℝ) (hx : 1 ≤ x) :
    lower x ≤ (∑' n : ℕ, 1/(x+(n:ℝ))^2) ∧
      (∑' n : ℕ, 1/(x+(n:ℝ))^2) ≤ upper x := by
  have hp : 0 < x := by linarith
  have hs := (tail_summable x hx).tendsto_sum_tsum_nat
  constructor
  · have h := le_of_tendsto_of_tendsto
      (tendsto_const_nhds.sub (lower_tendsto_zero x hp)) hs
      (Filter.Eventually.of_forall (finite_lower x hp))
    simpa only [sub_zero] using h
  · have h := le_of_tendsto_of_tendsto hs
      (tendsto_const_nhds.sub (upper_tendsto_zero x hp))
      (Filter.Eventually.of_forall (finite_upper x hp))
    simpa only [sub_zero] using h
theorem scaled_complete_tail_bounds (x L : ℝ) (hx : 1 ≤ x) (hL : 0 < L) :
    lower x / L^2 ≤ (∑' n : ℕ, 1/(L*x+(n:ℝ)*L)^2) ∧
      (∑' n : ℕ, 1/(L*x+(n:ℝ)*L)^2) ≤ upper x / L^2 := by
  have he : (∑' n : ℕ, 1/(L*x+(n:ℝ)*L)^2) =
      (∑' n : ℕ, 1/(x+(n:ℝ))^2) / L^2 := by
    rw [← tsum_div_const]
    apply tsum_congr
    intro n
    have hn : 0 < x+(n:ℝ) := by positivity
    field_simp
  rw [he]
  exact ⟨div_le_div_of_nonneg_right (complete_tail_bounds x hx).1 (sq_nonneg L),
    div_le_div_of_nonneg_right (complete_tail_bounds x hx).2 (sq_nonneg L)⟩
end RiemannResearch.Analysis.InverseSquareTailCertificates
