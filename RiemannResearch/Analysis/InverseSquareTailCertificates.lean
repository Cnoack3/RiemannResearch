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

/-!
# High-order rational complete-tail enclosures

Source: the ten-correction computation in the user-provided
Reciprocal_Head_Investigation_2026-11-07.md. The proof uses exact rational
step identities and limits, so no external Euler--Maclaurin remainder is
assumed. The coefficient list is the classical Bernoulli list B₂ through B₂₀;
the name records this truncation order, not a claim of novelty.
-/

noncomputable section
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.InverseSquareTailCertificates
open Filter

def upperNine {𝕜 : Type*} [Field 𝕜] (x : 𝕜) : 𝕜 :=
  1/x + (1/x)^2/2 + (1/x)^3/6 - (1/x)^5/30 + (1/x)^7/42 -
    (1/x)^9/30 + 5*(1/x)^11/66 - 691*(1/x)^13/2730 +
    7*(1/x)^15/6 - 3617*(1/x)^17/510 + 43867*(1/x)^19/798

def lowerTen {𝕜 : Type*} [Field 𝕜] (x : 𝕜) : 𝕜 := upperNine x - 174611*(1/x)^21/330

def upperNineNumerator (x : ℝ) : ℝ :=
  533203385 + 10130864315*x + 91108987112*x^2 +
    515367037328*x^3 + 2054944251932*x^4 + 6133644790988*x^5 +
    14202170156504*x^6 + 26078060860544*x^7 + 38477564123606*x^8 +
    45919205903034*x^9 + 44354489554008*x^10 + 34488100166160*x^11 +
    21303700067772*x^12 + 10197362752668*x^13 + 3612349379184*x^14 +
    862233308664*x^15 + 107779163583*x^16

def lowerTenNumerator (x : ℝ) : ℝ :=
  5132341123 + 107779163583*x + 1077258432445*x^2 +
    6814816422505*x^3 + 30605157702028*x^4 + 103730293636060*x^5 +
    275324571384772*x^6 + 586029725450260*x^7 + 1015855691128858*x^8 +
    1447932980318850*x^9 + 1705422975538870*x^10 + 1661306436529278*x^11 +
    1333878560799708*x^12 + 875263809942060*x^13 + 462154235828340*x^14 +
    191208495644100*x^15 + 59127234559635*x^16 + 12432766801455*x^17 +
    1381418533495*x^18

theorem upperNine_step (x : ℝ) (hx : 0 < x) :
    upperNine x - upperNine (x+1) - 1/x^2 =
      upperNineNumerator x / (9699690*x^19*(x+1)^19) := by
  unfold upperNine upperNineNumerator
  field_simp
  <;> ring

theorem lowerTen_step (x : ℝ) (hx : 0 < x) :
    lowerTen x - lowerTen (x+1) - 1/x^2 =
      -lowerTenNumerator x / (9699690*x^21*(x+1)^21) := by
  unfold lowerTen upperNine lowerTenNumerator
  field_simp
  <;> ring

theorem finite_upperNine (x : ℝ) (hx : 0 < x) (n : ℕ) :
    (∑ k ∈ Finset.range n, 1/(x+(k:ℝ))^2) ≤
      upperNine x - upperNine (x+(n:ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hp : 0 < x+(n:ℝ) := by positivity
    have hs := upperNine_step (x+(n:ℝ)) hp
    have hr : 0 ≤ upperNineNumerator (x+(n:ℝ)) /
        (9699690*(x+(n:ℝ))^19*(x+(n:ℝ)+1)^19) := by
      unfold upperNineNumerator
      positivity
    push_cast
    rw [← add_assoc]
    linarith

theorem finite_lowerTen (x : ℝ) (hx : 0 < x) (n : ℕ) :
    lowerTen x - lowerTen (x+(n:ℝ)) ≤
      ∑ k ∈ Finset.range n, 1/(x+(k:ℝ))^2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hp : 0 < x+(n:ℝ) := by positivity
    have hs := lowerTen_step (x+(n:ℝ)) hp
    have hr : -lowerTenNumerator (x+(n:ℝ)) /
        (9699690*(x+(n:ℝ))^21*(x+(n:ℝ)+1)^21) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg
      · have : 0 ≤ lowerTenNumerator (x+(n:ℝ)) := by
          unfold lowerTenNumerator
          positivity
        linarith
      · positivity
    push_cast
    rw [← add_assoc]
    linarith

theorem upperNine_tendsto_zero (x : ℝ) (hx : 0 < x) :
    Tendsto (fun n : ℕ => upperNine (x+(n:ℝ))) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => x+(n:ℝ)) atTop atTop := by
    apply Filter.tendsto_atTop_mono _ tendsto_natCast_atTop_atTop
    intro n
    linarith
  have hi := ht.const_div_atTop (1 : ℝ)
  have h := (((((((((hi.add ((hi.pow 2).div_const 2)).add
    ((hi.pow 3).div_const 6)).sub ((hi.pow 5).div_const 30)).add
    ((hi.pow 7).div_const 42)).sub ((hi.pow 9).div_const 30)).add
    (((hi.pow 11).const_mul 5).div_const 66)).sub
    (((hi.pow 13).const_mul 691).div_const 2730)).add
    (((hi.pow 15).const_mul 7).div_const 6)).sub
    (((hi.pow 17).const_mul 3617).div_const 510)).add
    (((hi.pow 19).const_mul 43867).div_const 798)
  simpa only [upperNine, zero_pow (by norm_num : 2 ≠ 0),
    zero_pow (by norm_num : 3 ≠ 0), zero_pow (by norm_num : 5 ≠ 0),
    zero_pow (by norm_num : 7 ≠ 0), zero_pow (by norm_num : 9 ≠ 0),
    zero_pow (by norm_num : 11 ≠ 0), zero_pow (by norm_num : 13 ≠ 0),
    zero_pow (by norm_num : 15 ≠ 0), zero_pow (by norm_num : 17 ≠ 0),
    zero_pow (by norm_num : 19 ≠ 0), zero_div, mul_zero,
    add_zero, sub_zero] using h

theorem lowerTen_tendsto_zero (x : ℝ) (hx : 0 < x) :
    Tendsto (fun n : ℕ => lowerTen (x+(n:ℝ))) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => x+(n:ℝ)) atTop atTop := by
    apply Filter.tendsto_atTop_mono _ tendsto_natCast_atTop_atTop
    intro n
    linarith
  have hi := ht.const_div_atTop (1 : ℝ)
  simpa only [lowerTen, zero_pow (by norm_num : 21 ≠ 0),
    mul_zero, zero_div, sub_zero] using
    (upperNine_tendsto_zero x hx).sub (((hi.pow 21).const_mul 174611).div_const 330)

theorem complete_tail_ten_bounds (x : ℝ) (hx : 1 ≤ x) :
    lowerTen x ≤ (∑' n : ℕ, 1/(x+(n:ℝ))^2) ∧
      (∑' n : ℕ, 1/(x+(n:ℝ))^2) ≤ upperNine x := by
  have hp : 0 < x := by linarith
  have hs := (tail_summable x hx).tendsto_sum_tsum_nat
  constructor
  · have h := le_of_tendsto_of_tendsto
      (tendsto_const_nhds.sub (lowerTen_tendsto_zero x hp)) hs
      (Filter.Eventually.of_forall (finite_lowerTen x hp))
    simpa only [sub_zero] using h
  · have h := le_of_tendsto_of_tendsto hs
      (tendsto_const_nhds.sub (upperNine_tendsto_zero x hp))
      (Filter.Eventually.of_forall (finite_upperNine x hp))
    simpa only [sub_zero] using h

theorem scaled_complete_tail_ten_bounds (x L : ℝ) (hx : 1 ≤ x) (hL : 0 < L) :
    lowerTen x / L^2 ≤ (∑' n : ℕ, 1/(L*x+(n:ℝ)*L)^2) ∧
      (∑' n : ℕ, 1/(L*x+(n:ℝ)*L)^2) ≤ upperNine x / L^2 := by
  have he : (∑' n : ℕ, 1/(L*x+(n:ℝ)*L)^2) =
      (∑' n : ℕ, 1/(x+(n:ℝ))^2) / L^2 := by
    rw [← tsum_div_const]
    apply tsum_congr
    intro n
    have hn : 0 < x+(n:ℝ) := by positivity
    field_simp
  rw [he]
  exact ⟨div_le_div_of_nonneg_right (complete_tail_ten_bounds x hx).1 (sq_nonneg L),
    div_le_div_of_nonneg_right (complete_tail_ten_bounds x hx).2 (sq_nonneg L)⟩

end RiemannResearch.Analysis.InverseSquareTailCertificates
