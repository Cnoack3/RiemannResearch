/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.CesaroDualTail
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# The complete divisor-escape tail and its explicit LCM rate

Source: user-provided CRT collocation handoff, Section 7. The strict p-series
estimate is the existing integral-comparison theorem `nat_rpow_tail_le`.
All prime-size and prime-power-depth escape remains in the exact sum.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.NumberTheory.DivisorEscapeTail

/-- On the escape set the gcd is a proper divisor, hence at most half the input. -/
theorem two_mul_gcd_le (L n : ℕ) (hn : 0 < n) (hnL : ¬ n ∣ L) :
    2 * Nat.gcd n L ≤ n := by
  obtain ⟨k, hk⟩ := Nat.gcd_dvd_left n L
  have hk2 : 2 ≤ k := by
    by_contra h
    have hc : k = 0 ∨ k = 1 := by omega
    rcases hc with hc | hc
    · simp only [hc, mul_zero] at hk
      omega
    · have he : n = Nat.gcd n L := by simpa only [hc, mul_one] using hk
      apply hnL
      rw [he]
      exact Nat.gcd_dvd_right n L
  calc
    2 * Nat.gcd n L = Nat.gcd n L * 2 := Nat.mul_comm _ _
    _ ≤ Nat.gcd n L * k := Nat.mul_le_mul_left _ hk2
    _ = n := hk.symm

/-- The proper-divisor bound propagates through every nonnegative power. -/
theorem gcd_rpow_le_half (L n : ℕ) (hn : 0 < n) (hnL : ¬ n ∣ L)
    (a : ℝ) (ha : 0 ≤ a) :
    (Nat.gcd n L : ℝ)^a ≤ (2 : ℝ)^(-a) * (n : ℝ)^a := by
  have hgn : 2 * (Nat.gcd n L : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast two_mul_gcd_le L n hn hnL
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ 2 * (Nat.gcd n L : ℝ))
    hgn ha
  rw [Real.mul_rpow (by norm_num : 0 ≤ (2 : ℝ)) (Nat.cast_nonneg _)] at hpow
  have hcancel : (2 : ℝ)^(-a) * (2 : ℝ)^a = 1 := by
    rw [← Real.rpow_add (by norm_num : 0 < (2 : ℝ))]
    simp
  calc
    _ = (2 : ℝ)^(-a) * ((2 : ℝ)^a * (Nat.gcd n L : ℝ)^a) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (by norm_num) _)

/-- One term of the complete positive-integer divisor escape sum. -/
def term (t : ℝ) (L n : ℕ) : ℝ :=
  if n ∣ L then 0 else (n : ℝ) ^ (-t)

/-- The zero coordinate contributes zero for t>1; no physical tail is omitted. -/
def tail (t : ℝ) (L : ℕ) : ℝ := ∑' n : ℕ, term t L n

theorem term_nonneg (t : ℝ) (L n : ℕ) : 0 ≤ term t L n := by
  unfold term
  split_ifs
  · exact le_rfl
  · exact Real.rpow_nonneg (Nat.cast_nonneg n) _

theorem term_le (t : ℝ) (L n : ℕ) : term t L n ≤ (n : ℝ) ^ (-t) := by
  unfold term
  split_ifs
  · exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  · exact le_rfl

theorem term_zero (t : ℝ) (ht : 1 < t) (L : ℕ) : term t L 0 = 0 := by
  have ht0 : -t ≠ 0 := by linarith
  simp [term, Real.zero_rpow ht0]

theorem summable_term (t : ℝ) (ht : 1 < t) (L : ℕ) :
    Summable (term t L) :=
  Summable.of_nonneg_of_le (term_nonneg t L) (term_le t L)
    (Real.summable_nat_rpow.mpr (by linarith))

theorem tail_nonneg (t : ℝ) (L : ℕ) : 0 ≤ tail t L :=
  tsum_nonneg (term_nonneg t L)

theorem summable_shifted_term (t : ℝ) (ht : 1 < t) (L : ℕ) :
    Summable (fun n : ℕ => term t L (n+1)) :=
  (summable_term t ht L).comp_injective (fun _ _ h => Nat.add_right_cancel h)

theorem tsum_shifted_term (t : ℝ) (ht : 1 < t) (L : ℕ) :
    (∑' n : ℕ, term t L (n+1)) = tail t L := by
  have h := (summable_term t ht L).tsum_eq_zero_add
  rw [term_zero t ht L, zero_add] at h
  exact h.symm

/-- Exact subtraction of the finite divisor contribution from the full series. -/
theorem tail_eq_tsum_sub_divisor_sum (t : ℝ) (ht : 1 < t) (L : ℕ) (hL : 0 < L) :
    tail t L = (∑' n : ℕ, (n : ℝ)^(-t)) -
      ∑ d ∈ L.divisors, (d : ℝ)^(-t) := by
  classical
  let saved : ℕ → ℝ := fun n => if n ∈ L.divisors then (n : ℝ)^(-t) else 0
  have hs : Summable saved := by
    apply summable_of_ne_finset_zero (s := L.divisors)
    intro n hn
    simp only [saved, if_neg hn]
  have hL0 : L ≠ 0 := Nat.ne_of_gt hL
  have hsplit (n : ℕ) : (n : ℝ)^(-t) = saved n + term t L n := by
    by_cases hn : n ∣ L
    · have hmem : n ∈ L.divisors := Nat.mem_divisors.mpr ⟨hn, hL0⟩
      simp only [saved, term, if_pos hmem, if_pos hn, add_zero]
    · have hmem : n ∉ L.divisors := fun h => hn (Nat.dvd_of_mem_divisors h)
      simp only [saved, term, if_neg hmem, if_neg hn, zero_add]
  have hfin : (∑' n : ℕ, saved n) = ∑ d ∈ L.divisors, (d : ℝ)^(-t) := by
    rw [tsum_eq_sum (s := L.divisors) (by intro n hn; simp only [saved, if_neg hn])]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [saved, if_pos hn]
  have he : (∑' n : ℕ, (n : ℝ)^(-t)) =
      (∑ d ∈ L.divisors, (d : ℝ)^(-t)) + tail t L := by
    calc
      _ = ∑' n : ℕ, (saved n + term t L n) := tsum_congr hsplit
      _ = _ := by
        rw [hs.tsum_add (summable_term t ht L), hfin]
        rfl
  linarith

/-- This arithmetical cutoff condition covers LCMs and any larger multiples. -/
theorem tail_le_rpow_of_contains_head (t : ℝ) (ht : 1 < t)
    (L M : ℕ) (hM : 0 < M) (hhead : ∀ d : ℕ, 0 < d → d ≤ M → d ∣ L) :
    tail t L ≤ (M : ℝ)^(1-t)/(t-1) := by
  have hp : ∑ n ∈ Finset.range (M+1), term t L n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      exact term_zero t ht L
    · have hd := hhead n (Nat.pos_of_ne_zero hn0) (by
        have := Finset.mem_range.mp hn
        omega)
      simp [term, hd]
  have he := (summable_term t ht L).sum_add_tsum_nat_add (M+1)
  rw [hp, zero_add] at he
  have hs : Summable (fun k : ℕ => ((k+(M+1) : ℕ) : ℝ)^(-t)) :=
    (Real.summable_nat_rpow.mpr (by linarith : -t < -1)).comp_injective
      (fun _ _ h => Nat.add_right_cancel h)
  calc
    tail t L = ∑' k : ℕ, term t L (k+(M+1)) := he.symm
    _ ≤ ∑' k : ℕ, ((k+(M+1) : ℕ) : ℝ)^(-t) :=
      Summable.tsum_le_tsum (fun k => term_le t L (k+(M+1)))
        ((summable_term t ht L).comp_injective (fun _ _ h => Nat.add_right_cancel h)) hs
    _ ≤ (M : ℝ)^(1-t)/(t-1) := by
      simpa only [Nat.add_assoc] using
        RiemannResearch.Analysis.Cesaro.nat_rpow_tail_le t ht M hM

theorem tail_lcmUpto_le (t : ℝ) (ht : 1 < t) (M : ℕ) (hM : 0 < M) :
    tail t (Nat.lcmUpto M) ≤ (M : ℝ)^(1-t)/(t-1) := by
  apply tail_le_rpow_of_contains_head t ht _ M hM
  intro d hd hdM
  exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨hd, hdM⟩)

/-- The complete Euler escape tail vanishes, with no RH assumption. -/
theorem tail_lcmUpto_tendsto_zero (t : ℝ) (ht : 1 < t) :
    Tendsto (fun M : ℕ => tail t (Nat.lcmUpto M)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun M : ℕ => (M : ℝ)^(1-t)/(t-1)) atTop (𝓝 0) := by
    have h := ((tendsto_rpow_neg_atTop (by linarith : 0 < t-1)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun M : ℕ => (M : ℝ)) atTop atTop)).div_const (t-1)
    simpa only [Function.comp_def, neg_sub, zero_div] using h
  refine squeeze_zero' (Eventually.of_forall (fun M => tail_nonneg t _)) ?_ hpow
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
  exact tail_lcmUpto_le t ht M (by omega)

/-- Exact finite escape prefix plus the complete shifted escape remainder. -/
theorem tail_split_at (t : ℝ) (ht : 1 < t) (L N : ℕ) :
    tail t L = (∑ n ∈ Finset.range (N+1), term t L n) +
      ∑' k : ℕ, term t L (k+(N+1)) :=
  ((summable_term t ht L).sum_add_tsum_nat_add (N+1)).symm

/-- A computable improvement: retain the exact escape prefix and bound only
its remaining physical tail. Any positive N is permitted. -/
theorem tail_le_finite_prefix_add_rpow (t : ℝ) (ht : 1 < t)
    (L N : ℕ) (hN : 0 < N) :
    tail t L ≤ (∑ n ∈ Finset.range (N+1), term t L n) +
      (N : ℝ)^(1-t)/(t-1) := by
  have hs : Summable (fun k : ℕ => ((k+(N+1) : ℕ) : ℝ)^(-t)) :=
    (Real.summable_nat_rpow.mpr (by linarith : -t < -1)).comp_injective
      (fun _ _ h => Nat.add_right_cancel h)
  have htail : (∑' k : ℕ, term t L (k+(N+1))) ≤
      (N : ℝ)^(1-t)/(t-1) := by
    calc
      _ ≤ ∑' k : ℕ, ((k+(N+1) : ℕ) : ℝ)^(-t) :=
        Summable.tsum_le_tsum (fun k => term_le t L (k+(N+1)))
          ((summable_term t ht L).comp_injective (fun _ _ h => Nat.add_right_cancel h)) hs
      _ ≤ _ := by
        simpa only [Nat.add_assoc] using
          RiemannResearch.Analysis.Cesaro.nat_rpow_tail_le t ht N hN
  rw [tail_split_at t ht L N]
  exact add_le_add le_rfl htail

/-- Finite escape prefixes are certified lower bounds on the same complete tail. -/
theorem finite_prefix_le_tail (t : ℝ) (ht : 1 < t) (L N : ℕ) :
    (∑ n ∈ Finset.range (N+1), term t L n) ≤ tail t L := by
  rw [tail_split_at t ht L N]
  exact le_add_of_nonneg_right (tsum_nonneg (fun k => term_nonneg t L _))

end RiemannResearch.NumberTheory.DivisorEscapeTail
