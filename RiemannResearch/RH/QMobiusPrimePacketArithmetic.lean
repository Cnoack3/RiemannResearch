/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimeSieve
import RiemannResearch.RH.CanonicalMobiusConditionalHead
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
/-!
# Exact Möbius-weighted prime-packet arithmetic

Source: user-provided prime-packet research agenda, 16 October 2026.
Möbius inclusion-exclusion reuses QPrimeSieve.divisor_sift. All integer
quotients are retained. This identity is valid for every positive L and p;
squarefreeness and primality are needed only by its legal-stage consumer.
-/
open scoped BigOperators
namespace RiemannResearch.RH.QMobiusPrimePacket
open ArithmeticCumulative QPrimeSieve Pareto
noncomputable section

def arithmeticPacket (L p n : ℕ) : ℝ :=
  ∑ d ∈ L.divisors, (ArithmeticFunction.moebius d : ℝ) * residueFraction (p*d) n

theorem coprimeCount_eq_floor_sum (L x : ℕ) (hL : L ≠ 0) :
    coprimeCount L x =
      ∑ d ∈ L.divisors, (ArithmeticFunction.moebius d : ℝ) * ((x/d : ℕ) : ℝ) := by
  calc
    _ = ∑ k ∈ Finset.range x, ∑ d ∈ L.divisors,
        (ArithmeticFunction.moebius d : ℝ) * divisorIndicator d (k+1) := by
      unfold coprimeCount cumulative
      apply Finset.sum_congr rfl
      intro k _
      exact (divisor_sift L (k+1) hL).symm
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.mul_sum]
      congr 1
      exact cumulative_divisorIndicator d x (Nat.pos_of_mem_divisors hd)

theorem arithmeticPacket_eq_all_floors (L p n : ℕ) (hp : 0 < p) :
    arithmeticPacket L p n =
      (n:ℝ)/(p:ℝ)*divisorDensity L -
        ∑ d ∈ L.divisors, (ArithmeticFunction.moebius d : ℝ) *
          ((n/(p*d) : ℕ) : ℝ) := by
  unfold arithmeticPacket divisorDensity
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [residueFraction_eq_div_sub_floor (p*d) n
    (Nat.mul_pos hp (Nat.pos_of_mem_divisors hd))]
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem arithmeticPacket_eq_count (L p n : ℕ) (hL : L ≠ 0) (hp : 0 < p) :
    arithmeticPacket L p n =
      (n:ℝ)/(p:ℝ)*divisorDensity L - coprimeCount L (n/p) := by
  rw [arithmeticPacket_eq_all_floors L p n hp, coprimeCount_eq_floor_sum L (n/p) hL]
  simp only [Nat.div_div_eq_div_mul, Nat.mul_comm p]


theorem coprimeCount_self (L : ℕ) :
    coprimeCount L L = (Nat.totient L : ℝ) := by
  let f : ℕ → ℝ := fun k => if Nat.Coprime k L then 1 else 0
  have h₀ := Finset.sum_range_succ f L
  have h₁ := Finset.sum_range_succ' f L
  have he : f L = f 0 := by
    simp [f, Nat.coprime_iff_gcd_eq_one]
  have hshift : (∑ k ∈ Finset.range L, f (k+1)) =
      ∑ k ∈ Finset.range L, f k := by
    linarith
  calc
    coprimeCount L L = ∑ k ∈ Finset.range L, f (k+1) := rfl
    _ = ∑ k ∈ Finset.range L, f k := hshift
    _ = (Nat.totient L : ℝ) := by
      rw [Nat.totient, Finset.card_eq_sum_ones, Finset.sum_filter]
      push_cast
      simp only [f, Nat.coprime_comm]

theorem divisorDensity_eq_totient (L : ℕ) (hL : L ≠ 0) :
    divisorDensity L = (Nat.totient L : ℝ) / (L : ℝ) := by
  have hzero : divisorSieve L L = 0 := by
    unfold divisorSieve
    rw [neg_eq_zero]
    apply Finset.sum_eq_zero
    intro d hd
    simp [residueFraction, Nat.mod_eq_zero_of_dvd (Nat.dvd_of_mem_divisors hd)]
  have h := divisorSieve_eq_count_sub_linear L L hL
  rw [hzero, coprimeCount_self] at h
  have hLR : (L:ℝ) ≠ 0 := by exact_mod_cast hL
  apply (eq_div_iff hLR).2
  nlinarith

theorem arithmeticPacket_eq_totient_count (L p n : ℕ)
    (hL : L ≠ 0) (hp : 0 < p) :
    arithmeticPacket L p n =
      (n:ℝ)*(Nat.totient L:ℝ)/((p:ℝ)*(L:ℝ)) - coprimeCount L (n/p) := by
  rw [arithmeticPacket_eq_count L p n hL hp, divisorDensity_eq_totient L hL]
  ring

theorem arithmeticPacket_short_head (L p n : ℕ)
    (hL : L ≠ 0) (hp : 0 < p) (hn : n < p) :
    arithmeticPacket L p n = (n:ℝ)/(p:ℝ)*divisorDensity L := by
  rw [arithmeticPacket_eq_count L p n hL hp, Nat.div_eq_of_lt hn]
  simp [coprimeCount, cumulative]

theorem arithmeticPacket_period (L p n : ℕ) :
    arithmeticPacket L p (n+p*L) = arithmeticPacket L p n := by
  unfold arithmeticPacket
  apply Finset.sum_congr rfl
  intro d hd
  have hdiv : p*d ∣ p*L := Nat.mul_dvd_mul_left p (Nat.dvd_of_mem_divisors hd)
  simp [residueFraction, Nat.add_mod, Nat.mod_eq_zero_of_dvd hdiv]

theorem arithmeticPacket_six_five_seven :
    arithmeticPacket 6 5 7 = -(8/15:ℝ) := by
  have ht : Nat.totient 6 = 2 := by decide
  have hc : coprimeCount 6 1 = 1 := by
    simp only [coprimeCount, cumulative, Finset.range_one, Finset.sum_singleton]
    norm_num
  rw [arithmeticPacket_eq_totient_count 6 5 7 (by decide) (by decide)]
  norm_num [ht, hc]

end
end RiemannResearch.RH.QMobiusPrimePacket
