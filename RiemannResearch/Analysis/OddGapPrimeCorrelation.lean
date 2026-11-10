/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ShortIntervalBoundary
import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Card
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
/-! # Actual prime-pair correlations at odd gaps

For an odd additive gap, a nonzero von Mangoldt pair must contain a
positive power of two. We retain both exception sums exactly, count their
possible exponents, and prove an unconditional raw correlation bound by
twice the square of a logarithm. The centered estimate retains the actual
one-point Mangoldt discrepancy and its shifted endpoint correction.

Source: the interpretation in terms of centered prime pairs is the
Montgomery--Soundararajan short-interval expansion,
https://arxiv.org/abs/math/0409258, equations (18)--(19).
The parity argument and finite estimates are proved directly from Mathlib's
actual von Mangoldt function and prime-power characterization. No
Hardy--Littlewood estimate or hypothesis about zeta zeros is used.
The corresponding even-gap cancellation remains open.
-/

open scoped BigOperators ArithmeticFunction
open Finset
namespace RiemannResearch.Analysis.OddGapPrimeCorrelation

theorem even_prime_pow (n : ℕ) (hn : IsPrimePow n) (he : 2 ∣ n) :
    ∃ k ≤ Nat.log 2 n, 0 < k ∧ n = 2 ^ k := by
  obtain ⟨k,hk,hpos,hpow⟩ := (isPrimePow_nat_iff_bounded_log_minFac n).mp hn
  have hm : n.minFac = 2 := by exact (Nat.minFac_eq_two_iff n).mpr he
  exact ⟨k,hk,hpos,by simpa [hm] using hpow⟩

theorem odd_gap_support (n h : ℕ) (hh : h % 2 = 1)
    (hp : Λ n * Λ (n + h) ≠ 0) :
    (∃ k ≤ Nat.log 2 n, 0 < k ∧ n = 2 ^ k) ∨
    (∃ k ≤ Nat.log 2 (n + h), 0 < k ∧ n + h = 2 ^ k) := by
  have hp1 := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp (mul_ne_zero_iff.mp hp).1
  have hp2 := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp (mul_ne_zero_iff.mp hp).2
  have he : 2 ∣ n ∨ 2 ∣ n + h := by
    simp only [Nat.dvd_iff_mod_eq_zero]
    omega
  exact he.elim (fun he => Or.inl (even_prime_pow n hp1 he))
    (fun he => Or.inr (even_prime_pow (n + h) hp2 he))


def powersTwo (L : ℕ) : Finset ℕ :=
  (range (Nat.log 2 L)).image (fun k => 2 ^ (k + 1))

theorem mem_powersTwo_of_witness {n L k : ℕ} (hn : n ≤ L)
    (hk : k ≤ Nat.log 2 n) (hk0 : 0 < k) (hpow : n = 2 ^ k) :
    n ∈ powersTwo L := by
  have hkL := hk.trans (Nat.log_mono_right hn)
  unfold powersTwo
  apply mem_image.mpr
  refine ⟨k - 1, mem_range.mpr (by omega), ?_⟩
  have he : k - 1 + 1=k := by omega
  rw [he]
  exact hpow.symm

theorem even_of_mem_powersTwo {n L : ℕ} (hn : n ∈ powersTwo L) : n % 2 = 0 := by
  obtain ⟨k,hk,rfl⟩ := mem_image.mp hn
  simp [pow_succ]

theorem mangoldt_of_mem_powersTwo {n L : ℕ} (hn : n ∈ powersTwo L) :
    Λ n = Real.log 2 := by
  obtain ⟨k,hk,rfl⟩ := mem_image.mp hn
  rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num

theorem odd_gap_support_mem (n h L : ℕ) (hh : h % 2= 1)
    (hnL : n ≤ L) (hmL : n + h ≤ L) (hp : Λ n * Λ (n + h) ≠ 0) :
    n ∈ powersTwo L ∨ n + h ∈ powersTwo L := by
  rcases odd_gap_support n h hh hp with ⟨k,hk,hk0,he⟩ | ⟨k,hk,hk0,he⟩
  · exact Or.inl (mem_powersTwo_of_witness hnL hk hk0 he)
  · exact Or.inr (mem_powersTwo_of_witness hmL hk hk0 he)

theorem odd_gap_product_exact (n h L : ℕ) (hh : h % 2= 1)
    (hnL : n ≤ L) (hmL : n + h ≤ L) :
    Λ n * Λ (n + h) = Real.log 2 *
      ((if n ∈ powersTwo L then Λ (n + h) else 0) +
        (if n + h ∈ powersTwo L then Λ n else 0)) := by
  by_cases h1 : n ∈ powersTwo L
  · have h2 : n + h ∉ powersTwo L := by
      intro h2
      have he1 := even_of_mem_powersTwo h1
      have he2 := even_of_mem_powersTwo h2
      omega
    rw [if_pos h1, if_neg h2, mangoldt_of_mem_powersTwo h1]
    ring
  · by_cases h2 : n + h ∈ powersTwo L
    · rw [if_neg h1, if_pos h2, mangoldt_of_mem_powersTwo h2]
      ring
    · have hz : Λ n * Λ (n + h) = 0 := by
        by_contra hp
        exact (odd_gap_support_mem n h L hh hnL hmL hp).elim h1 h2
      simp only [if_neg h1, if_neg h2, add_zero, mul_zero]
      exact hz

theorem shifted_power_count (N b L : ℕ) :
    ((range N).filter (fun x => x + b ∈ powersTwo L)).card ≤ Nat.log 2 L := by
  calc
    _ ≤ (powersTwo L).card := by
      apply card_le_card_of_injOn (fun x => x + b)
      · intro x hx
        exact (mem_filter.mp hx).2
      · intro x hx y hy he
        exact Nat.add_right_cancel he
    _ ≤ _ := by
      unfold powersTwo
      exact card_image_le.trans_eq (card_range _)

theorem power_sample_sum_le (f : ℕ → ℝ) (N b L : ℕ) {B : ℝ}
    (hB : 0 ≤ B) (hf : ∀ x ∈ range N, f x ≤ B) :
    (∑ x ∈ range N, if x + b ∈ powersTwo L then f x else 0) ≤
      (Nat.log 2 L : ℝ) * B := by
  rw [← sum_filter]
  calc
    _ ≤ ∑ _x ∈ (range N).filter (fun x => x + b ∈ powersTwo L), B := by
      apply sum_le_sum
      intro x hx
      exact hf x (mem_filter.mp hx).1
    _ ≤ _ := by
      simp only [sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast shifted_power_count N b L) hB

open ShortIntervalBoundary

/-- Both possible power-of-two exceptions are retained exactly. -/
theorem odd_raw_exact (N h : ℕ) (hh : h % 2= 1) :
    rawGapCorrelation N h = Real.log 2 *
      ((∑ x ∈ range N,
          if x + 2 ∈ powersTwo (N + h + 2) then Λ (x + 2 + h) else 0) +
        (∑ x ∈ range N,
          if x + 2 + h ∈ powersTwo (N + h + 2) then Λ (x + 2) else 0)) := by
  unfold rawGapCorrelation
  calc
    _ = ∑ x ∈ range N, Real.log 2 *
      ((if x + 2 ∈ powersTwo (N + h + 2) then Λ (x + 2 + h) else 0) +
        (if x + 2 + h ∈ powersTwo (N + h + 2) then Λ (x + 2) else 0)) := by
      apply sum_congr rfl
      intro x hx
      have hxN := mem_range.mp hx
      exact odd_gap_product_exact (x + 2) h (N + h + 2) hh (by omega) (by omega)
    _ = _ := by rw [← mul_sum, sum_add_distrib]

theorem logTwo_mul_natLog_le (L : ℕ) (hL : 0 <  L) :
    (Nat.log 2 L : ℝ) * Real.log 2 ≤ Real.log L := by
  have hp := Nat.pow_log_le_self 2 (by omega : L ≠ 0)
  have hreal : (2: ℝ) ^ (Nat.log 2 L) ≤ (L: ℝ) := by exact_mod_cast hp
  have hl := Real.log_le_log (by positivity : (0: ℝ)<2 ^ (Nat.log 2 L)) hreal
  rwa [Real.log_pow] at hl

theorem rawGapCorrelation_nonneg (N h : ℕ) :
    0 ≤ rawGapCorrelation N h := by
  unfold rawGapCorrelation
  exact sum_nonneg fun x hx => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    ArithmeticFunction.vonMangoldt_nonneg

/-- An unconditional estimate for actual von Mangoldt coefficients at every odd gap. -/
theorem odd_raw_le_log_sq (N h : ℕ) (hh : h % 2 = 1) :
    rawGapCorrelation N h ≤ 2 * (Real.log ((N + h + 2: ℕ): ℝ)) ^ 2 := by
  let L : ℕ := N + h + 2
  have hL : 0 < L := by dsimp [L]; omega
  have hlog : 0 ≤ Real.log (L: ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ L by omega))
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hfirst :
      (∑ x ∈ range N, if x + 2 ∈ powersTwo L then Λ (x + 2 + h) else 0) ≤
        (Nat.log 2 L : ℝ) * Real.log L := by
    apply power_sample_sum_le _ N 2 L hlog
    intro x hx
    apply ArithmeticFunction.vonMangoldt_le_log.trans
    apply Real.log_le_log
    · exact_mod_cast (show 0 < x + 2 + h by omega)
    · exact_mod_cast (show x + 2 + h ≤ L by dsimp [L]; have := mem_range.mp hx; omega)
  have hsecond :
      (∑ x ∈ range N, if x + 2 + h ∈ powersTwo L then Λ (x + 2) else 0) ≤
        (Nat.log 2 L : ℝ) * Real.log L := by
    have hf : ∀ x ∈ range N, Λ (x + 2) ≤ Real.log (L: ℝ) := by
      intro x hx
      apply ArithmeticFunction.vonMangoldt_le_log.trans
      apply Real.log_le_log
      · exact_mod_cast (show 0 < x + 2 by omega)
      · exact_mod_cast (show x + 2 ≤ L by dsimp [L]; have := mem_range.mp hx; omega)
    simpa only [Nat.add_assoc] using
      power_sample_sum_le (fun x => Λ (x + 2)) N (2 + h) L hlog hf
  calc
    _ = Real.log 2 *
      ((∑ x ∈ range N, if x + 2 ∈ powersTwo L then Λ (x + 2 + h) else 0) +
       (∑ x ∈ range N, if x + 2 + h ∈ powersTwo L then Λ (x + 2) else 0)) :=
      odd_raw_exact N h hh
    _ ≤ Real.log 2 * ((Nat.log 2 L : ℝ) * Real.log L +
        (Nat.log 2 L : ℝ) * Real.log L) :=
      mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hlog2
    _ = 2 * ((Nat.log 2 L : ℝ) * Real.log 2) * Real.log L := by ring
    _ ≤ 2 * (Real.log L) ^ 2 := by
      have hm := mul_le_mul_of_nonneg_right (logTwo_mul_natLog_le L hL) hlog
      nlinarith
    _ = _ := rfl

open ShortIntervalVariance

theorem odd_centered_gap_error_bound (N h : ℕ) (hh : h % 2 = 1) :
    |gapCorrelation centeredMangoldt N h + N| ≤
      2 * (Real.log ((N + h + 2: ℕ): ℝ)) ^ 2 +
      2 * |mangoldtMass N - N| + |mangoldtMassBoundary N h| := by
  have he : gapCorrelation centeredMangoldt N h + N =
      rawGapCorrelation N h - 2 * (mangoldtMass N - N) - mangoldtMassBoundary N h := by
    rw [centered_gap_raw_exact]
    ring
  rw [he]
  calc
    _ ≤ |rawGapCorrelation N h - 2 * (mangoldtMass N - N)| +
        |mangoldtMassBoundary N h| := abs_sub _ _
    _ ≤ (|rawGapCorrelation N h| + |2 * (mangoldtMass N - N)|) +
        |mangoldtMassBoundary N h| := by
      exact add_le_add (abs_sub (rawGapCorrelation N h) (2 * (mangoldtMass N - N))) le_rfl
    _ = rawGapCorrelation N h + 2 * |mangoldtMass N - N| +
        |mangoldtMassBoundary N h| := by
      rw [abs_of_nonneg (rawGapCorrelation_nonneg N h), abs_mul]
      norm_num
    _ ≤ _ := by linarith [odd_raw_le_log_sq N h hh]


theorem odd_centered_gap_bound (N h : ℕ) (hh : h % 2 = 1) :
    |gapCorrelation centeredMangoldt N h + N| ≤
      2 * (Real.log ((N + h + 2: ℕ): ℝ)) ^ 2 +
      2 * |mangoldtMass N - N| + (h: ℝ) * Real.log ((N + h + 2: ℕ): ℝ) := by
  have hb : |mangoldtMassBoundary N h| ≤
      (h: ℝ) * Real.log ((N + h + 2: ℕ): ℝ) := by
    unfold mangoldtMassBoundary
    calc
      _ ≤ ∑ x ∈ range h, |Λ (N + x + 2) - Λ (x + 2)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x ∈ range h, Real.log ((N + h + 2: ℕ): ℝ) := by
        apply sum_le_sum
        intro x hx
        have hx' := mem_range.mp hx
        have hfirst : Λ (N + x + 2) ≤ Real.log ((N + h + 2: ℕ): ℝ) := by
          apply ArithmeticFunction.vonMangoldt_le_log.trans
          apply Real.log_le_log
          · exact_mod_cast (show 0 < N + x + 2 by omega)
          · exact_mod_cast (show N + x + 2 ≤ N + h + 2 by omega)
        have hsecond : Λ (x + 2) ≤ Real.log ((N + h + 2: ℕ): ℝ) := by
          apply ArithmeticFunction.vonMangoldt_le_log.trans
          apply Real.log_le_log
          · exact_mod_cast (show 0 < x + 2 by omega)
          · exact_mod_cast (show x + 2 ≤ N + h + 2 by omega)
        have hn1 := ArithmeticFunction.vonMangoldt_nonneg (n := N + x + 2)
        have hn2 := ArithmeticFunction.vonMangoldt_nonneg (n := x + 2)
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      _ = _ := by simp
  exact (odd_centered_gap_error_bound N h hh).trans (by linarith)

end RiemannResearch.Analysis.OddGapPrimeCorrelation
