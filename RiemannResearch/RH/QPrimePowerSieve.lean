/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.PeriodicDivisorJumps
import RiemannResearch.RH.QSquarefreeLatticePackets
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Actual gcd-class sieve vectors and their complete-Q head obstruction

Source: the 20 October 2026 RH/CRT research continuation. This module defines
the finite residue synthesis itself, proves its exact count-minus-slope
sequence, and bounds its full Q norm from below by a finite physical head.
The arithmetic count bound is supplied concretely by prime-factor uniqueness.
No norm boundedness, closure characterization, or RH assertion is assumed.

-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QPrimePowerSieve
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative
open PeriodicDivisorJumps QSquarefreeLatticePackets
open RiemannResearch.NumberTheory.DivisorIncidence

/-- The exact finite divisor-inversion coefficients of one gcd class. -/
def sieveCoefficient (L p d : ℕ) : ℝ :=
  divisorCoefficients L (fun e => if e = p then 1 else 0) d

/-- The complete linear slope produced by finite incidence inversion. -/
def sieveSlope (L p : ℕ) : ℝ :=
  ∑ d ∈ L.divisors, sieveCoefficient L p d / (d : ℝ)

/-- Positive visits to the selected gcd class, as a real-valued count. -/
def sieveCount (L p n : ℕ) : ℝ :=
  cumulative (fun k => if Nat.gcd k L = p then 1 else 0) n

/-- The actual finite residue synthesis; every composite divisor is retained. -/
def sieveVector (L p : ℕ) : QHilbert :=
  -(∑ d ∈ L.divisors, sieveCoefficient L p d • qResidue d)

theorem sieveCoefficient_eq (L p d : ℕ) (hp : p ∈ L.divisors) :
    sieveCoefficient L p d =
      if p ∣ d then (ArithmeticFunction.moebius (d / p) : ℝ) else 0 := by
  classical
  simp [sieveCoefficient, divisorCoefficients, mul_ite, hp]

theorem sieveVector_mem_divisorStage (L p : ℕ) :
    sieveVector L p ∈ divisorStage L := by
  apply (divisorStage L).neg_mem
  apply (divisorStage L).sum_mem
  intro d hd
  exact (divisorStage L).smul_mem _
    (Submodule.subset_span ⟨d, Nat.dvd_of_mem_divisors hd, rfl⟩)

theorem sieveVector_mem_squarefreeSpan (L p : ℕ) (hL : 0 < L)
    (hsf : Squarefree L) : sieveVector L p ∈ qSquarefreeCRTSpan :=
  divisorStage_le_squarefreeSpan L hL hsf (sieveVector_mem_divisorStage L p)

@[simp] theorem sieveCount_zero (L p : ℕ) : sieveCount L p 0 = 0 := by
  simp [sieveCount]

theorem sieveCount_eq_card (L p n : ℕ) :
    sieveCount L p n =
      (((Finset.Icc 1 n).filter (fun k => Nat.gcd k L = p)).card : ℝ) := by
  rw [sieveCount, cumulative, ← sum_Icc_one n
    (fun k => if Nat.gcd k L = p then (1 : ℝ) else 0)]
  exact Finset.sum_boole _ _

theorem sieveCount_nonneg (L p n : ℕ) : 0 ≤ sieveCount L p n := by
  rw [sieveCount_eq_card]
  positivity

theorem sieveCount_integrated (L p n : ℕ) (hL : 0 < L) :
    sieveCount L p n = (n : ℝ) * sieveSlope L p -
      ∑ d ∈ L.divisors, sieveCoefficient L p d * residueFraction d n := by
  have hj (k : ℕ) : sieveCount L p (k + 1) - sieveCount L p k =
      ∑ d ∈ L.divisors, sieveCoefficient L p d * divisorIndicator d (k + 1) := by
    simp only [sieveCount, cumulative_succ, add_sub_cancel_left]
    exact gcd_function_eq_divisor_sum L hL (fun e => if e = p then 1 else 0) (k + 1)
  simpa only [sieveCount_zero, zero_add, sieveSlope] using
    integrate_divisor_jumps L (sieveCoefficient L p) (sieveCount L p) hj n

theorem qSequence_sieveVector (L p n : ℕ) (hL : 0 < L) :
    qSequence (sieveVector L p) n = sieveCount L p n - sieveSlope L p * (n : ℝ) := by
  have hs : qSequence (sieveVector L p) n =
      -(∑ d ∈ L.divisors, sieveCoefficient L p d * residueFraction d n) := by
    change qSequenceLinear (-(∑ d ∈ L.divisors,
      sieveCoefficient L p d • qResidue d)) n = _
    simp only [map_neg, map_sum, map_smul, Pi.neg_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    change -(∑ d ∈ L.divisors, sieveCoefficient L p d * qSequence (qResidue d) n) = _
    simp only [qSequence_qResidue]
  rw [hs, sieveCount_integrated L p n hL]
  ring

/-- The slope is the exact density of the selected class in one complete period. -/
theorem sieveSlope_eq_period_count (L p : ℕ) (hL : 0 < L) :
    sieveSlope L p = sieveCount L p L / (L : ℝ) := by
  have hz : (∑ d ∈ L.divisors, sieveCoefficient L p d * residueFraction d L) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    simp [residueFraction, Nat.mod_eq_zero_of_dvd (Nat.dvd_of_mem_divisors hd)]
  have he := sieveCount_integrated L p L hL
  rw [hz, sub_zero] at he
  apply (eq_div_iff (by positivity : (L : ℝ) ≠ 0)).mpr
  nlinarith [he]

/-- The finite slope has its exact classical totient formula. -/
theorem sieveSlope_eq_totient (L p : ℕ) (hL : 0 < L) (hp : p ∈ L.divisors) :
    sieveSlope L p = (Nat.totient (L / p) : ℝ) / (L : ℝ) := by
  rw [sieveSlope_eq_period_count L p hL, sieveCount_eq_card]
  change ((gcdClass L p).card : ℝ) / (L : ℝ) = _
  rw [gcd_class_card L p hp]

/-- A selected gcd-class member below a fully sieved cutoff is a power of p. -/
theorem eq_prime_power_of_gcd_eq (L p H n : ℕ) (hp : p.Prime)
    (hcover : ∀ q : ℕ, q.Prime → q ≤ H → q ∣ L)
    (hn : 0 < n) (hnH : n ≤ H) (hg : Nat.gcd n L = p) :
    ∃ k : ℕ, 0 < k ∧ n = p ^ k := by
  have hpn : p ∣ n := by rw [← hg]; exact Nat.gcd_dvd_left n L
  have huniq (q : ℕ) (hq : q.Prime) (hqn : q ∣ n) : q = p := by
    have hqH : q ≤ H := (Nat.le_of_dvd hn hqn).trans hnH
    have hqg : q ∣ Nat.gcd n L := Nat.dvd_gcd hqn (hcover q hq hqH)
    rw [hg] at hqg
    exact (Nat.prime_dvd_prime_iff_eq hq hp).mp hqg
  have hpow : IsPrimePow n := isPrimePow_iff_unique_prime_dvd.mpr
    ⟨p, ⟨hp, hpn⟩, fun q hq => huniq q hq.1 hq.2⟩
  obtain ⟨q, k, hq, hk, he⟩ := (isPrimePow_nat_iff n).mp hpow
  have hqn : q ∣ n := by rw [← he]; exact dvd_pow_self q (ne_of_gt hk)
  have hqp := huniq q hq hqn
  subst q
  exact ⟨k, hk, he.symm⟩

/-- The exact arithmetic count is bounded by the number of possible p-powers. -/
theorem sieveCount_le_log (L p H n : ℕ) (hp : p.Prime)
    (hcover : ∀ q : ℕ, q.Prime → q ≤ H → q ∣ L) (hnH : n ≤ H) :
    sieveCount L p n ≤ (Nat.log p H : ℝ) := by
  classical
  let S := (Finset.Icc 1 n).filter (fun k => Nat.gcd k L = p)
  have hpower (m : ℕ) (hm : m ∈ S) :
      0 < Nat.log p m ∧ p ^ (Nat.log p m) = m := by
    obtain ⟨hmI, hmg⟩ := Finset.mem_filter.mp hm
    obtain ⟨hm1, hmn⟩ := Finset.mem_Icc.mp hmI
    obtain ⟨k, hk, he⟩ := eq_prime_power_of_gcd_eq L p H m hp hcover
      (by omega) (hmn.trans hnH) hmg
    rw [he, Nat.log_pow hp.one_lt]
    exact ⟨hk, rfl⟩
  have hc : S.card ≤ (Finset.Icc 1 (Nat.log p H)).card := by
    apply Finset.card_le_card_of_injOn (Nat.log p)
    · intro m hm
      have hmn := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).2
      exact Finset.mem_Icc.mpr
        ⟨(hpower m hm).1, Nat.log_monotone (hmn.trans hnH)⟩
    · intro m hm k hk he
      rw [← (hpower m hm).2, ← (hpower k hk).2, he]
  rw [sieveCount_eq_card]
  exact_mod_cast (show S.card ≤ Nat.log p H by simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hc)

/-- A squarefree period sees every positive power of a divisor prime in its class. -/
theorem gcd_prime_power_eq (L p k : ℕ) (hsf : Squarefree L)
    (hpL : p ∣ L) (hk : 0 < k) : Nat.gcd (p ^ k) L = p := by
  apply Nat.dvd_antisymm
  · have hs : Squarefree (Nat.gcd (p ^ k) L) :=
      hsf.squarefree_of_dvd (Nat.gcd_dvd_right (p ^ k) L)
    exact (hs.dvd_pow_iff_dvd (ne_of_gt hk)).mp (Nat.gcd_dvd_left (p ^ k) L)
  · exact Nat.dvd_gcd (dvd_pow_self p (ne_of_gt hk)) hpL

/-- Exact finite head stabilization to the prime-power counting target. -/
theorem sieveCount_eq_log (L p H n : ℕ) (hp : p.Prime) (hsf : Squarefree L)
    (hpL : p ∣ L) (hcover : ∀ q : ℕ, q.Prime → q ≤ H → q ∣ L) (hnH : n ≤ H) :
    sieveCount L p n = (Nat.log p n : ℝ) := by
  classical
  by_cases hn : n = 0
  · subst n
    simp
  apply le_antisymm
  · exact sieveCount_le_log L p n n hp (fun q hq hqn =>
      hcover q hq (hqn.trans hnH)) le_rfl
  · let S := (Finset.Icc 1 n).filter (fun k => Nat.gcd k L = p)
    have hc : (Finset.Icc 1 (Nat.log p n)).card ≤ S.card := by
      apply Finset.card_le_card_of_injOn (fun k : ℕ => p ^ k)
      · intro k hk
        obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_Icc.mpr ⟨Nat.succ_le_iff.mpr (pow_pos hp.pos k),
          (Nat.le_log_iff_pow_le hp.one_lt hn).mp hkn⟩,
          gcd_prime_power_eq L p k hsf hpL (by omega)⟩
      · intro k hk j hj he
        have hh := congrArg (Nat.log p) he
        simpa only [Nat.log_pow hp.one_lt] using hh
    rw [sieveCount_eq_card]
    exact_mod_cast (show Nat.log p n ≤ S.card by
      simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hc)

/-- The exact vector head retains its density correction; no tail is discarded. -/
theorem qSequence_sieveVector_head (L p H n : ℕ) (hL : 0 < L)
    (hp : p.Prime) (hsf : Squarefree L) (hpL : p ∣ L)
    (hcover : ∀ q : ℕ, q.Prime → q ≤ H → q ∣ L) (hnH : n ≤ H) :
    qSequence (sieveVector L p) n = (Nat.log p n : ℝ) - sieveSlope L p * (n : ℝ) := by
  rw [qSequence_sieveVector L p n hL, sieveCount_eq_log L p H n hp hsf hpL hcover hnH]

/-- An actual complete Q norm dominates its finite physical head. -/
theorem finite_head_le_norm_sq (x : QHilbert) (H : ℕ) :
    (∑ n ∈ Finset.Icc 1 H, positiveQWeight n * (qSequence x n) ^ 2) ≤ ‖x‖ ^ 2 := by
  rw [qNorm_weighted_sq]
  exact Summable.sum_le_tsum _
    (fun n _ => mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg _))
    (qSequence_square_summable x)

/-- A bounded count-minus-slope head forces complete norm growth. -/
theorem head_norm_lower (x : QHilbert) (f : ℕ → ℝ) (a B : ℝ) (H : ℕ)
    (hB : 0 ≤ B)
    (hf : ∀ n ∈ Finset.Icc 1 H, 0 ≤ f n ∧ f n ≤ B)
    (he : ∀ n ∈ Finset.Icc 1 H, qSequence x n = f n - a * (n : ℝ)) :
    a ^ 2 * (H : ℝ) / (2 * zetaTwo) - B ^ 2 ≤ ‖x‖ ^ 2 := by
  have hweight : (∑ n ∈ Finset.Icc 1 H, positiveQWeight n) ≤ 1 := by
    rw [← positiveQWeight_tsum]
    exact Summable.sum_le_tsum _ (fun n _ => positiveQWeight_nonneg n)
      positiveQWeight_summable
  have hpoint (n : ℕ) (hn : n ∈ Finset.Icc 1 H) :
      a ^ 2 / (2 * zetaTwo) - positiveQWeight n * B ^ 2 ≤
        positiveQWeight n * (qSequence x n) ^ 2 := by
    have hnpos : 0 < n := by have := (Finset.mem_Icc.mp hn).1; omega
    have hnc : (n : ℝ) ≠ 0 := by positivity
    have hcancel : positiveQWeight n * (a * (n : ℝ)) ^ 2 / 2 =
        a ^ 2 / (2 * zetaTwo) := by
      unfold positiveQWeight
      field_simp [hnc, ne_of_gt zetaTwo_pos]
      <;> ring
    have hf2 : (f n) ^ 2 ≤ B ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr (hf n hn).2)
        (add_nonneg hB (hf n hn).1)]
    have hsq : (a * (n : ℝ)) ^ 2 / 2 - B ^ 2 ≤
        (f n - a * (n : ℝ)) ^ 2 := by
      nlinarith [sq_nonneg (a * (n : ℝ) - 2 * f n)]
    have hw := mul_le_mul_of_nonneg_left hsq (positiveQWeight_nonneg n)
    rw [he n hn]
    nlinarith [hcancel]
  have hs := Finset.sum_le_sum hpoint
  have hsum : (∑ n ∈ Finset.Icc 1 H,
      (a ^ 2 / (2 * zetaTwo) - positiveQWeight n * B ^ 2)) =
      a ^ 2 * (H : ℝ) / (2 * zetaTwo) -
        (∑ n ∈ Finset.Icc 1 H, positiveQWeight n) * B ^ 2 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_mul]
    simp only [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    ring
  rw [hsum] at hs
  have hmass := mul_le_mul_of_nonneg_right hweight (sq_nonneg B)
  have hnorm := finite_head_le_norm_sq x H
  nlinarith

/-- Concrete full-Q lower bound for the actual gcd-class sieve vector. -/
theorem sieveVector_norm_lower (L p H : ℕ) (hL : 0 < L) (hp : p.Prime)
    (hcover : ∀ q : ℕ, q.Prime → q ≤ H → q ∣ L) :
    sieveSlope L p ^ 2 * (H : ℝ) / (2 * zetaTwo) - (Nat.log p H : ℝ) ^ 2 ≤
      ‖sieveVector L p‖ ^ 2 := by
  apply head_norm_lower (sieveVector L p) (sieveCount L p) (sieveSlope L p)
    (Nat.log p H : ℝ) H (by positivity)
  · intro n hn
    exact ⟨sieveCount_nonneg L p n,
      sieveCount_le_log L p H n hp hcover (Finset.mem_Icc.mp hn).2⟩
  · intro n _
    exact qSequence_sieveVector L p n hL

end RiemannResearch.RH.QPrimePowerSieve
