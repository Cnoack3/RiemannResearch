/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.CanonicalMobiusConditionalHead
import RiemannResearch.NumberTheory.MobiusReciprocalSum
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import RiemannResearch.RH.QMobiusExactHead
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Prime-balanced Mobius exact heads

Source: the user-provided exact-head averaging agenda, 24 October 2026.
The arithmetic construction replaces the canonical terminal conductor N+1
by an arbitrary prime q>N. Its squarefree legality, exact physical head,
and integer amplitude bound are unconditional. No uniform complete-energy
bound is asserted.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.QPrimeBalancedExactHead
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative

/-- A rational finite arithmetic synthesis, with an independently chosen anchor. -/
def primeHead (N q : ℕ) : QHilbert :=
  -(∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) • qResidue d) +
    ((q : ℝ) * Pareto.mobiusReciprocalSum N) • qResidue q

theorem primeHead_sequence (N q n : ℕ) :
    qSequence (primeHead N q) n =
      -(∑ d ∈ Finset.Icc 1 N,
          (ArithmeticFunction.moebius d : ℝ) * residueFraction d n) +
        (q : ℝ) * Pareto.mobiusReciprocalSum N * residueFraction q n := by
  change qSequenceLinear (primeHead N q) n = _
  unfold primeHead
  simp only [map_add, map_neg, map_sum, map_smul]
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  change -(∑ d ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius d : ℝ) * qSequence (qResidue d) n) +
    ((q : ℝ) * Pareto.mobiusReciprocalSum N) * qSequence (qResidue q) n = _
  simp_rw [qSequence_qResidue]

/-- The exact head is independent of the size of the prime anchor. -/
theorem primeHead_exact (N q n : ℕ) (hNq : N < q)
    (hn : 0 < n) (hnN : n ≤ N) :
    qSequence (primeHead N q) n = 1 := by
  rw [primeHead_sequence, Pareto.mobius_residue_prefix_identity N n hn hnN]
  unfold residueFraction
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt hnN hNq)]
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  field_simp
  ring

theorem primeHead_canonical (N : ℕ) :
    primeHead N (N+1) = QMobiusExactHead.exactHead N := rfl

/-- Composite nonsquarefree conductors have zero Mobius coefficient. -/
theorem primeHead_mem_squarefreeSpan (N q : ℕ) (hq : Nat.Prime q) :
    primeHead N q ∈ qSquarefreeCRTSpan := by
  have hres (d : ℕ) (hd : 0 < d) (hs : Squarefree d) :
      qResidue d ∈ qSquarefreeCRTSpan := by
    by_cases h1 : d = 1
    · rw [h1, qResidue_one]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨⟨d, by omega, hs⟩, rfl⟩
  unfold primeHead
  apply Submodule.add_mem
  · apply Submodule.neg_mem
    apply Submodule.sum_mem
    intro d hd
    by_cases hs : Squarefree d
    · exact Submodule.smul_mem _ _ (hres d (Finset.mem_Icc.mp hd).1 hs)
    · have hm : ArithmeticFunction.moebius d = 0 :=
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs
      simp only [hm, Int.cast_zero, zero_smul]
      exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (hres q hq.pos hq.squarefree)

/-- The direct coefficient amplitude retains the actual reciprocal sum. -/
theorem primeHead_residual_coefficient_bound (N q n : ℕ) (hq : 0 < q) :
    |qSequence (primeHead N q) n - 1| ≤
      1 + (∑ d ∈ Finset.Icc 1 N, |(ArithmeticFunction.moebius d : ℝ)|) +
        |(q : ℝ) * Pareto.mobiusReciprocalSum N| := by
  have hsum :
      |∑ d ∈ Finset.Icc 1 N,
          (ArithmeticFunction.moebius d : ℝ) * residueFraction d n| ≤
        ∑ d ∈ Finset.Icc 1 N, |(ArithmeticFunction.moebius d : ℝ)| := by
    calc
      _ ≤ ∑ d ∈ Finset.Icc 1 N,
          |(ArithmeticFunction.moebius d : ℝ) * residueFraction d n| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro d hd
        rw [abs_mul]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (Pareto.residueFraction_abs_le_one d n (Finset.mem_Icc.mp hd).1)
          (abs_nonneg (ArithmeticFunction.moebius d : ℝ))
  have ha : |(q : ℝ) * Pareto.mobiusReciprocalSum N * residueFraction q n| ≤
      |(q : ℝ) * Pareto.mobiusReciprocalSum N| := by
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Pareto.residueFraction_abs_le_one q n hq)
      (abs_nonneg ((q : ℝ) * Pareto.mobiusReciprocalSum N))
  rw [primeHead_sequence]
  have ht := abs_add_le
    (-(∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) * residueFraction d n) +
      (q : ℝ) * Pareto.mobiusReciprocalSum N * residueFraction q n) (-1 : ℝ)
  have hs := abs_add_le
    (-(∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) * residueFraction d n))
    ((q : ℝ) * Pareto.mobiusReciprocalSum N * residueFraction q n)
  simp only [← sub_eq_add_neg, abs_neg, abs_one] at ht hs
  linarith

/-- N+q is an explicit nonnegative integer amplitude certificate. -/
theorem primeHead_residual_abs_le (N q n : ℕ) (hN : 0 < N) (hq : 0 < q) :
    |qSequence (primeHead N q) n - 1| ≤ ((N + q : ℕ) : ℝ) := by
  have hsum := Pareto.finite_mobius_sum_abs N hN
    (fun d => residueFraction d n) 1
    (by simp [residueFraction, Nat.mod_one])
    (fun d hd => Pareto.residueFraction_abs_le_one d n (Finset.mem_Icc.mp hd).1)
  have hm := Pareto.mobiusReciprocalSum_abs_le_one N hN
  have hg := Pareto.residueFraction_abs_le_one q n hq
  have ha : |(q : ℝ) * Pareto.mobiusReciprocalSum N * residueFraction q n| ≤
      (q : ℝ) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    have hh := mul_le_mul hm hg (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have hhq := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
    nlinarith
  rw [primeHead_sequence]
  have ht := abs_add_le
    (-(∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) * residueFraction d n) +
      (q : ℝ) * Pareto.mobiusReciprocalSum N * residueFraction q n) (-1 : ℝ)
  have hs := abs_add_le
    (-(∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) * residueFraction d n))
    ((q : ℝ) * Pareto.mobiusReciprocalSum N * residueFraction q n)
  simp only [← sub_eq_add_neg, abs_neg, abs_one, mul_one] at ht hs hsum
  push_cast
  linarith

/-- The first prime strictly beyond the requested head, found by integer search. -/
def anchorPrime (N : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes (N+1))

theorem anchorPrime_spec (N : ℕ) : N < anchorPrime N ∧ Nat.Prime (anchorPrime N) := by
  have h := Nat.find_spec (Nat.exists_infinite_primes (N+1))
  exact ⟨by change N < Nat.find (Nat.exists_infinite_primes (N+1)); omega, h.2⟩

/-- The specified squarefree family used by the rational experiments. -/
def nextPrimeHead (N : ℕ) : QHilbert := primeHead N (anchorPrime N)

theorem nextPrimeHead_exact (N n : ℕ) (hn : 0 < n) (hnN : n ≤ N) :
    qSequence (nextPrimeHead N) n = 1 :=
  primeHead_exact N (anchorPrime N) n (anchorPrime_spec N).1 hn hnN

theorem nextPrimeHead_mem_squarefreeSpan (N : ℕ) :
    nextPrimeHead N ∈ qSquarefreeCRTSpan :=
  primeHead_mem_squarefreeSpan N (anchorPrime N) (anchorPrime_spec N).2

theorem nextPrimeHead_amplitude (N n : ℕ) (hN : 0 < N) :
    |qSequence (nextPrimeHead N) n - 1| ≤ ((N + anchorPrime N : ℕ) : ℝ) :=
  primeHead_residual_abs_le N (anchorPrime N) n hN (anchorPrime_spec N).2.pos

end RiemannResearch.RH.QPrimeBalancedExactHead
