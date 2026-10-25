/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimeBalancedExactHead
import RiemannResearch.NumberTheory.FiniteFloorTail
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Signed floor tails of prime-balanced exact heads

Source: the attached `RH_Kappa_Capacity_and_Energy_Certificates_Chat_2026-10-24(1).md`,
Appendix A, attempt 4. These identities retain the anchor correction and the
full signed arithmetic tail. No asymptotic energy estimate is asserted.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.QPrimeBalancedExactHead
open ZetaTwoHilbert ArithmeticCumulative

/-- Cancellation of the linear terms gives an exact floor formula at every n. -/
theorem primeHead_floor_identity (N q n : ℕ) (hq : 0 < q) :
    qSequence (primeHead N q) n =
      (∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) * ((n / d : ℕ) : ℝ)) -
      (q : ℝ) * Pareto.mobiusReciprocalSum N * ((n / q : ℕ) : ℝ) := by
  have hs : (∑ d ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius d : ℝ) * residueFraction d n) =
      (n : ℝ) * Pareto.mobiusReciprocalSum N -
      ∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) * ((n / d : ℕ) : ℝ) := by
    calc
      _ = ∑ d ∈ Finset.Icc 1 N,
          ((n : ℝ) * ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) -
            (ArithmeticFunction.moebius d : ℝ) * ((n / d : ℕ) : ℝ)) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [Pareto.residueFraction_eq_div_sub_floor d n (Finset.mem_Icc.mp hd).1]
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        rfl
  rw [primeHead_sequence, hs, Pareto.residueFraction_eq_div_sub_floor q n hq]
  have hqR : (q : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- The entire signed tail, including its anchor correction. -/
theorem primeHead_residual_floor_tail (N q n : ℕ)
    (hq : 0 < q) (hn : 0 < n) (hNn : N ≤ n) :
    qSequence (primeHead N q) n - 1 =
      -(∑ d ∈ Finset.Ioc N n,
        (ArithmeticFunction.moebius d : ℝ) * ((n / d : ℕ) : ℝ)) -
      (q : ℝ) * Pareto.mobiusReciprocalSum N * ((n / q : ℕ) : ℝ) := by
  have ht := Pareto.finite_mobius_floor_sum n n hn le_rfl
  rw [RiemannResearch.NumberTheory.positive_prefix_split_at _ N n hNn] at ht
  have hi : Finset.Icc (N+1) n = Finset.Ioc N n := by ext d; simp
  rw [hi] at ht
  rw [primeHead_floor_identity N q n hq]
  linarith

/-- Before the anchor and the second quotient level, the tail is a Mertens increment. -/
theorem primeHead_residual_first_window (N q n : ℕ)
    (hNn : N < n) (hnq : n < q) (hn2 : n < 2 * (N + 1)) :
    qSequence (primeHead N q) n - 1 =
      -(∑ d ∈ Finset.Ioc N n, (ArithmeticFunction.moebius d : ℝ)) := by
  rw [primeHead_residual_floor_tail N q n (by omega) (by omega) hNn.le,
    Nat.div_eq_of_lt hnq]
  simp only [Nat.cast_zero, mul_zero, sub_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  have hNd : N < d := (Finset.mem_Ioc.mp hd).1
  have hdn : d ≤ n := (Finset.mem_Ioc.mp hd).2
  have hd0 : 0 < d := by omega
  have hdlt : n / d < 2 := (Nat.div_lt_iff_lt_mul hd0).mpr (by omega)
  have hdle : 1 ≤ n / d := (Nat.le_div_iff_mul_le hd0).mpr (by simpa using hdn)
  have he : n / d = 1 := by omega
  simp [he]

theorem primeHead_residual_first_window_prefix (N q n : ℕ)
    (hNn : N < n) (hnq : n < q) (hn2 : n < 2 * (N + 1)) :
    qSequence (primeHead N q) n - 1 =
      (∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ)) -
      ∑ d ∈ Finset.Icc 1 n, (ArithmeticFunction.moebius d : ℝ) := by
  rw [primeHead_residual_first_window N q n hNn hnq hn2,
    RiemannResearch.NumberTheory.positive_prefix_split_at _ N n hNn.le]
  have hi : Finset.Icc (N+1) n = Finset.Ioc N n := by ext d; simp
  rw [hi]
  ring

/-- The complete signed residual in quotient-level Möbius increments. -/
theorem primeHead_residual_quotient_tail (N q n : ℕ)
    (hq : 0 < q) (hn : 0 < n) (hNn : N ≤ n) :
    qSequence (primeHead N q) n - 1 =
      -(∑ j ∈ Finset.Icc 1 (n / (N + 1)),
        ∑ d ∈ Finset.Ioc N (n / j), (ArithmeticFunction.moebius d : ℝ)) -
      (q : ℝ) * Pareto.mobiusReciprocalSum N * ((n / q : ℕ) : ℝ) := by
  rw [primeHead_residual_floor_tail N q n hq hn hNn]
  have hi (m : ℕ) : Finset.Icc (N+1) m = Finset.Ioc N m := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have h := RiemannResearch.NumberTheory.finite_floor_tail_swap
    (fun d => (ArithmeticFunction.moebius d : ℝ)) N n
  simp only [hi] at h
  rw [h]

end RiemannResearch.RH.QPrimeBalancedExactHead
