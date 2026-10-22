/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Exact jumps of factorial valuation blocks

Source: user-provided Möbius-recovery argument and the continuation agenda
of 21 October 2026. These identities supply the exact legality test for
finite compensated factorial constructions. They make no closure or RH claim.

-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.NumberTheory.PrimeFactorialBlockJumps

/-- The actual factorial valuation block, with integer-valued subtraction. -/
def factorialBlock (p d n : ℕ) : ℤ := ((n / d).factorial.factorization p : ℤ)

/-- The floor quotient increases exactly at the multiples of its denominator.
The result holds for any coordinate of the factorization, without primality. -/
theorem factorialBlock_succ_sub (p d n : ℕ) :
    factorialBlock p d (n + 1) - factorialBlock p d n =
      if d ∣ n + 1 then (((n + 1) / d).factorization p : ℤ) else 0 := by
  classical
  by_cases h : d ∣ n + 1
  · rw [if_pos h]
    simp only [factorialBlock, Nat.succ_div_of_dvd h, Nat.factorial_succ,
      Nat.factorization_mul (Nat.succ_ne_zero _) (Nat.factorial_ne_zero _),
      Finsupp.add_apply, Nat.cast_add]
    ring
  · simp [factorialBlock, if_neg h, Nat.succ_div_of_not_dvd h]

/-- The positive-coordinate predecessor form used by squarefree jump witnesses. -/
theorem factorialBlock_sub_pred (p d n : ℕ) (hn : 0 < n) :
    factorialBlock p d n - factorialBlock p d (n - 1) =
      if d ∣ n then ((n / d).factorization p : ℤ) else 0 := by
  simpa only [Nat.sub_add_cancel hn] using factorialBlock_succ_sub p d (n - 1)

/-- Complete signed jump of a finite linearly compensated factorial family.
The compensation contributes the same constant at every positive jump site. -/
theorem compensated_sum_succ_sub (p : ℕ) (s : Finset ℕ) (c : ℕ → ℝ)
    (β : ℝ) (n : ℕ) :
    ((∑ d ∈ s, c d * (factorialBlock p d (n + 1) : ℝ)) - β * (n + 1 : ℕ)) -
      ((∑ d ∈ s, c d * (factorialBlock p d n : ℝ)) - β * (n : ℝ)) =
    (∑ d ∈ s, c d *
      (if d ∣ n + 1 then (((n + 1) / d).factorization p : ℝ) else 0)) - β := by
  classical
  have hsum :
      (∑ d ∈ s, c d * (factorialBlock p d (n + 1) : ℝ)) -
        (∑ d ∈ s, c d * (factorialBlock p d n : ℝ)) =
      ∑ d ∈ s, c d *
        (if d ∣ n + 1 then (((n + 1) / d).factorization p : ℝ) else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [← mul_sub, ← Int.cast_sub, factorialBlock_succ_sub]
    split_ifs <;> simp
  simp only [Nat.cast_add, Nat.cast_one]
  linear_combination hsum

/-- Exact prime pairing: the factorial difference collapses to a floor. -/
theorem factorialBlock_prime_pair (p n : ℕ) (hp : p.Prime) :
    factorialBlock p 1 n - factorialBlock p p n = ((n / p : ℕ) : ℤ) := by
  induction n with
  | zero => simp [factorialBlock]
  | succ n ih =>
    have h1 := factorialBlock_succ_sub p 1 n
    have hpair := factorialBlock_succ_sub p p n
    simp only [one_dvd, if_true, Nat.div_one] at h1
    by_cases hdiv : p ∣ n + 1
    · have hq : 0 < (n + 1) / p :=
        Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos _) hdiv) hp.pos
      have hmul : p * ((n + 1) / p) = n + 1 := Nat.mul_div_cancel' hdiv
      have hval : (n + 1).factorization p = 1 + ((n + 1) / p).factorization p := by
        calc
          (n + 1).factorization p = (p * ((n + 1) / p)).factorization p :=
            congrArg (fun m : ℕ => m.factorization p) hmul.symm
          _ = 1 + ((n + 1) / p).factorization p := by
            rw [Nat.factorization_mul hp.ne_zero (Nat.ne_of_gt hq),
              Finsupp.add_apply, hp.factorization_self]
      have hv : ((n + 1).factorization p : ℤ) =
          1 + (((n + 1) / p).factorization p : ℤ) := by exact_mod_cast hval
      rw [if_pos hdiv] at hpair
      rw [Nat.succ_div_of_dvd hdiv, Nat.cast_add, Nat.cast_one]
      linear_combination h1 - hpair + ih + hv
    · have hval : (n + 1).factorization p = 0 :=
        Nat.factorization_eq_zero_of_not_dvd hdiv
      rw [hval, Nat.cast_zero] at h1
      rw [if_neg hdiv] at hpair
      rw [Nat.succ_div_of_not_dvd hdiv]
      linear_combination h1 - hpair + ih

/-- The arbitrary outer floor cutoff is retained exactly. -/
theorem factorialBlock_pair (p d n : ℕ) (hp : p.Prime) :
    factorialBlock p d n - factorialBlock p (p * d) n =
      ((n / (p * d) : ℕ) : ℤ) := by
  simpa only [factorialBlock, Nat.div_one, Nat.div_div_eq_div_mul,
    Nat.mul_comm d p] using factorialBlock_prime_pair p (n / d) hp

end RiemannResearch.NumberTheory.PrimeFactorialBlockJumps
