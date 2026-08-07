/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.GCD.Basic

/-!
# Common divisors of orbit-partition degrees

If several finite group actions are restricted to the same subgroup, the
cardinalities of the subgroup orbits partition the cardinality of each
original finite set.  Consequently, a number dividing every orbit degree
divides every total cardinality.  This module isolates that elementary step
without committing to a particular group-action API.
-/

open scoped BigOperators

namespace RiemannResearch.GroupTheory

private theorem dvd_sum_univ
    {ι : Type*} [Fintype ι] (d : ι → ℕ) {c : ℕ}
    (h : ∀ i, c ∣ d i) :
    c ∣ ∑ i, d i := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact Nat.dvd_add (h a) ih

/-- If three finite degree packets have relatively prime total cardinalities,
then their degrees have no common divisor other than one.  In applications the
index types enumerate subgroup orbits and the degree maps give orbit sizes. -/
theorem eq_one_of_dvd_three_partition_degrees
    {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    {d₁ : ι₁ → ℕ} {d₂ : ι₂ → ℕ} {d₃ : ι₃ → ℕ}
    {N₁ N₂ N₃ c : ℕ}
    (hc₁ : ∀ i, c ∣ d₁ i) (hc₂ : ∀ i, c ∣ d₂ i)
    (hc₃ : ∀ i, c ∣ d₃ i)
    (h₁ : ∑ i, d₁ i = N₁) (h₂ : ∑ i, d₂ i = N₂)
    (h₃ : ∑ i, d₃ i = N₃)
    (hgcd : Nat.gcd (Nat.gcd N₁ N₂) N₃ = 1) :
    c = 1 := by
  have hcN₁ : c ∣ N₁ := by
    rw [← h₁]
    exact dvd_sum_univ d₁ hc₁
  have hcN₂ : c ∣ N₂ := by
    rw [← h₂]
    exact dvd_sum_univ d₂ hc₂
  have hcN₃ : c ∣ N₃ := by
    rw [← h₃]
    exact dvd_sum_univ d₃ hc₃
  apply Nat.dvd_one.mp
  rw [← hgcd]
  exact Nat.dvd_gcd (Nat.dvd_gcd hcN₁ hcN₂) hcN₃

end RiemannResearch.GroupTheory
