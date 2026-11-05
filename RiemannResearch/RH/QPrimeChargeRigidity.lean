/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QChargeDilation
import Mathlib.Data.Nat.Squarefree

/-! # One-sided bounded jumps after all composite charges cancel

Finite products can select the primes carrying positive signed charge.
At such a product the divisor sum reads off their total, since every
other divisor beyond one is a composite with zero charge. -/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QPrimeChargeRigidity
open Pareto ZetaTwoHilbert QSquarefreeDisplacementRigidity

/-- A one-sided bound for divisor sums bounds the mass on the same side
when the charges beyond one are supported on primes. -/
theorem positive_mass_of_prime_support (b : ℕ → ℝ) (C : ℝ)
    (hz : ∀ m, 1 < m → ¬m.Prime → b m = 0)
    (hu : ∀ n, 0 < n → (∑ m ∈ n.divisors, b m) ≤ C) (H : ℕ) :
    (∑ m ∈ Finset.Icc 1 H, max (b m) 0) ≤ max (b 1) 0 + (C - b 1) := by
  classical
  let U := Finset.Icc 1 H
  let S := U.filter (fun m => m ≠ 1 ∧ 0 < b m)
  let n := ∏ p ∈ S, p
  have hp (p : ℕ) (hp : p ∈ S) : p.Prime := by
    have hh := Finset.mem_filter.mp hp
    have hp1 := (Finset.mem_Icc.mp hh.1).1
    by_contra hn
    have hb := hz p (by have := hh.2.1; omega) hn
    exact (ne_of_gt hh.2.2) hb
  have hn : 0 < n := Finset.prod_pos (fun p hm => (hp p hm).pos)
  have hay : n.primeFactors = S := Nat.primeFactors_prod hp
  have hnot : 1 ∉ S := fun hm => (Finset.mem_filter.mp hm).2.1 rfl
  have hsub : insert 1 S ⊆ n.divisors := by
    intro m hm
    rw [Finset.mem_insert] at hm
    rcases hm with h1 | hm
    · subst m
      exact Nat.mem_divisors.mpr ⟨one_dvd _, hn.ne'⟩
    · exact Nat.mem_divisors.mpr ⟨Finset.dvd_prod_of_mem id hm, hn.ne'⟩
  have hdiv : (∑ m ∈ n.divisors, b m) = b 1 + ∑ m ∈ S, b m := by
    calc
      _ = ∑ m ∈ insert 1 S, b m := by
        symm
        apply Finset.sum_subset hsub
        intro m hm hno
        have h1 : m ≠ 1 := fun he => hno (Finset.mem_insert.mpr (Or.inl he))
        have hs : m ∉ S := fun he => hno (Finset.mem_insert.mpr (Or.inr he))
        have hpos := Nat.pos_of_mem_divisors hm
        apply hz m (by omega)
        intro hpr
        apply hs
        rw [← hay]
        exact Nat.mem_primeFactors.mpr ⟨hpr, (Nat.mem_divisors.mp hm).1, hn.ne'⟩
      _ = _ := Finset.sum_insert hnot
  have hupper := hu n hn
  rw [hdiv] at hupper
  have hex : (∑ m ∈ U, max (b m) 0) =
      (if 1 ∈ U then max (b 1) 0 else 0) + ∑ m ∈ S, b m := by
    calc
      _ = ∑ m ∈ U, ((if m = 1 then max (b 1) 0 else 0) +
          (if m ≠ 1 ∧ 0 < b m then b m else 0)) := by
        apply Finset.sum_congr rfl
        intro m _
        by_cases h1 : m = 1
        · simp [h1]
        · by_cases hpos : 0 < b m
          · simp [h1, hpos, max_eq_left hpos.le]
          · simp [h1, hpos, max_eq_right (le_of_not_gt hpos)]
      _ = _ := by
        rw [Finset.sum_add_distrib]
        congr 1
        · simp
        · exact (Finset.sum_filter ..).symm
  change (∑ m ∈ U, max (b m) 0) ≤ _
  rw [hex]
  apply add_le_add _ (by linarith only [hupper])
  split_ifs
  · rfl
  · exact le_max_right _ _

/-- For the matched displacement a finite upper bound on either signed
jump suffices once all of its composite Möbius charges vanish. -/
theorem riemannHypothesis_of_prime_charge_bounded_jump (σ C : ℝ) (hσ : |σ| = 1)
    (hz : ∀ m, 1 < m → ¬m.Prime → mobiusDifference m (qSequence displacement) = 0)
    (hu : ∀ n : ℕ, 0 < n → σ * (qSequence displacement n -
      qSequence displacement (n - 1)) ≤ C) : RiemannHypothesis := by
  let b (m : ℕ) := σ * mobiusDifference m (qSequence displacement)
  have h0 (m : ℕ) (hm : 1 < m) (hn : ¬m.Prime) : b m = 0 := by simp [b, hz m hm hn]
  have hdiv (n : ℕ) (hn : 0 < n) : (∑ m ∈ n.divisors, b m) ≤ C := by
    simpa only [b, ← Finset.mul_sum, sum_mobiusDifference _ n hn] using hu n hn
  apply QChargeDilation.riemannHypothesis_of_one_sided_charges (-σ)
    (max (b 1) 0 + (C - b 1)) (by simpa only [abs_neg] using hσ)
  intro H
  simpa only [neg_mul, neg_neg, b] using positive_mass_of_prime_support b C h0 hdiv H

end RiemannResearch.RH.QPrimeChargeRigidity
