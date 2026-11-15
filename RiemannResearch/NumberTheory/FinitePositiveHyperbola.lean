/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Lean.Elab.Tactic.Omega

/-! # Finite positive divisor/multiple rearrangement
Source: user-provided reciprocal-head investigation, Section 2. The theorem
retains every positive product at or below the exact cutoff.
-/

open scoped BigOperators
namespace RiemannResearch.NumberTheory

theorem sum_positive_hyperbola {A : Type*} [AddCommMonoid A]
    (N : ℕ) (F : ℕ → ℕ → A) :
    (∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 (N / k), F k j) =
      ∑ m ∈ Finset.Icc 1 N, ∑ k ∈ m.divisors, F k (m / k) := by
  classical
  have hsum :
      (∑ z ∈ (Finset.Icc 1 N).sigma (fun k => Finset.Icc 1 (N / k)), F z.1 z.2) =
      ∑ z ∈ (Finset.Icc 1 N).sigma (fun m => m.divisors), F z.2 (z.1 / z.2) := by
    apply Finset.sum_bij (fun z _ => (⟨z.1 * z.2, z.1⟩ : Sigma (fun _ : ℕ => ℕ)))
    · intro z hz
      obtain ⟨hk, hj⟩ := Finset.mem_sigma.mp hz
      obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hk
      obtain ⟨hj1, hjN⟩ := Finset.mem_Icc.mp hj
      have hprod : z.1 * z.2 ≤ N := by
        have h := (Nat.le_div_iff_mul_le hk1).mp hjN
        simpa only [Nat.mul_comm] using h
      exact Finset.mem_sigma.mpr
        ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hk1 hj1, hprod⟩,
          Nat.mem_divisors.mpr ⟨dvd_mul_right _ _, (Nat.mul_pos hk1 hj1).ne'⟩⟩
    · intro z hz w hw hzw
      have hk : z.1 = w.1 := congrArg (fun z : Sigma (fun _ : ℕ => ℕ) => z.2) hzw
      have hprod : z.1 * z.2 = w.1 * w.2 :=
        congrArg (fun z : Sigma (fun _ : ℕ => ℕ) => z.1) hzw
      have hk0 : 0 < z.1 := (Finset.mem_Icc.mp (Finset.mem_sigma.mp hz).1).1
      have hj : z.2 = w.2 := Nat.eq_of_mul_eq_mul_left hk0 (by simpa only [hk] using hprod)
      exact Sigma.ext hk (heq_of_eq hj)
    · intro z hz
      obtain ⟨hm, hk⟩ := Finset.mem_sigma.mp hz
      obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
      have hk1 := Nat.pos_of_mem_divisors hk
      have hkd := Nat.dvd_of_mem_divisors hk
      have hkN : z.2 ≤ N := (Nat.le_of_dvd hm1 hkd).trans hmN
      have hdivpos : 0 < z.1 / z.2 := Nat.div_pos (Nat.le_of_dvd hm1 hkd) hk1
      refine ⟨⟨z.2, z.1 / z.2⟩, Finset.mem_sigma.mpr
        ⟨Finset.mem_Icc.mpr ⟨hk1, hkN⟩,
          Finset.mem_Icc.mpr ⟨hdivpos, Nat.div_le_div_right hmN⟩⟩, ?_⟩
      apply Sigma.ext
        (by simpa only [Nat.mul_comm] using Nat.div_mul_cancel hkd)
      exact heq_of_eq rfl
    · intro z hz
      have hk0 : 0 < z.1 := (Finset.mem_Icc.mp (Finset.mem_sigma.mp hz).1).1
      have hdiv : (z.1 * z.2) / z.1 = z.2 := by
        apply Nat.eq_of_mul_eq_mul_left hk0
        simpa only [Nat.mul_comm] using Nat.div_mul_cancel (dvd_mul_right z.1 z.2)
      simp only [hdiv]
  simpa only [Finset.sum_sigma'] using hsum

end RiemannResearch.NumberTheory
