/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.NumberTheory.MertensShiftedTest
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Divisor rearrangement for finite shifted Möbius tests

For the finite positive cutoff, count each divisor by the number of its
positive multiples up to the cutoff. This is the finite rearrangement
appearing in the shifted Möbius pairing of the displacement manuscript.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.NumberTheory.MertensShiftedTest

/-- Interchanging divisors and multiples in a finite positive head. -/
theorem sum_divisors_Icc_eq_floor_sum (n : ℕ) (f : ℕ → ℂ) :
    (∑ m ∈ Finset.Icc 1 n, ∑ k ∈ m.divisors, f k) =
      ∑ k ∈ Finset.Icc 1 n, f k * ((n / k : ℕ) : ℂ) := by
  classical
  have hI : Finset.Icc 1 n = Finset.Ioc 0 n := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hI]
  have hd (m : ℕ) (hm : m ∈ Finset.Ioc 0 n) :
      m.divisors = (Finset.Ioc 0 n).filter (fun k => k ∣ m) := by
    obtain ⟨hm0,hmn⟩ := Finset.mem_Ioc.mp hm
    ext k
    constructor
    · intro hk
      have hkm := Nat.dvd_of_mem_divisors hk
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Ioc.mpr ⟨Nat.pos_of_mem_divisors hk, (Nat.le_of_dvd hm0 hkm).trans hmn⟩, hkm⟩
    · intro hk
      exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hk).2, hm0.ne'⟩
  calc
    _ = ∑ m ∈ Finset.Ioc 0 n, ∑ k ∈ Finset.Ioc 0 n, if k ∣ m then f k else 0 := by
      refine Finset.sum_congr rfl ?_
      intro m hm
      rw [hd m hm, Finset.sum_filter]
    _ = ∑ k ∈ Finset.Ioc 0 n, ∑ m ∈ Finset.Ioc 0 n, if k ∣ m then f k else 0 :=
      Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      rw [← Finset.sum_filter, Finset.sum_const, Nat.Ioc_filter_dvd_card_eq_div,
        nsmul_eq_mul, mul_comm]

/-- The finite sum of the coefficients of ζ(z)/ζ(z+s) as a single
Möbius-weighted sum of integer quotients. -/
theorem sum_shiftedCoeff_eq_floor_sum (n : ℕ) (s : ℂ) :
    (∑ m ∈ Finset.Icc 1 n, shiftedCoeff m s) =
      ∑ k ∈ Finset.Icc 1 n, ((ArithmeticFunction.moebius k : ℂ) * (k : ℂ) ^ (-s)) *
        ((n / k : ℕ) : ℂ) :=
  sum_divisors_Icc_eq_floor_sum n _

end RiemannResearch.NumberTheory.MertensShiftedTest
