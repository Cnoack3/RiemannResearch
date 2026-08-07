/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib

/-!
# Arithmetic of the three E8 Weyl-index packets

This module checks the numerical consequences of the three proposed reduction
degrees `135`, `2240`, and `48384`. It deliberately does not construct the
finite fixed loci or prove that their residue fields split an E8 torsor; those
are geometric inputs in the manuscript.
-/

namespace RiemannResearch.E8

/-- A small integral Bezout relation for the three packet degrees. -/
theorem weylIndexPacket_bezout :
    (-73 : ℤ) * 135 + 26 * 2240 - 48384 = 1 := by
  norm_num

/-- The three Weyl-index packet degrees have gcd one. -/
theorem weylIndexPacket_gcd : Nat.gcd (Nat.gcd 135 2240) 48384 = 1 := by
  norm_num

/-- If finitely many natural degrees sum to `135`, at least one is odd.

This is the exact parity step used to pass from an effective degree-135
splitting cycle to an odd-degree splitting field.
-/
theorem exists_odd_of_sum_eq_135 {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (hsum : ∑ i, d i = 135) :
    ∃ i, Odd (d i) := by
  by_contra h
  push Not at h
  have heven : ∀ i, Even (d i) := fun i => Nat.not_odd_iff_even.mp (h i)
  have hcast : ((∑ i, d i : ℕ) : ZMod 2) = 0 := by
    rw [Nat.cast_sum]
    apply Finset.sum_eq_zero
    intro i hi
    obtain ⟨m, hm⟩ := heven i
    rw [hm, Nat.cast_add]
    change (m : ZMod 2) + m = 0
    calc
      (m : ZMod 2) + m = (2 : ZMod 2) * m := by ring
      _ = 0 := by
        have htwo : (2 : ZMod 2) = 0 := by decide
        rw [htwo, zero_mul]
  rw [hsum] at hcast
  have hne : (135 : ZMod 2) ≠ 0 := by decide
  exact hne hcast

/-- Every residue modulo 135 has a bounded nonnegative representative using
2240 and 48384. This finite certificate underlies the explicit symmetric-power
bound in the manuscript. -/
theorem exists_bounded_weylIndexPacket_residue :
    ∀ r : Fin 135, ∃ a : Fin 27, ∃ b : Fin 5,
      (2240 * a.val + 48384 * b.val) % 135 = r.val := by
  set_option maxRecDepth 100000 in
    decide

/-- The largest bound produced by the elementary residue construction. -/
theorem weylIndexPacket_residue_bound :
    26 * 2240 + 4 * 48384 = 251776 := by
  norm_num

/-- An element of an abelian group annihilated by the three packet degrees is
zero. This is only an additive shadow; it says nothing about a pointed
nonabelian neutral fiber. -/
theorem eq_zero_of_weylIndexPacket_annihilators
    {A : Type*} [AddCommGroup A] {x : A}
    (h135 : 135 • x = 0) (h2240 : 2240 • x = 0)
    (h48384 : 48384 • x = 0) : x = 0 := by
  have h5 : 5 • x = 0 := by
    have h27 : 27 • (5 • x) = 0 := by
      rw [← mul_nsmul]
      norm_num
      exact h135
    have h448 : 448 • (5 • x) = 0 := by
      rw [← mul_nsmul]
      norm_num
      exact h2240
    apply (nsmul_eq_zero_iff_of_coprime
      (by norm_num : Nat.Coprime 27 448)).mp
    exact ⟨h27, h448⟩
  exact (nsmul_eq_zero_iff_of_coprime
    (by norm_num : Nat.Coprime 5 48384)).mp ⟨h5, h48384⟩

end RiemannResearch.E8
