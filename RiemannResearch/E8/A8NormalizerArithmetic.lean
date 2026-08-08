/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.GCD

/-!
# Arithmetic of the A8 solvable-normalizer cover

This module formalizes the exact additive arithmetic behind the subsystem
fields of degrees 15, 35, and 336. It does not construct those fields or
supply a corestriction in nonabelian H¹.
-/

namespace RiemannResearch.E8

/-- The three A8 cover degrees have the displayed integral Bezout relation. -/
theorem a8Normalizer_bezout :
    (-27 : ℤ) * 15 + 2 * 35 + 336 = 1 := by
  norm_num

/-- An element of an abelian group killed by 15, 35, and 336 is zero.

This is the additive detection step supplied by the point, plane, and
solvable Sylow-5 normalizer fields. It deliberately says nothing about
a pointed nonabelian neutral fiber.
-/
theorem eq_zero_of_a8_annihilators
    {A : Type*} [AddCommGroup A] {x : A}
    (h15 : 15 • x = 0) (h35 : 35 • x = 0) (h336 : 336 • x = 0) :
    x = 0 := by
  have h5 : 5 • x = 0 := by
    apply (nsmul_eq_zero_iff_of_coprime
      (by norm_num : Nat.Coprime 3 7)).mp
    constructor
    · rw [← mul_nsmul]
      norm_num
      exact h15
    · rw [← mul_nsmul]
      norm_num
      exact h35
  exact (nsmul_eq_zero_iff_of_coprime
    (by norm_num : Nat.Coprime 5 336)).mp ⟨h5, h336⟩
/-- The overlap and Sylow-five field degrees in PDF Proposition 6.7. -/
theorem serreIIProgram_a8Gauge_field_degrees :
    20160 / 192 = 105 ∧ 20160 / 5 = 4032 := by
  norm_num

/-- An integral Bezout certificate for the three degrees in PDF Proposition 6.7. -/
theorem serreIIProgram_a8Gauge_bezout :
    (-3226 : ℤ) * 15 + 1613 * 35 - 2 * 4032 = 1 := by
  norm_num

/-- The three degrees in PDF Proposition 6.7 have gcd one. -/
theorem serreIIProgram_a8Gauge_gcd :
    Nat.gcd (Nat.gcd 15 35) 4032 = 1 := by
  norm_num

/-- The additive restriction--corestriction shadow of PDF Proposition 6.7. -/
theorem eq_zero_of_serreIIProgram_a8Gauge_annihilators
    {A : Type*} [AddCommGroup A] {x : A}
    (h15 : 15 • x = 0) (h35 : 35 • x = 0) (h4032 : 4032 • x = 0) :
    x = 0 := by
  have h5 : 5 • x = 0 := by
    apply (nsmul_eq_zero_iff_of_coprime
      (by norm_num : Nat.Coprime 3 7)).mp
    constructor
    · rw [← mul_nsmul]
      norm_num
      exact h15
    · rw [← mul_nsmul]
      norm_num
      exact h35
  exact (nsmul_eq_zero_iff_of_coprime
    (by norm_num : Nat.Coprime 5 4032)).mp ⟨h5, h4032⟩


end RiemannResearch.E8
