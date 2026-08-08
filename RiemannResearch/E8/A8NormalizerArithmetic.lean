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

end RiemannResearch.E8
