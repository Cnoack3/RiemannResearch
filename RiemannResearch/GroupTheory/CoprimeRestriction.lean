/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Data.Int.GCD

/-!
# Coprime restriction--corestriction

This module isolates the elementary abelian argument behind coprime-degree
descent. It deliberately assumes additive restriction and corestriction maps;
it does not assert that such maps exist for nonabelian cohomology.
-/

namespace RiemannResearch.GroupTheory

/-- Two restriction maps with coprime index formulas jointly detect zero.

This is the precise abelian Bézout step used by the degree-five/degree-six
two-gauge audit. The statement does not apply to pointed nonabelian H¹.
-/
theorem eq_zero_of_coprime_restrictions
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (resM : A →+ B) (resN : A →+ C)
    (corM : B →+ A) (corN : C →+ A)
    {m n : ℕ}
    (hM : ∀ x, corM (resM x) = m • x)
    (hN : ∀ x, corN (resN x) = n • x)
    (hcop : m.Coprime n)
    {x : A} (hxM : resM x = 0) (hxN : resN x = 0) : x = 0 := by
  apply (nsmul_eq_zero_iff_of_coprime hcop).mp
  constructor
  · rw [← hM x, hxM, map_zero]
  · rw [← hN x, hxN, map_zero]

end RiemannResearch.GroupTheory
