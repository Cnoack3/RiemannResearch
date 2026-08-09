/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Abel

/-!
# Odd-degree restriction modulo two

The additive restriction-corestriction argument underlying Theorem 10.35 of
the user-provided 27 July 2026 rational-involutions manuscript.
-/

namespace RiemannResearch.GroupCohomology

/-- Additive restriction-corestriction form of Theorem 10.35. -/
theorem odd_degree_restriction_injective_mod_two
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (res : A →+ B) (cor : B →+ A) {d : ℕ}
    (hindex : ∀ x, cor (res x) = d • x) (hodd : Odd d)
    {x : A} (hres : ∃ y : B, res x = 2 • y) :
    ∃ z : A, x = 2 • z := by
  obtain ⟨q, rfl⟩ := hodd
  obtain ⟨y, hy⟩ := hres
  refine ⟨cor y - q • x, ?_⟩
  have hcor : (2 * q + 1) • x = 2 • cor y := by
    rw [← hindex x, hy, map_nsmul]
  simp only [add_nsmul, one_nsmul, mul_nsmul] at hcor
  have hs : q • 2 • x = 2 • q • x := by
    rw [← mul_nsmul, ← mul_nsmul, Nat.mul_comm]
  rw [hs] at hcor
  have hx : x = 2 • cor y - 2 • q • x :=
    eq_sub_iff_add_eq'.2 hcor
  calc
    x = 2 • cor y - 2 • q • x := hx
    _ = 2 • (cor y - q • x) := by
      simp only [two_nsmul]
      abel

end RiemannResearch.GroupCohomology
