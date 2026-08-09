/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Tactic.Abel

/-!
# Fibers of additive boundary maps

The affine-kernel-fiber statement underlying Theorem 10.51 of the
user-provided 27 July 2026 rational-involutions manuscript.
-/

namespace RiemannResearch.GroupCohomology

/-- The affine-fiber statement behind Theorem 10.51. -/
theorem boundary_fiber_is_kernel_torsor
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (boundary : A →+ B) (e : B) (x : A) (hx : boundary x = e) :
    ∀ y : A, boundary y = e ↔
      ∃! k : boundary.ker, y = x + (k : A) := by
  intro y
  constructor
  · intro hy
    let k : boundary.ker := ⟨y - x, by
      simp [AddMonoidHom.mem_ker, map_sub, hy, hx]⟩
    refine ⟨k, ?_, ?_⟩
    · change y = x + (y - x)
      abel
    · intro k' hk'
      apply Subtype.ext
      change (k' : A) = y - x
      rw [hk']
      abel
  · rintro ⟨k, hk, -⟩
    rw [hk, map_add, hx]
    simp [AddMonoidHom.mem_ker.mp k.property]

end RiemannResearch.GroupCohomology
