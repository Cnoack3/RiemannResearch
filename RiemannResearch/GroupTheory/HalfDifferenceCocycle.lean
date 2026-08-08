/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Tactic.Abel

/-!
# The half-difference cocycle

This module verifies the elementary cocycle calculation used to lift an
invariant class modulo two from an anti-invariant lattice.  The hypotheses
isolate the divisibility and torsion-freeness inputs from the application to
the ramified `E₈` valuation packet.
-/

namespace RiemannResearch.GroupTheory

/-- If `a(g)` is the unique half of `ell - g • ell`, then `a` satisfies the
one-cocycle identity. -/
theorem halfDifference_cocycle
    {Γ B : Type*} [Group Γ] [AddCommGroup B] [DistribMulAction Γ B]
    (two_nsmul_injective : Function.Injective (fun x : B => 2 • x))
    (ell : B) (a : Γ → B)
    (ha : ∀ g, 2 • a g = ell - g • ell) :
    ∀ g h, a (g * h) = a g + g • a h := by
  intro g h
  have hcomm : 2 • (g • a h) = g • (2 • a h) := by
    exact (map_nsmul (DistribMulAction.toAddMonoidEnd Γ B g) 2 (a h)).symm
  have hha := congrArg (fun x : B => g • x) (ha h)
  simp only [smul_sub] at hha
  apply two_nsmul_injective
  change 2 • a (g * h) = 2 • (a g + g • a h)
  rw [ha, nsmul_add, ha, hcomm, hha, mul_smul]
  abel

/-- At an element acting by minus one on `ell`, the half-difference cocycle
takes the value `ell`. -/
theorem halfDifference_at_involution
    {Γ B : Type*} [Group Γ] [AddCommGroup B] [DistribMulAction Γ B]
    (two_nsmul_injective : Function.Injective (fun x : B => 2 • x))
    (ell : B) (a : Γ → B)
    (ha : ∀ g, 2 • a g = ell - g • ell)
    (c : Γ) (hc : c • ell = -ell) :
    a c = ell := by
  apply two_nsmul_injective
  change 2 • a c = 2 • ell
  rw [ha, hc]
  simp [two_nsmul]

end RiemannResearch.GroupTheory
