/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.AlgebraicGeometry.FpqcH1

/-!
# Serre's Conjecture II as an open problem

This module records Serre's Conjecture II as a proposition. It deliberately
does not assert the proposition, introduce it as an axiom, or supply a
placeholder proof.

The project already has a concrete fpqc H1 type for affine group schemes
represented by commutative Hopf algebras. The intrinsic predicates saying that
the base is a perfect field of cohomological dimension at most two and that
the group is semisimple simply connected are not yet available, so the
statement is parameterized by those two predicates.
-/

universe u

namespace RiemannResearch.AlgebraicGeometry.SerreII

/-- Predicate selecting perfect fields of cohomological dimension at most two. -/
abbrev BaseCondition := CommRingCat.{u} → Prop

/-- Predicate selecting semisimple simply connected affine group schemes. -/
abbrev GroupCondition :=
  (R A : CommRingCat.{u}) → [HopfAlgebra R A] → Prop

/-- **Serre's Conjecture II (open problem).**

For every perfect field of cohomological dimension at most two and every
semisimple simply connected group over it, every fpqc H1 class is neutral.

This is a definition of the conjectural proposition, not a proof or an axiom.
-/
def Conjecture
    (IsPerfectFieldCdAtMostTwo : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition) : Prop :=
  ∀ (R A : CommRingCat.{u}) [HopfAlgebra R A],
    IsPerfectFieldCdAtMostTwo R →
    IsSemisimpleSimplyConnected R A →
    ∀ ξ : FpqcH1.{u, u} R A, ξ = FpqcH1.neutral R A

/-- The usual formulation H1(k,G) = {1} is equivalent to saying that the
corresponding fpqc H1 type is a subsingleton. -/
theorem conjecture_iff_subsingleton
    (IsPerfectFieldCdAtMostTwo : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition) :
    Conjecture IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected ↔
      ∀ (R A : CommRingCat.{u}) [HopfAlgebra R A],
        IsPerfectFieldCdAtMostTwo R →
        IsSemisimpleSimplyConnected R A →
        Subsingleton (FpqcH1.{u, u} R A) := by
  constructor
  · intro h R A _ hField hGroup
    refine ⟨fun ξ η => ?_⟩
    rw [h R A hField hGroup ξ, h R A hField hGroup η]
  · intro h R A _ hField hGroup ξ
    exact (h R A hField hGroup).allEq ξ (FpqcH1.neutral R A)

end RiemannResearch.AlgebraicGeometry.SerreII
