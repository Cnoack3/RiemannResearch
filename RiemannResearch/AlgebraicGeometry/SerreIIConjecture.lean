/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.FieldTheory.Perfect
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import RiemannResearch.AlgebraicGeometry.AlgebraicGroupGaloisH1

/-!
# Serre's Conjecture II in pointed Galois cohomology

This module records Serre's Conjecture II as an open proposition. All
cohomology in the Serre-II hierarchy is now the pointed continuous Galois
cohomology `GaloisH1`; no auxiliary covering-site cohomology occurs here.

Mathematically, `H¹(F,G) = {1}` is equivalent to saying that every `G`-torsor
over `F` is trivial, or equivalently has an `F`-rational point. The present
Lean statement uses the Galois-cohomological side directly.

The exact predicates selecting perfect fields of cohomological dimension at
most two and semisimple simply connected reductive groups remain explicit
interfaces because Mathlib does not yet supply those combined intrinsic
predicates at the required level of generality.
-/

universe u

namespace RiemannResearch.AlgebraicGeometry.SerreII

/-- Predicate selecting fields that are perfect and have Galois
cohomological dimension at most two. -/
abbrev BaseCondition :=
  (K : Type u) → [Field K] → Prop

/-- Predicate selecting semisimple simply connected reductive algebraic
groups in Hopf-algebra coordinates. -/
abbrev GroupCondition :=
  (K A : Type u) → [Field K] → [CommRing A] → [HopfAlgebra K A] → Prop

/-- **Serre's Conjecture II (open problem).**

If `G` is a simply connected semisimple algebraic group over a perfect field
`F` of cohomological dimension at most two, then its pointed continuous
Galois cohomology is trivial: `H¹(F,G) = {1}`. Equivalently, every `G`-torsor
over `F` has an `F`-rational point.

This declaration defines the conjectural proposition; it is neither an axiom
nor a proof. -/
def Conjecture
    (IsPerfectFieldCdAtMostTwo : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition) : Prop :=
  ∀ (K A : Type u) [Field K] [CommRing A] [HopfAlgebra K A],
    IsPerfectFieldCdAtMostTwo K →
    IsSemisimpleSimplyConnected K A →
    ∀ ξ : GaloisH1 K A, ξ = GaloisH1.neutral K A

/-- The every-class-neutral formulation is equivalent to saying that the
pointed Galois-cohomology type is a subsingleton. -/
theorem conjecture_iff_subsingleton
    (IsPerfectFieldCdAtMostTwo : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition) :
    Conjecture IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected ↔
      ∀ (K A : Type u) [Field K] [CommRing A] [HopfAlgebra K A],
        IsPerfectFieldCdAtMostTwo K →
        IsSemisimpleSimplyConnected K A →
        Subsingleton (GaloisH1 K A) := by
  constructor
  · intro h K A _ _ _ hField hGroup
    constructor
    intro x y
    calc
      x = GaloisH1.neutral K A := h K A hField hGroup x
      _ = y := (h K A hField hGroup y).symm
  · intro h K A _ _ _ hField hGroup ξ
    exact (h K A hField hGroup).allEq ξ (GaloisH1.neutral K A)

end RiemannResearch.AlgebraicGeometry.SerreII
