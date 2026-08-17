/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.FieldTheory.Perfect
import RiemannResearch.AlgebraicGeometry.FpqcH1
import RiemannResearch.AlgebraicGeometry.FpqcTorsor

/-!
# Serre's Conjecture II as an open problem

This module records Serre's Conjecture II as a proposition. It deliberately
does not assert the proposition, introduce it as an axiom, or supply a
placeholder proof.

The imports make the closest existing foundations available:

* Mathlib's exact `PerfectField` predicate;
* Mathlib's `LieAlgebra.IsSemisimple` predicate;
* the project's scheme-level `IsFpqcTorsor` and `FpqcTorsor` definitions;
* the project's concrete nonabelian fpqc `H¹` type `FpqcH1`.

The Lie-algebra predicate is not a definition of a semisimple affine group
scheme. Moreover, neither Mathlib nor this project yet supplies the intrinsic
predicate that an affine group scheme is semisimple and simply connected, or
the Galois-cohomological-dimension predicate needed here. Consequently the
global statement remains parameterized by those exact missing group-scheme
and field-arithmetic conditions; no Lie-algebra condition is substituted for
the former.
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

/-- Serre II is equivalent to the concrete local task of neutralizing every
fixed-cover Čech class after pullback along a witnessed fpqc refinement. -/
theorem conjecture_iff_every_class_locally_neutral
    (Base : BaseCondition)
    (Group : GroupCondition) :
    Conjecture Base Group ↔
      ∀ (R A : CommRingCat.{u}) [HopfAlgebra R A],
        Base R →
        Group R A →
        ∀ (I : Type u) (U : FpqcCover R I) (ξ : FpqcCechH1 R A U),
          ∃ (K : Type u) (W : FpqcCover R K) (r : W.Refinement U),
            r.pullbackH1 ξ = FpqcCechH1.neutral R A W := by
  rw [conjecture_iff_subsingleton]
  constructor
  · intro h R A _ hBase hGroup
    exact (FpqcH1.subsingleton_iff_every_class_locally_neutral R A).mp
      (h R A hBase hGroup)
  · intro h R A _ hBase hGroup
    exact (FpqcH1.subsingleton_iff_every_class_locally_neutral R A).mpr
      (h R A hBase hGroup)

end RiemannResearch.AlgebraicGeometry.SerreII
