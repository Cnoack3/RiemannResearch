/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-!
# fpqc torsors under group objects

This module defines fpqc torsors in the slice category of schemes. A torsor is
a module object whose action is simply transitive and whose structure morphism
is faithfully flat and quasi-compact.

It does not yet prove effective fpqc descent or identify isomorphism classes of
torsors with the global nonabelian Čech `H¹` carrier.
-/

namespace RiemannResearch.AlgebraicGeometry

open CategoryTheory

universe u

/-- A group action is simply transitive when the canonical map
`G × P ⟶ P × P` is an isomorphism. -/
def IsSimplyTransitive
    (X : _root_.AlgebraicGeometry.Scheme.{u})
    (G : Over X) [GrpObj G]
    (P : CategoryTheory.Mod (Over X) G) : Prop :=
  let _ : ModObj G P.X := P.mod
  IsIso (ModObj.leftSMul G P.X)

/-- An fpqc torsor is a simply transitive group action whose structure
morphism is flat, surjective, and quasi-compact. -/
def IsFpqcTorsor
    (X : _root_.AlgebraicGeometry.Scheme.{u})
    (G : Over X) [GrpObj G]
    (P : CategoryTheory.Mod (Over X) G) : Prop :=
  IsSimplyTransitive X G P ∧
    _root_.AlgebraicGeometry.Flat P.X.hom ∧
    _root_.AlgebraicGeometry.Surjective P.X.hom ∧
    _root_.AlgebraicGeometry.QuasiCompact P.X.hom

/-- The full subcategory of fpqc torsors under `G` over `X`. -/
abbrev FpqcTorsor
    (X : _root_.AlgebraicGeometry.Scheme.{u})
    (G : Over X) [GrpObj G] :=
  ObjectProperty.FullSubcategory (IsFpqcTorsor X G)

/-- Simple transitivity is equivalent to existence and uniqueness of the
group element carrying any generalized point of the torsor to any other. -/
theorem isSimplyTransitive_iff
    (X : _root_.AlgebraicGeometry.Scheme.{u})
    (G : Over X) [GrpObj G]
    (P : CategoryTheory.Mod (Over X) G) :
    IsSimplyTransitive X G P ↔
      ∀ (Z : Over X) (x y : Z ⟶ P.X),
        ∃! m : Z ⟶ G, m • x = y := by
  let _ : ModObj G P.X := P.mod
  exact ModObj.isIso_leftSMul_iff

end RiemannResearch.AlgebraicGeometry
