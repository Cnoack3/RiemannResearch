/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.FpqcH1Functoriality

/-!
# Hopf-algebra automorphisms on fpqc H1

The contravariant Hopf spectrum functor, followed by the group-valued Yoneda
functor, sends automorphisms of a commutative Hopf algebra to automorphisms of
its represented affine group presheaf. Inversion before passage to the
opposite category corrects the variance and gives an honest group
homomorphism. Consequently every supplied group action by Hopf automorphisms
acts on fixed-cover and global fpqc H1 and preserves the neutral class.

This is genuine group-scheme coefficient functoriality. It does not construct
the coordinate Hopf algebra or triality automorphisms of split Spin(8).
-/

namespace RiemannResearch.AlgebraicGeometry

open CategoryTheory

universe u v w

noncomputable section

/-- The functor sending a commutative Hopf algebra, contravariantly, to its
represented affine group presheaf. -/
def hopfSpecPresheaf (R : CommRingCat.{u}) :
    (CommHopfAlgCat R)ᵒᵖ ⥤
      ((Over (_root_.AlgebraicGeometry.Spec R))ᵒᵖ ⥤ GrpCat) :=
  _root_.AlgebraicGeometry.hopfSpec R ⋙ yonedaGrp

/-- A bialgebra morphism induces the contravariant morphism of represented
affine group presheaves. -/
def affineGroupPresheafHomOfBialgHom
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [HopfAlgebra R A] [HopfAlgebra R B]
    (f : A →ₐc[R] B) :
    affineGroupPresheaf (CommRingCat.of R) (CommRingCat.of B) ⟶
      affineGroupPresheaf (CommRingCat.of R) (CommRingCat.of A) :=
  yonedaGrp.map
    ((_root_.AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
      (CommHopfAlgCat.ofHom f).op)

/-- A Hopf-algebra isomorphism induces the contravariant isomorphism of
represented affine group presheaves. -/
def affineGroupPresheafIsoOfHopfIso
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [HopfAlgebra R A] [HopfAlgebra R B]
    (e : CommHopfAlgCat.of R A ≅ CommHopfAlgCat.of R B) :
    affineGroupPresheaf (CommRingCat.of R) (CommRingCat.of B) ≅
      affineGroupPresheaf (CommRingCat.of R) (CommRingCat.of A) :=
  yonedaGrp.mapIso
    ((_root_.AlgebraicGeometry.hopfSpec (CommRingCat.of R)).mapIso e.op)

/-- Inversion corrects the contravariance of op, producing a genuine
homomorphism on categorical automorphism groups. -/
def inverseOpAutHom {C : Type u} [Category.{v} C] (X : C) :
    CategoryTheory.Aut X →* CategoryTheory.Aut (Opposite.op X) where
  toFun e := e.symm.op
  map_one' := by
    ext
    rfl
  map_mul' e f := by
    ext
    rfl

/-- Hopf automorphisms act on the represented affine group presheaf. -/
def hopfAutToPresheafAut
    (R A : Type u) [CommRing R] [CommRing A] [HopfAlgebra R A] :
    CategoryTheory.Aut (CommHopfAlgCat.of R A) →*
      CategoryTheory.Aut
        (affineGroupPresheaf (CommRingCat.of R) (CommRingCat.of A)) :=
  ((hopfSpecPresheaf (CommRingCat.of R)).mapAut
      (Opposite.op (CommHopfAlgCat.of R A))).comp
    (inverseOpAutHom (CommHopfAlgCat.of R A))

/-- A supplied action by Hopf automorphisms induces an action on the
represented affine group presheaf. -/
def presheafActionOfHopfAction
    {Γ : Type w} [Group Γ]
    (R A : Type u) [CommRing R] [CommRing A] [HopfAlgebra R A]
    (ρ : Γ →* CategoryTheory.Aut (CommHopfAlgCat.of R A)) :
    Γ →* CategoryTheory.Aut
      (affineGroupPresheaf (CommRingCat.of R) (CommRingCat.of A)) :=
  (hopfAutToPresheafAut R A).comp ρ

/-- A presheaf action acts on fixed-cover nonabelian Cech H1. -/
def FpqcCechH1.actionOfPresheafAction
    {Γ : Type w} [Group Γ]
    (R A : CommRingCat.{u}) [HopfAlgebra R A]
    {I : Type v} (U : FpqcCover R I)
    (ρ : Γ →* CategoryTheory.Aut (affineGroupPresheaf R A)) :
    Γ →* Equiv.Perm (FpqcCechH1 R A U) :=
  PresheafH1.action ρ

@[simp] theorem FpqcCechH1.actionOfPresheafAction_neutral
    {Γ : Type w} [Group Γ]
    (R A : CommRingCat.{u}) [HopfAlgebra R A]
    {I : Type v} (U : FpqcCover R I)
    (ρ : Γ →* CategoryTheory.Aut (affineGroupPresheaf R A))
    (g : Γ) :
    FpqcCechH1.actionOfPresheafAction R A U ρ g
        (FpqcCechH1.neutral R A U) =
      FpqcCechH1.neutral R A U := by
  change PresheafH1.map (ρ g).hom 1 = 1
  exact PresheafH1.map_one _

/-- Hopf automorphisms act on fixed-cover nonabelian Cech H1. -/
def FpqcCechH1.hopfAutAction
    (R A : Type u) [CommRing R] [CommRing A] [HopfAlgebra R A]
    {I : Type v} (U : FpqcCover (CommRingCat.of R) I) :
    CategoryTheory.Aut (CommHopfAlgCat.of R A) →*
      Equiv.Perm (FpqcCechH1
        (CommRingCat.of R) (CommRingCat.of A) U) :=
  FpqcCechH1.actionOfPresheafAction
    (CommRingCat.of R) (CommRingCat.of A) U
    (hopfAutToPresheafAut R A)

@[simp] theorem FpqcCechH1.hopfAutAction_neutral
    (R A : Type u) [CommRing R] [CommRing A] [HopfAlgebra R A]
    {I : Type v} (U : FpqcCover (CommRingCat.of R) I)
    (e : CategoryTheory.Aut (CommHopfAlgCat.of R A)) :
    FpqcCechH1.hopfAutAction R A U e
        (FpqcCechH1.neutral
          (CommRingCat.of R) (CommRingCat.of A) U) =
      FpqcCechH1.neutral
        (CommRingCat.of R) (CommRingCat.of A) U :=
  FpqcCechH1.actionOfPresheafAction_neutral
    (CommRingCat.of R) (CommRingCat.of A) U
    (hopfAutToPresheafAut R A) e

/-- Hopf automorphisms act on global fpqc nonabelian Cech H1. -/
def FpqcH1.hopfAutAction
    (R A : Type u) [CommRing R] [CommRing A] [HopfAlgebra R A] :
    CategoryTheory.Aut (CommHopfAlgCat.of R A) →*
      Equiv.Perm (FpqcH1.{u, v}
        (CommRingCat.of R) (CommRingCat.of A)) :=
  FpqcH1.autAction.comp (hopfAutToPresheafAut R A)

@[simp] theorem FpqcH1.hopfAutAction_neutral
    (R A : Type u) [CommRing R] [CommRing A] [HopfAlgebra R A]
    (e : CategoryTheory.Aut (CommHopfAlgCat.of R A)) :
    FpqcH1.hopfAutAction R A e
        (FpqcH1.neutral (CommRingCat.of R) (CommRingCat.of A)) =
      FpqcH1.neutral (CommRingCat.of R) (CommRingCat.of A) :=
  FpqcH1.map_neutral _

/-- A supplied action by Hopf automorphisms acts on global fpqc H1. -/
def FpqcH1.actionOfHopfAction
    {Γ : Type w} [Group Γ]
    (R A : Type u) [CommRing R] [CommRing A] [HopfAlgebra R A]
    (ρ : Γ →* CategoryTheory.Aut (CommHopfAlgCat.of R A)) :
    Γ →* Equiv.Perm (FpqcH1.{u, v}
      (CommRingCat.of R) (CommRingCat.of A)) :=
  FpqcH1.hopfAutAction R A |>.comp ρ

@[simp] theorem FpqcH1.actionOfHopfAction_neutral
    {Γ : Type w} [Group Γ]
    (R A : Type u) [CommRing R] [CommRing A] [HopfAlgebra R A]
    (ρ : Γ →* CategoryTheory.Aut (CommHopfAlgCat.of R A))
    (g : Γ) :
    FpqcH1.actionOfHopfAction R A ρ g
        (FpqcH1.neutral (CommRingCat.of R) (CommRingCat.of A)) =
      FpqcH1.neutral (CommRingCat.of R) (CommRingCat.of A) :=
  FpqcH1.hopfAutAction_neutral R A (ρ g)

end

end RiemannResearch.AlgebraicGeometry
