/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.FpqcH1ChangeOfBase
import RiemannResearch.AlgebraicGeometry.FpqcH1ScalarExtension

/-!
# Canonical scalar extension on fpqc H¹

This module constructs scalar extension rather than merely postulating it.
It base-changes indexed fpqc covers, transports nonabelian Čech cocycles
through the pullback adjunction, checks compatibility with refinements, and
descends the construction to global fpqc Čech H¹.

For a commutative Hopf algebra `A` over `R` and an `R`-algebra `S`,
the target coefficient algebra is the genuine tensor-product base change
`S ⊗[R] A`.  The comparison of represented group-valued presheaves is
packaged as a natural isomorphism.
-/

namespace RiemannResearch.AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits CategoryTheory.Over
open CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

universe u v w

noncomputable section

/-- The morphism of affine bases induced by an algebra structure `R → S`. -/
abbrev scalarExtensionSpecMap
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    _root_.AlgebraicGeometry.Spec (CommRingCat.of S) ⟶
      _root_.AlgebraicGeometry.Spec (CommRingCat.of R) :=
  _root_.AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (algebraMap R S))

/-- Pull an indexed fpqc cover back along a morphism of affine bases. -/
def FpqcCover.baseChangeAlong {R S : CommRingCat.{u}}
    (f : _root_.AlgebraicGeometry.Spec S ⟶
      _root_.AlgebraicGeometry.Spec R)
    {I : Type v} (U : FpqcCover R I) : FpqcCover S I where
  obj i := (Over.pullback f).obj (U.obj i)
  mem_fpqc := by
    change Presieve.ofArrows
      (fun i => pullback (U.obj i).hom f)
      (fun i => pullback.snd (U.obj i).hom f) ∈
        _root_.AlgebraicGeometry.Scheme.fpqcPrecoverage.coverings
          (_root_.AlgebraicGeometry.Spec S)
    rw [Presieve.ofArrows_pullback]
    exact Precoverage.pullbackArrows_mem f U.mem_fpqc

/-- Pull a refinement of indexed fpqc covers back along a base morphism. -/
def FpqcCover.Refinement.baseChangeAlong
    {R S : CommRingCat.{u}}
    (f : _root_.AlgebraicGeometry.Spec S ⟶
      _root_.AlgebraicGeometry.Spec R)
    {I : Type v} {J : Type w}
    {U : FpqcCover R I} {V : FpqcCover R J}
    (r : V.Refinement U) :
    (V.baseChangeAlong f).Refinement (U.baseChangeAlong f) where
  index := r.index
  hom j := (Over.pullback f).map (r.hom j)

/-- The adjunction counit from a base-changed cover object to the old cover. -/
def FpqcCover.baseChangeProjection
    {R S : CommRingCat.{u}}
    (f : _root_.AlgebraicGeometry.Spec S ⟶
      _root_.AlgebraicGeometry.Spec R)
    {I : Type v} (U : FpqcCover R I) (i : I) :
    (Over.map f).obj ((U.baseChangeAlong f).obj i) ⟶ U.obj i :=
  (Over.mapPullbackAdj f).counit.app (U.obj i)

/-- Base-change projections commute with refinement morphisms. -/
theorem FpqcCover.Refinement.baseChangeProjection_naturality
    {R S : CommRingCat.{u}}
    (f : _root_.AlgebraicGeometry.Spec S ⟶
      _root_.AlgebraicGeometry.Spec R)
    {I : Type v} {J : Type w}
    {U : FpqcCover R I} {V : FpqcCover R J}
    (r : V.Refinement U) (j : J) :
    (Over.map f).map ((r.baseChangeAlong f).hom j) ≫
        U.baseChangeProjection f (r.index j) =
      V.baseChangeProjection f j ≫ r.hom j :=
  (Over.mapPullbackAdj f).counit.naturality (r.hom j)

/-- A pullback adjunction identifies a restricted represented group presheaf
with the presheaf represented by the pulled-back group object. -/
def overMapYonedaGrpIso
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    {X Y : C} (f : X ⟶ Y)
    [CartesianMonoidalCategory (Over X)]
    [CartesianMonoidalCategory (Over Y)]
    [(Over.pullback f).Monoidal]
    (G : Grp (Over Y)) :
    (Over.map f).op ⋙ yonedaGrp.obj G ≅
      yonedaGrp.obj ((Over.pullback f).mapGrp.obj G) := by
  let H := (Over.pullback f).mapGrp.obj G
  letI : GrpObj ((Over.pullback f).obj G.X) := H.grp
  change (Over.map f).op ⋙ yonedaGrp.obj G ≅
    yonedaGrpObj ((Over.pullback f).obj G.X)
  refine NatIso.ofComponents
    (fun T => MulEquiv.toGrpIso
      { toEquiv := (Over.mapPullbackAdj f).homEquiv T.unop G.X
        map_mul' := ?_ }) ?_
  · intro a b
    let a' : (Over.map f).obj T.unop ⟶ G.X := a
    let b' : (Over.map f).obj T.unop ⟶ G.X := b
    let pa := (Over.pullback f).map a'
    let pb := (Over.pullback f).map b'
    let un := (Over.mapPullbackAdj f).unit.app T.unop
    have hmap :
        (Over.pullback f).map (a' * b') = pa * pb := by
      rw [Functor.map_mul]
      rfl
    have hcomp :
        un ≫ (pa * pb) = (un ≫ pa) * (un ≫ pb) := by
      rw [Hom.mul_def, Hom.mul_def]
      exact comp_lift_assoc un pa pb
        μ[(Over.pullback f).obj G.X]
    change
      un ≫ (Over.pullback f).map (a' * b') =
        (un ≫ pa) * (un ≫ pb)
    rw [hmap, hcomp]
  · intro T T' h
    ext k
    exact (Over.mapPullbackAdj f).homEquiv_naturality_left
      h.unop k

/-- The group object represented by a Hopf algebra. -/
abbrev affineGroupSchemeGroup
    (R A : Type u) [CommRing R] [CommRing A] [HopfAlgebra R A] :=
  (_root_.AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
    (Opposite.op (CommHopfAlgCat.of R A))

/-- The categorical pullback of the group object represented by `A`. -/
abbrev affineGroupSchemePullbackGroup
    (R S A : Type u)
    [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [HopfAlgebra R A] :=
  (Over.pullback (scalarExtensionSpecMap R S)).mapGrp.obj
    (affineGroupSchemeGroup R A)

/-- The group object represented by the tensor-product base change. -/
abbrev affineGroupScalarExtensionGroup
    (R S A : Type u)
    [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [HopfAlgebra R A] :=
  (_root_.AlgebraicGeometry.hopfSpec (CommRingCat.of S)).obj
    (Opposite.op (CommHopfAlgCat.of S (TensorProduct R S A)))

/-- The scheme-level pullback/tensor-product comparison over `Spec S`. -/
def affineGroupBaseChangeOverIso
    (R S A : Type u)
    [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [HopfAlgebra R A] :
    (Over.pullback (scalarExtensionSpecMap R S)).obj
      ((_root_.AlgebraicGeometry.Spec (CommRingCat.of A)).asOver
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of R))) ≅
    (_root_.AlgebraicGeometry.Spec
      (CommRingCat.of (TensorProduct R S A))).asOver
      (_root_.AlgebraicGeometry.Spec (CommRingCat.of S)) := by
  let q :=
    pullbackSymmetry
      (_root_.AlgebraicGeometry.Spec (CommRingCat.of A) ↘
        _root_.AlgebraicGeometry.Spec (CommRingCat.of R))
      (_root_.AlgebraicGeometry.Spec (CommRingCat.of S) ↘
        _root_.AlgebraicGeometry.Spec (CommRingCat.of R)) ≪≫
      _root_.AlgebraicGeometry.pullbackSpecIso' R S A
  exact
    { hom := q.hom.asOver
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of S))
      inv := q.inv.asOver
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of S))
      hom_inv_id := by ext; exact q.hom_inv_id
      inv_hom_id := by ext; exact q.inv_hom_id }

/-- The pullback/tensor-product comparison as an isomorphism of group objects. -/
def affineGroupBaseChangeGroupIso
    (R S A : Type u)
    [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [HopfAlgebra R A] :
    affineGroupSchemePullbackGroup R S A ≅
      affineGroupScalarExtensionGroup R S A := by
  letI : GrpObj
      ((Over.pullback (scalarExtensionSpecMap R S)).obj
        ((_root_.AlgebraicGeometry.Spec (CommRingCat.of A)).asOver
          (_root_.AlgebraicGeometry.Spec (CommRingCat.of R)))) :=
    (affineGroupSchemePullbackGroup R S A).grp
  let e := affineGroupBaseChangeOverIso R S A
  haveI : IsMonHom e.hom := by
    change IsMonHom
      ((pullbackSymmetry
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of A) ↘
          _root_.AlgebraicGeometry.Spec (CommRingCat.of R))
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of S) ↘
          _root_.AlgebraicGeometry.Spec (CommRingCat.of R)) ≪≫
        _root_.AlgebraicGeometry.pullbackSpecIso' R S A).hom.asOver
          (_root_.AlgebraicGeometry.Spec (CommRingCat.of S)))
    infer_instance
  exact Grp.mkIso' e

/-- Scalar extension as a natural isomorphism of represented group presheaves. -/
def affineGroupPresheafBaseChangeIso
    (R S A : Type u)
    [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [HopfAlgebra R A] :
    (Over.map (scalarExtensionSpecMap R S)).op ⋙
        affineGroupPresheaf (CommRingCat.of R) (CommRingCat.of A) ≅
      affineGroupPresheaf (CommRingCat.of S)
        (CommRingCat.of (TensorProduct R S A)) := by
  change
    (Over.map (scalarExtensionSpecMap R S)).op ⋙
        yonedaGrp.obj (affineGroupSchemeGroup R A) ≅
      yonedaGrp.obj (affineGroupScalarExtensionGroup R S A)
  exact
    overMapYonedaGrpIso (scalarExtensionSpecMap R S)
        (affineGroupSchemeGroup R A) ≪≫
      yonedaGrp.mapIso (affineGroupBaseChangeGroupIso R S A)

/-- Forward coefficient comparison used to transport Čech cocycles. -/
def affineGroupPresheafBaseChange
    (R S A : Type u)
    [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [HopfAlgebra R A] :
    (Over.map (scalarExtensionSpecMap R S)).op ⋙
        affineGroupPresheaf (CommRingCat.of R) (CommRingCat.of A) ⟶
      affineGroupPresheaf (CommRingCat.of S)
        (CommRingCat.of (TensorProduct R S A)) :=
  (affineGroupPresheafBaseChangeIso R S A).hom

/-- All geometric data needed to change base on fixed-cover fpqc Čech H¹. -/
def fpqcH1ScalarExtensionGeometricData
    (R S A : Type u)
    [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [HopfAlgebra R A] :
    FpqcH1GeometricChangeOfBaseData.{u, v}
      (CommRingCat.of R) (CommRingCat.of A)
      (CommRingCat.of S) (CommRingCat.of (TensorProduct R S A)) where
  restrict := Over.map (scalarExtensionSpecMap R S)
  coefficient := affineGroupPresheafBaseChange R S A
  mapCover U := U.baseChangeAlong (scalarExtensionSpecMap R S)
  coverProjection U := U.baseChangeProjection (scalarExtensionSpecMap R S)
  mapRefinementHom r j :=
    (Over.pullback (scalarExtensionSpecMap R S)).map (r.hom j)
  mapRefinementHom_projection r j :=
    r.baseChangeProjection_naturality (scalarExtensionSpecMap R S) j

/-- Canonical scalar extension on fixed-cover fpqc Čech H¹. -/
def FpqcCechH1.scalarExtension
    (R S A : Type u)
    [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [HopfAlgebra R A]
    {I : Type v} (U : FpqcCover (CommRingCat.of R) I) :
    FpqcCechH1 (CommRingCat.of R) (CommRingCat.of A) U →
      FpqcCechH1 (CommRingCat.of S)
        (CommRingCat.of (TensorProduct R S A))
        (U.baseChangeAlong (scalarExtensionSpecMap R S)) :=
  (fpqcH1ScalarExtensionGeometricData R S A).mapH1 U

/-- Fixed-cover scalar extension preserves the neutral class. -/
@[simp] theorem FpqcCechH1.scalarExtension_neutral
    (R S A : Type u)
    [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [HopfAlgebra R A]
    {I : Type v} (U : FpqcCover (CommRingCat.of R) I) :
    FpqcCechH1.scalarExtension R S A U
        (FpqcCechH1.neutral (CommRingCat.of R) (CommRingCat.of A) U) =
      FpqcCechH1.neutral (CommRingCat.of S)
        (CommRingCat.of (TensorProduct R S A))
        (U.baseChangeAlong (scalarExtensionSpecMap R S)) :=
  (fpqcH1ScalarExtensionGeometricData R S A).mapH1_neutral U

/-- Quotient-level change-of-base data produced by the geometric construction. -/
def fpqcH1ScalarExtensionChangeOfBaseData
    (R S A : Type u)
    [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [HopfAlgebra R A] :
    FpqcH1ChangeOfBaseData.{u, v}
      (CommRingCat.of R) (CommRingCat.of A)
      (CommRingCat.of S) (CommRingCat.of (TensorProduct R S A)) :=
  (fpqcH1ScalarExtensionGeometricData R S A).toChangeOfBaseData

/-- Canonical scalar extension on global fpqc Čech H¹. -/
def FpqcH1.scalarExtension
    (R S A : Type u)
    [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [HopfAlgebra R A] :
    FpqcH1.{u, v} (CommRingCat.of R) (CommRingCat.of A) →
      FpqcH1.{u, v} (CommRingCat.of S)
        (CommRingCat.of (TensorProduct R S A)) :=
  (fpqcH1ScalarExtensionChangeOfBaseData R S A).toFun

/-- Scalar extension sends a represented class to its base-changed cover
and its explicitly transported fixed-cover class. -/
@[simp] theorem FpqcH1.scalarExtension_classOf
    (R S A : Type u)
    [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [HopfAlgebra R A]
    {I : Type v} (U : FpqcCover (CommRingCat.of R) I)
    (ξ : FpqcCechH1 (CommRingCat.of R) (CommRingCat.of A) U) :
    FpqcH1.scalarExtension R S A
        (FpqcH1.classOf (CommRingCat.of R) (CommRingCat.of A) U ξ) =
      FpqcH1.classOf (CommRingCat.of S)
        (CommRingCat.of (TensorProduct R S A))
        (U.baseChangeAlong (scalarExtensionSpecMap R S))
        (FpqcCechH1.scalarExtension R S A U ξ) :=
  rfl

/-- Global scalar extension preserves the distinguished neutral class. -/
@[simp] theorem FpqcH1.scalarExtension_neutral
    (R S A : Type u)
    [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [HopfAlgebra R A] :
    FpqcH1.scalarExtension R S A
        (FpqcH1.neutral (CommRingCat.of R) (CommRingCat.of A) :
          FpqcH1.{u, v} (CommRingCat.of R) (CommRingCat.of A)) =
      FpqcH1.neutral (CommRingCat.of S)
        (CommRingCat.of (TensorProduct R S A)) :=
  (fpqcH1ScalarExtensionChangeOfBaseData R S A).toFun_neutral

/-- The canonical map filling the finite scalar-extension interface. -/
def FpqcH1ScalarExtensionMap.canonical
    {K A : Type u} [Field K] [CommRing A] [HopfAlgebra K A]
    (E : FiniteFieldExtension K) :
    FpqcH1ScalarExtensionMap K A E where
  toFun := FpqcH1.scalarExtension K E.Extension A
  map_neutral := FpqcH1.scalarExtension_neutral K E.Extension A

/-- Build a concrete restriction system from any family of finite extensions. -/
def FpqcH1RestrictionSystem.ofExtensions
    {K A : Type u} [Field K] [CommRing A] [HopfAlgebra K A]
    {J : Type (u + 1)}
    (extension : J → FiniteFieldExtension K) :
    FpqcH1RestrictionSystem K A where
  Index := J
  extension := extension
  map i := FpqcH1ScalarExtensionMap.canonical (extension i)

/-- The canonical restriction system indexed by all bundled finite extensions. -/
def FpqcH1RestrictionSystem.all
    (K A : Type u) [Field K] [CommRing A] [HopfAlgebra K A] :
    FpqcH1RestrictionSystem K A :=
  FpqcH1RestrictionSystem.ofExtensions
    (fun E : FiniteFieldExtension K => E)

end

end RiemannResearch.AlgebraicGeometry
