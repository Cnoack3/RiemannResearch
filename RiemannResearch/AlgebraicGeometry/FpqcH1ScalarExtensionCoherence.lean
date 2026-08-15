/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.AlgebraicGeometry.AffineGroupScalarExtensionCoherence

/-!
# Coherence for canonical scalar extension on fpqc H¹

This module assembles generic map/pullback coherence and affine
tensor-coordinate comparisons into canonical cover refinements, fixed-cover
Čech identities, and global normalized scalar-extension laws.

The imported comparison modules identify the chosen pullback adjunction with
`pullbackSpecIso'` and the tensor-unit/associativity coordinates. The
common-refinement quotient then transports the fixed-cover identities to
global fpqc H¹.
-/

namespace RiemannResearch.AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits CategoryTheory.Over
open scoped TensorProduct

universe u v w

noncomputable section

/-! ## Coefficient change on global H¹ -/

/-- Change coefficients without changing the base or the chosen cover. -/
def fpqcH1CoefficientChangeOfBaseData
    {R A B : CommRingCat.{u}}
    [HopfAlgebra R A] [HopfAlgebra R B]
    (η : affineGroupPresheaf R A ⟶ affineGroupPresheaf R B) :
    FpqcH1ChangeOfBaseData.{u, v} R A R B where
  mapCover U := U
  mapRefinement r := r
  mapH1 _ ξ := PresheafH1.map η ξ
  mapH1_pullback r ξ := r.map_pullbackH1 η ξ
  mapH1_neutral U := PresheafH1.map_one (U := U.obj) η

/-- A morphism of coefficient presheaves induces a map on global fpqc H¹. -/
def FpqcH1.mapCoefficients
    {R A B : CommRingCat.{u}}
    [HopfAlgebra R A] [HopfAlgebra R B]
    (η : affineGroupPresheaf R A ⟶ affineGroupPresheaf R B) :
    FpqcH1.{u, v} R A → FpqcH1.{u, v} R B :=
  (fpqcH1CoefficientChangeOfBaseData η :
    FpqcH1ChangeOfBaseData.{u, v} R A R B).toFun

@[simp] theorem FpqcH1.mapCoefficients_classOf
    {R A B : CommRingCat.{u}}
    [HopfAlgebra R A] [HopfAlgebra R B]
    (η : affineGroupPresheaf R A ⟶ affineGroupPresheaf R B)
    {I : Type v} (U : FpqcCover R I)
    (ξ : FpqcCechH1 R A U) :
    FpqcH1.mapCoefficients η (FpqcH1.classOf R A U ξ) =
      FpqcH1.classOf R B U (PresheafH1.map η ξ) :=
  rfl

@[simp] theorem FpqcH1.mapCoefficients_neutral
    {R A B : CommRingCat.{u}}
    [HopfAlgebra R A] [HopfAlgebra R B]
    (η : affineGroupPresheaf R A ⟶ affineGroupPresheaf R B) :
    FpqcH1.mapCoefficients.{u, v} η (FpqcH1.neutral R A) =
      FpqcH1.neutral R B :=
  (fpqcH1CoefficientChangeOfBaseData η :
    FpqcH1ChangeOfBaseData.{u, v} R A R B).toFun_neutral

@[simp] theorem FpqcH1.mapCoefficients_id
    {R A : CommRingCat.{u}} [HopfAlgebra R A] :
    FpqcH1.mapCoefficients.{u, v}
      (𝟙 (affineGroupPresheaf R A)) = id := by
  funext x
  refine Quotient.inductionOn x ?_
  intro a
  change FpqcH1.classOf R A a.cover
      (PresheafH1.map (𝟙 (affineGroupPresheaf R A)) a.value) =
    FpqcH1.classOf R A a.cover a.value
  rw [PresheafH1.map_id]
  rfl

theorem FpqcH1.mapCoefficients_comp
    {R A B C : CommRingCat.{u}}
    [HopfAlgebra R A] [HopfAlgebra R B] [HopfAlgebra R C]
    (η : affineGroupPresheaf R A ⟶ affineGroupPresheaf R B)
    (θ : affineGroupPresheaf R B ⟶ affineGroupPresheaf R C) :
    FpqcH1.mapCoefficients.{u, v} (η ≫ θ) =
      FpqcH1.mapCoefficients θ ∘ FpqcH1.mapCoefficients η := by
  funext x
  refine Quotient.inductionOn x ?_
  intro a
  change FpqcH1.classOf R C a.cover
      (PresheafH1.map (η ≫ θ) a.value) =
    FpqcH1.classOf R C a.cover
      (PresheafH1.map θ (PresheafH1.map η a.value))
  rw [PresheafH1.map_comp]
  rfl

/-! ## Iterated scalar extension and cover coherence -/

/-- The change-of-base datum for two successive scalar extensions. -/
def fpqcH1IteratedScalarExtensionChangeOfBaseData
    (R S T A : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra S T] [HopfAlgebra R A] :
    FpqcH1ChangeOfBaseData.{u, v}
      (CommRingCat.of R) (CommRingCat.of A)
      (CommRingCat.of T)
      (CommRingCat.of
        (TensorProduct S T (TensorProduct R S A))) :=
  (fpqcH1ScalarExtensionChangeOfBaseData
      S T (TensorProduct R S A)).comp
    (fpqcH1ScalarExtensionChangeOfBaseData R S A)

@[simp] theorem fpqcH1IteratedScalarExtension_mapCover
    (R S T A : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra S T] [HopfAlgebra R A]
    {I : Type v} (U : FpqcCover (CommRingCat.of R) I) :
    (fpqcH1IteratedScalarExtensionChangeOfBaseData
      R S T A).mapCover U =
      (U.baseChangeAlong (scalarExtensionSpecMap R S)).baseChangeAlong
        (scalarExtensionSpecMap S T) :=
  rfl

@[simp] theorem fpqcH1IteratedScalarExtension_mapH1
    (R S T A : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra S T] [HopfAlgebra R A]
    {I : Type v} (U : FpqcCover (CommRingCat.of R) I)
    (ξ : FpqcCechH1 (CommRingCat.of R) (CommRingCat.of A) U) :
    (fpqcH1IteratedScalarExtensionChangeOfBaseData
      R S T A).mapH1 U ξ =
      FpqcCechH1.scalarExtension S T (TensorProduct R S A)
        (U.baseChangeAlong (scalarExtensionSpecMap R S))
        (FpqcCechH1.scalarExtension R S A U ξ) :=
  rfl

@[simp] theorem fpqcH1IteratedScalarExtension_toFun
    (R S T A : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra S T] [HopfAlgebra R A] :
    (fpqcH1IteratedScalarExtensionChangeOfBaseData R S T A :
      FpqcH1ChangeOfBaseData.{u, v}
        (CommRingCat.of R) (CommRingCat.of A)
        (CommRingCat.of T)
        (CommRingCat.of
          (TensorProduct S T (TensorProduct R S A)))).toFun =
      FpqcH1.scalarExtension S T (TensorProduct R S A) ∘
        FpqcH1.scalarExtension R S A := by
  exact FpqcH1ChangeOfBaseData.comp_toFun_eq
    (fpqcH1ScalarExtensionChangeOfBaseData
      S T (TensorProduct R S A))
    (fpqcH1ScalarExtensionChangeOfBaseData R S A)
/-- The self-base-change cover is objectwise isomorphic to the original. -/
def FpqcCover.scalarExtensionSelfObjIso
    (R : Type u) [CommRing R]
    {I : Type v} (U : FpqcCover (CommRingCat.of R) I) (i : I) :
    (U.baseChangeAlong (scalarExtensionSpecMap R R)).obj i ≅ U.obj i := by
  exact (overPullbackIdIsoOfEq (scalarExtensionSpecMap R R)
    (scalarExtensionSpecMap_self R)).app (U.obj i)

/-- The self-base-change cover refines the original cover. -/
def FpqcCover.scalarExtensionSelfRefinement
    (R : Type u) [CommRing R]
    {I : Type v} (U : FpqcCover (CommRingCat.of R) I) :
    (U.baseChangeAlong (scalarExtensionSpecMap R R)).Refinement U where
  index := id
  hom i := (U.scalarExtensionSelfObjIso R i).hom

/-- Identity-base-change cover arguments agree with the canonical refinement
after the map/pullback adjunction comparison. -/
theorem FpqcCover.scalarExtensionSelf_argument
    (R : Type u) [CommRing R]
    {I : Type v} (U : FpqcCover (CommRingCat.of R) I) (i : I)
    (T : Over (_root_.AlgebraicGeometry.Spec (CommRingCat.of R)))
    (a : T ⟶ (U.baseChangeAlong (scalarExtensionSpecMap R R)).obj i) :
    (overMapIdIsoOfEq (scalarExtensionSpecMap R R)
        (scalarExtensionSpecMap_self R)).inv.app T ≫
      (Over.map (scalarExtensionSpecMap R R)).map a ≫
      U.baseChangeProjection (scalarExtensionSpecMap R R) i =
    a ≫ (U.scalarExtensionSelfRefinement R).hom i := by
  exact
    overMapIdIsoOfEq_inv_app_comp_map_comp_counit
      (scalarExtensionSpecMap R R) (scalarExtensionSpecMap_self R)
      T (U.obj i) a

/-- Objectwise comparison between twice-pulled and directly pulled covers. -/
def FpqcCover.baseChangeAlongCompObjIso
    {R S T : CommRingCat.{u}}
    (f : _root_.AlgebraicGeometry.Spec S ⟶
      _root_.AlgebraicGeometry.Spec R)
    (g : _root_.AlgebraicGeometry.Spec T ⟶
      _root_.AlgebraicGeometry.Spec S)
    {I : Type v} (U : FpqcCover R I) (i : I) :
    ((U.baseChangeAlong f).baseChangeAlong g).obj i ≅
      (U.baseChangeAlong (g ≫ f)).obj i :=
  (Over.pullbackComp g f).symm.app (U.obj i)

theorem FpqcCover.Refinement.baseChangeAlongCompObjIso_naturality
    {R S T : CommRingCat.{u}}
    (f : _root_.AlgebraicGeometry.Spec S ⟶
      _root_.AlgebraicGeometry.Spec R)
    (g : _root_.AlgebraicGeometry.Spec T ⟶
      _root_.AlgebraicGeometry.Spec S)
    {I : Type v} {J : Type w}
    {U : FpqcCover R I} {V : FpqcCover R J}
    (r : V.Refinement U) (j : J) :
    (Over.pullback g).map ((Over.pullback f).map (r.hom j)) ≫
        (U.baseChangeAlongCompObjIso f g (r.index j)).hom =
      (V.baseChangeAlongCompObjIso f g j).hom ≫
        (Over.pullback (g ≫ f)).map (r.hom j) :=
  (Over.pullbackComp g f).symm.hom.naturality (r.hom j)

/-- The twice scalar-extended cover is objectwise isomorphic to the directly
scalar-extended cover. -/
def FpqcCover.scalarExtensionCompObjIso
    (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T]
    {I : Type v} (U : FpqcCover (CommRingCat.of R) I) (i : I) :
    ((U.baseChangeAlong (scalarExtensionSpecMap R S)).baseChangeAlong
        (scalarExtensionSpecMap S T)).obj i ≅
      (U.baseChangeAlong (scalarExtensionSpecMap R T)).obj i := by
  exact (overPullbackCompIsoOfEq (scalarExtensionSpecMap S T)
    (scalarExtensionSpecMap R S) (scalarExtensionSpecMap R T)
    (scalarExtensionSpecMap_comp R S T)).symm.app (U.obj i)

/-- The twice scalar-extended cover refines the directly scalar-extended
cover through the pullback-composition isomorphism. -/
def FpqcCover.scalarExtensionCompRefinement
    (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T]
    {I : Type v} (U : FpqcCover (CommRingCat.of R) I) :
    ((U.baseChangeAlong (scalarExtensionSpecMap R S)).baseChangeAlong
        (scalarExtensionSpecMap S T)).Refinement
      (U.baseChangeAlong (scalarExtensionSpecMap R T)) where
  index := id
  hom i := (U.scalarExtensionCompObjIso R S T i).hom

/-- Iterated scalar-extension cover arguments agree with direct scalar
extension after the canonical cover refinement. -/
theorem FpqcCover.scalarExtensionComp_argument
    (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T]
    {I : Type v} (U : FpqcCover (CommRingCat.of R) I) (i : I)
    (V : Over (_root_.AlgebraicGeometry.Spec (CommRingCat.of T)))
    (a : V ⟶
      ((U.baseChangeAlong (scalarExtensionSpecMap R S)).baseChangeAlong
        (scalarExtensionSpecMap S T)).obj i) :
    (overMapCompIsoOfEq (scalarExtensionSpecMap S T)
        (scalarExtensionSpecMap R S) (scalarExtensionSpecMap R T)
        (scalarExtensionSpecMap_comp R S T)).hom.app V ≫
      (Over.map (scalarExtensionSpecMap S T) ⋙
        Over.map (scalarExtensionSpecMap R S)).map a ≫
      (Over.map (scalarExtensionSpecMap R S)).map
        ((U.baseChangeAlong
          (scalarExtensionSpecMap R S)).baseChangeProjection
            (scalarExtensionSpecMap S T) i) ≫
      U.baseChangeProjection (scalarExtensionSpecMap R S) i =
    (Over.map (scalarExtensionSpecMap R T)).map
        (a ≫ (U.scalarExtensionCompRefinement R S T).hom i) ≫
      U.baseChangeProjection (scalarExtensionSpecMap R T) i := by
  exact
    overMapCompIsoOfEq_hom_app_comp_map_comp_counit
      (scalarExtensionSpecMap S T) (scalarExtensionSpecMap R S)
      (scalarExtensionSpecMap R T) (scalarExtensionSpecMap_comp R S T)
      V (U.obj i) a

/-- The tensor-unit isomorphism on represented affine group presheaves. -/
def affineGroupPresheafScalarExtensionSelfIso
    (R A : Type u)
    [CommRing R] [CommRing A] [HopfAlgebra R A] :
    affineGroupPresheaf (CommRingCat.of R)
        (CommRingCat.of (TensorProduct R R A)) ≅
      affineGroupPresheaf (CommRingCat.of R) (CommRingCat.of A) :=
  yonedaGrp.mapIso (affineGroupScalarExtensionSelfGroupIso R A)

/-- The normalized self-scalar-extension comparison on a represented
section is precomposition by the canonical map-to-identity comparison. -/
theorem affineGroupPresheafScalarExtensionSelfIso_hom_app
    (R A : Type u)
    [CommRing R] [CommRing A] [HopfAlgebra R A]
    (T : Over (_root_.AlgebraicGeometry.Spec (CommRingCat.of R)))
    (g : (Over.map (scalarExtensionSpecMap R R)).obj T ⟶
      (affineGroupSchemeGroup R A).X) :
    ((affineGroupPresheafScalarExtensionSelfIso R A).hom.app
        (Opposite.op T)).hom
      (((affineGroupPresheafBaseChange R R A).app
        (Opposite.op T)).hom g) =
      (overMapIdIsoOfEq (scalarExtensionSpecMap R R)
        (scalarExtensionSpecMap_self R)).inv.app T ≫ g := by
  change
    ((Over.mapPullbackAdj (scalarExtensionSpecMap R R)).unit.app T ≫
      (Over.pullback (scalarExtensionSpecMap R R)).map g) ≫
      (affineGroupBaseChangeGroupIso R R A ≪≫
        affineGroupScalarExtensionSelfGroupIso R A).hom.hom.hom = _
  rw [affineGroupScalarExtensionSelfGroupIso_hom, Category.assoc]
  exact
    overPullbackIdIsoOfEq_unit_naturality
      (scalarExtensionSpecMap R R) (scalarExtensionSpecMap_self R)
      T (affineGroupSchemeGroup R A).X g

/-- Presheaf-valued form of the normalized represented-section comparison. -/
theorem affineGroupPresheafScalarExtensionSelfIso_hom_apply
    (R A : Type u)
    [CommRing R] [CommRing A] [HopfAlgebra R A]
    (T : Over (_root_.AlgebraicGeometry.Spec (CommRingCat.of R)))
    (g : ((Over.map (scalarExtensionSpecMap R R)).op ⋙
      affineGroupPresheaf (CommRingCat.of R) (CommRingCat.of A)).obj
        (Opposite.op T)) :
    ((affineGroupPresheafScalarExtensionSelfIso R A).hom.app
        (Opposite.op T)).hom
      (((affineGroupPresheafBaseChange R R A).app
        (Opposite.op T)).hom g) =
      ((affineGroupPresheaf (CommRingCat.of R)
        (CommRingCat.of A)).map
          ((overMapIdIsoOfEq (scalarExtensionSpecMap R R)
            (scalarExtensionSpecMap_self R)).inv.app T).op).hom g := by
  change
    ((affineGroupPresheafScalarExtensionSelfIso R A).hom.app
        (Opposite.op T)).hom
      (((affineGroupPresheafBaseChange R R A).app
        (Opposite.op T)).hom g) =
      (overMapIdIsoOfEq (scalarExtensionSpecMap R R)
        (scalarExtensionSpecMap_self R)).inv.app T ≫ g
  exact affineGroupPresheafScalarExtensionSelfIso_hom_app R A T g

/-- Scalar extension along the identity base ring, followed by the tensor-unit
coefficient comparison, is pullback along the canonical cover refinement. -/
theorem FpqcCechH1.scalarExtension_self
    (R A : Type u)
    [CommRing R] [CommRing A] [HopfAlgebra R A]
    {I : Type v} (U : FpqcCover (CommRingCat.of R) I)
    (ξ : FpqcCechH1 (CommRingCat.of R) (CommRingCat.of A) U) :
    PresheafH1.map
        (affineGroupPresheafScalarExtensionSelfIso R A).hom
        (FpqcCechH1.scalarExtension R R A U ξ) =
      (U.scalarExtensionSelfRefinement R).pullbackH1 ξ := by
  refine Quot.inductionOn ξ ?_
  intro γ
  apply congrArg PresheafOfGroups.OneCocycle.class
  apply PresheafH1.cocycle_ext
  apply PresheafOfGroups.OneCochain.ext
  funext i j T a b
  dsimp [PresheafH1.mapOneCocycle, PresheafH1.mapOneCochain,
    PresheafH1.changeBaseOneCocycle, PresheafH1.changeBaseOneCochain,
    FpqcCover.Refinement.pullbackOneCocycle,
    FpqcCover.Refinement.pullbackOneCochain,
    fpqcH1ScalarExtensionGeometricData]
  rw [affineGroupPresheafScalarExtensionSelfIso_hom_apply]
  rw [γ.ev_precomp]
  rw [U.scalarExtensionSelf_argument R i T a,
    U.scalarExtensionSelf_argument R j T b]
  rfl

/-- Tensor associativity on represented affine group presheaves. -/
def affineGroupPresheafScalarExtensionCompIso
    (R S T A : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [HopfAlgebra R A] :
    affineGroupPresheaf (CommRingCat.of T)
        (CommRingCat.of
          (TensorProduct S T (TensorProduct R S A))) ≅
      affineGroupPresheaf (CommRingCat.of T)
        (CommRingCat.of (TensorProduct R T A)) :=
  yonedaGrp.mapIso
    (affineGroupScalarExtensionCompGroupIso R S T A)

/-- Two successive mates for map/pullback adjunctions agree with the direct
mate after the canonical map- and pullback-composition comparisons. -/
theorem overMapPullbackAdj_homEquiv_comp
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (e : f ≫ g = h) (V : Over X) (G : Over Z)
    (x : (Over.map f ⋙ Over.map g).obj V ⟶ G) :
    (Over.mapPullbackAdj f).homEquiv V ((Over.pullback g).obj G)
        ((Over.mapPullbackAdj g).homEquiv ((Over.map f).obj V) G x) ≫
      (overPullbackCompIsoOfEq f g h e).inv.app G =
    (Over.mapPullbackAdj h).homEquiv V G
      ((overMapCompIsoOfEq f g h e).hom.app V ≫ x) := by
  subst h
  rw [show
    (Over.mapPullbackAdj f).homEquiv V ((Over.pullback g).obj G)
        ((Over.mapPullbackAdj g).homEquiv ((Over.map f).obj V) G x) =
      ((Over.mapPullbackAdj f).comp
        (Over.mapPullbackAdj g)).homEquiv V G x by
      simp only [Adjunction.homEquiv_unit, Adjunction.comp_unit,
        NatTrans.comp_app, Functor.comp_obj, Category.assoc]
      simp]
  apply ((Over.mapPullbackAdj (f ≫ g)).homEquiv V G).symm.injective
  rw [Equiv.symm_apply_apply]
  rw [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  change
    (Over.map (f ≫ g)).map
        (((Over.mapPullbackAdj f).comp
          (Over.mapPullbackAdj g)).homEquiv V G x) ≫
      (Over.map (f ≫ g)).map
          ((conjugateEquiv
            ((Over.mapPullbackAdj f).comp (Over.mapPullbackAdj g))
            (Over.mapPullbackAdj (f ≫ g))
            (Over.mapComp f g).hom).app G) ≫
        (Over.mapPullbackAdj (f ≫ g)).counit.app G =
      (Over.mapComp f g).hom.app V ≫ x
  rw [conjugateEquiv_counit
    ((Over.mapPullbackAdj f).comp (Over.mapPullbackAdj g))
    (Over.mapPullbackAdj (f ≫ g)) (Over.mapComp f g).hom G]
  rw [← Category.assoc, (Over.mapComp f g).hom.naturality]
  rw [Category.assoc]
  change
    (Over.mapComp f g).hom.app V ≫
      ((((Over.mapPullbackAdj f).comp
        (Over.mapPullbackAdj g)).homEquiv V G).symm
          (((Over.mapPullbackAdj f).comp
            (Over.mapPullbackAdj g)).homEquiv V G x)) = _
  rw [Equiv.symm_apply_apply]

/-- Presheaf-valued form of normalized associativity for represented affine
group sections. -/
theorem affineGroupPresheafScalarExtensionCompIso_hom_apply
    (R S T A : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [HopfAlgebra R A]
    (V : Over (_root_.AlgebraicGeometry.Spec (CommRingCat.of T)))
    (x : (Over.map (scalarExtensionSpecMap S T) ⋙
      Over.map (scalarExtensionSpecMap R S)).obj V ⟶
        (affineGroupSchemeGroup R A).X) :
    ((affineGroupPresheafScalarExtensionCompIso R S T A).hom.app
      (Opposite.op V)).hom
      (((affineGroupPresheafBaseChange S T
        (TensorProduct R S A)).app (Opposite.op V)).hom
        (((affineGroupPresheafBaseChange R S A).app
          (Opposite.op ((Over.map
            (scalarExtensionSpecMap S T)).obj V))).hom x)) =
    ((affineGroupPresheafBaseChange R T A).app
      (Opposite.op V)).hom
      ((overMapCompIsoOfEq (scalarExtensionSpecMap S T)
        (scalarExtensionSpecMap R S) (scalarExtensionSpecMap R T)
        (scalarExtensionSpecMap_comp R S T)).hom.app V ≫ x) := by
  change
    ((Over.mapPullbackAdj (scalarExtensionSpecMap S T)).homEquiv V
      (affineGroupScalarExtensionGroup R S A).X
      ((Over.mapPullbackAdj (scalarExtensionSpecMap R S)).homEquiv
        ((Over.map (scalarExtensionSpecMap S T)).obj V)
        (affineGroupSchemeGroup R A).X x ≫
        (affineGroupBaseChangeGroupIso R S A).hom.hom.hom)) ≫
      (affineGroupBaseChangeGroupIso S T
        (TensorProduct R S A)).hom.hom.hom ≫
      (affineGroupScalarExtensionCompGroupIso R S T A).hom.hom.hom =
    (Over.mapPullbackAdj (scalarExtensionSpecMap R T)).homEquiv V
      (affineGroupSchemeGroup R A).X
      ((overMapCompIsoOfEq (scalarExtensionSpecMap S T)
        (scalarExtensionSpecMap R S) (scalarExtensionSpecMap R T)
        (scalarExtensionSpecMap_comp R S T)).hom.app V ≫ x) ≫
      (affineGroupBaseChangeGroupIso R T A).hom.hom.hom
  let y := (Over.mapPullbackAdj
    (scalarExtensionSpecMap R S)).homEquiv
      ((Over.map (scalarExtensionSpecMap S T)).obj V)
      (affineGroupSchemeGroup R A).X x
  have hn := (Over.mapPullbackAdj
    (scalarExtensionSpecMap S T)).homEquiv_naturality_right y
      (affineGroupBaseChangeGroupIso R S A).hom.hom.hom
  rw [hn]
  simp only [Category.assoc]
  let m0 : V ⟶
      (Over.pullback (scalarExtensionSpecMap S T)).obj
        ((Over.pullback (scalarExtensionSpecMap R S)).obj
          (affineGroupSchemeGroup R A).X) :=
    (Over.mapPullbackAdj (scalarExtensionSpecMap S T)).homEquiv V
      ((Over.pullback (scalarExtensionSpecMap R S)).obj
        (affineGroupSchemeGroup R A).X) y
  let d0 : V ⟶
      (Over.pullback (scalarExtensionSpecMap R T)).obj
        (affineGroupSchemeGroup R A).X :=
    (Over.mapPullbackAdj (scalarExtensionSpecMap R T)).homEquiv V
      (affineGroupSchemeGroup R A).X
      ((overMapCompIsoOfEq (scalarExtensionSpecMap S T)
        (scalarExtensionSpecMap R S) (scalarExtensionSpecMap R T)
        (scalarExtensionSpecMap_comp R S T)).hom.app V ≫ x)
  change m0 ≫
      ((Over.pullback (scalarExtensionSpecMap S T)).map
          (affineGroupBaseChangeGroupIso R S A).hom.hom.hom ≫
        (affineGroupBaseChangeGroupIso S T
          (TensorProduct R S A)).hom.hom.hom ≫
        (affineGroupScalarExtensionCompGroupIso R S T A).hom.hom.hom) =
    d0 ≫ (affineGroupBaseChangeGroupIso R T A).hom.hom.hom
  calc
    _ = m0 ≫
        ((overPullbackCompIsoOfEq (scalarExtensionSpecMap S T)
          (scalarExtensionSpecMap R S) (scalarExtensionSpecMap R T)
          (scalarExtensionSpecMap_comp R S T)).inv.app
            (affineGroupSchemeGroup R A).X ≫
          (affineGroupBaseChangeGroupIso R T A).hom.hom.hom) :=
      congrArg (fun z => m0 ≫ z)
        (affineGroupScalarExtensionCompGroupIso_hom R S T A)
    _ = _ := by
      have hmate : m0 ≫
          (overPullbackCompIsoOfEq (scalarExtensionSpecMap S T)
            (scalarExtensionSpecMap R S) (scalarExtensionSpecMap R T)
            (scalarExtensionSpecMap_comp R S T)).inv.app
              (affineGroupSchemeGroup R A).X = d0 := by
        simpa only [m0, d0, y] using
          overMapPullbackAdj_homEquiv_comp
            (scalarExtensionSpecMap S T) (scalarExtensionSpecMap R S)
            (scalarExtensionSpecMap R T)
            (scalarExtensionSpecMap_comp R S T)
            V (affineGroupSchemeGroup R A).X x
      rw [← hmate]
      exact (Category.assoc _ _ _).symm

set_option maxHeartbeats 2000000 in
/-- Two successive fixed-cover scalar extensions, normalized by tensor
associativity, agree with direct scalar extension after the canonical cover
refinement. -/
theorem FpqcCechH1.scalarExtension_comp
    (R S T A : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [HopfAlgebra R A]
    {I : Type v} (U : FpqcCover (CommRingCat.of R) I)
    (xi : FpqcCechH1 (CommRingCat.of R) (CommRingCat.of A) U) :
    PresheafH1.map
        (affineGroupPresheafScalarExtensionCompIso R S T A).hom
        (FpqcCechH1.scalarExtension S T (TensorProduct R S A)
          (U.baseChangeAlong (scalarExtensionSpecMap R S))
          (FpqcCechH1.scalarExtension R S A U xi)) =
      (U.scalarExtensionCompRefinement R S T).pullbackH1
        (FpqcCechH1.scalarExtension R T A U xi) := by
  refine Quot.inductionOn xi ?_
  intro gamma
  apply congrArg PresheafOfGroups.OneCocycle.class
  apply PresheafH1.cocycle_ext
  apply PresheafOfGroups.OneCochain.ext
  funext i j V a b
  dsimp [PresheafH1.mapOneCocycle, PresheafH1.mapOneCochain,
    PresheafH1.changeBaseOneCocycle, PresheafH1.changeBaseOneCochain,
    FpqcCover.Refinement.pullbackOneCocycle,
    FpqcCover.Refinement.pullbackOneCochain,
    fpqcH1ScalarExtensionGeometricData]
  let phi :
      (Over.map (scalarExtensionSpecMap R T)).obj V ⟶
        (Over.map (scalarExtensionSpecMap S T) ⋙
          Over.map (scalarExtensionSpecMap R S)).obj V :=
    (overMapCompIsoOfEq (scalarExtensionSpecMap S T)
      (scalarExtensionSpecMap R S) (scalarExtensionSpecMap R T)
      (scalarExtensionSpecMap_comp R S T)).hom.app V
  let pi :
      (Over.map (scalarExtensionSpecMap S T) ⋙
        Over.map (scalarExtensionSpecMap R S)).obj V ⟶ U.obj i :=
    (Over.map (scalarExtensionSpecMap R S)).map
        ((Over.map (scalarExtensionSpecMap S T)).map a ≫
          (U.baseChangeAlong
            (scalarExtensionSpecMap R S)).baseChangeProjection
              (scalarExtensionSpecMap S T) i) ≫
      U.baseChangeProjection (scalarExtensionSpecMap R S) i
  let pj :
      (Over.map (scalarExtensionSpecMap S T) ⋙
        Over.map (scalarExtensionSpecMap R S)).obj V ⟶ U.obj j :=
    (Over.map (scalarExtensionSpecMap R S)).map
        ((Over.map (scalarExtensionSpecMap S T)).map b ≫
          (U.baseChangeAlong
            (scalarExtensionSpecMap R S)).baseChangeProjection
              (scalarExtensionSpecMap S T) j) ≫
      U.baseChangeProjection (scalarExtensionSpecMap R S) j
  let x0 :
      (Over.map (scalarExtensionSpecMap S T) ⋙
        Over.map (scalarExtensionSpecMap R S)).obj V ⟶
          (affineGroupSchemeGroup R A).X :=
    gamma.ev i j pi pj
  change
    ((affineGroupPresheafScalarExtensionCompIso R S T A).hom.app
      (Opposite.op V)).hom
      (((affineGroupPresheafBaseChange S T
        (TensorProduct R S A)).app (Opposite.op V)).hom
        (((affineGroupPresheafBaseChange R S A).app
          (Opposite.op ((Over.map
            (scalarExtensionSpecMap S T)).obj V))).hom x0)) = _
  rw [affineGroupPresheafScalarExtensionCompIso_hom_apply
    R S T A V x0]
  apply congrArg
    ((affineGroupPresheafBaseChange R T A).app
      (Opposite.op V)).hom
  change phi ≫ x0 =
    gamma.ev
      ((U.scalarExtensionCompRefinement R S T).index i)
      ((U.scalarExtensionCompRefinement R S T).index j)
      ((Over.map (scalarExtensionSpecMap R T)).map
          (a ≫ (U.scalarExtensionCompRefinement R S T).hom i) ≫
        U.baseChangeProjection (scalarExtensionSpecMap R T)
          ((U.scalarExtensionCompRefinement R S T).index i))
      ((Over.map (scalarExtensionSpecMap R T)).map
          (b ≫ (U.scalarExtensionCompRefinement R S T).hom j) ≫
        U.baseChangeProjection (scalarExtensionSpecMap R T)
          ((U.scalarExtensionCompRefinement R S T).index j))
  have hpre :
      phi ≫ x0 = gamma.ev i j (phi ≫ pi) (phi ≫ pj) := by
    dsimp only [x0]
    exact gamma.ev_precomp i j phi pi pj
  rw [hpre]
  have hi :
      phi ≫ pi =
        (Over.map (scalarExtensionSpecMap R T)).map
            (a ≫ (U.scalarExtensionCompRefinement R S T).hom i) ≫
          U.baseChangeProjection (scalarExtensionSpecMap R T) i := by
    dsimp only [phi, pi]
    rw [Functor.map_comp, ← Functor.comp_map]
    simpa only [Category.assoc] using
      U.scalarExtensionComp_argument R S T i V a
  have hj :
      phi ≫ pj =
        (Over.map (scalarExtensionSpecMap R T)).map
            (b ≫ (U.scalarExtensionCompRefinement R S T).hom j) ≫
          U.baseChangeProjection (scalarExtensionSpecMap R T) j := by
    dsimp only [phi, pj]
    rw [Functor.map_comp, ← Functor.comp_map]
    simpa only [Category.assoc] using
      U.scalarExtensionComp_argument R S T j V b
  rw [hi, hj]
  rfl

/-! ## Global normalized laws from fixed-cover coherence -/

/-- The normalized identity law on global fpqc H¹ follows from the explicit
fixed-cover compatibility square. -/
theorem FpqcH1.scalarExtension_self_of_fixedCover
    (R A : Type u)
    [CommRing R] [CommRing A] [HopfAlgebra R A]
    (h : ∀ {I : Type v}
      (U : FpqcCover (CommRingCat.of R) I)
      (ξ : FpqcCechH1 (CommRingCat.of R) (CommRingCat.of A) U),
      PresheafH1.map
          (affineGroupPresheafScalarExtensionSelfIso R A).hom
          (FpqcCechH1.scalarExtension R R A U ξ) =
        (U.scalarExtensionSelfRefinement R).pullbackH1 ξ) :
    FpqcH1.mapCoefficients.{u, v}
        (affineGroupPresheafScalarExtensionSelfIso R A).hom ∘
      FpqcH1.scalarExtension R R A = id := by
  let D :
      FpqcH1ChangeOfBaseData.{u, v}
        (CommRingCat.of R) (CommRingCat.of A)
        (CommRingCat.of R) (CommRingCat.of A) :=
    (fpqcH1CoefficientChangeOfBaseData
      (affineGroupPresheafScalarExtensionSelfIso R A).hom).comp
        (fpqcH1ScalarExtensionChangeOfBaseData R R A)
  let E :
      FpqcH1ChangeOfBaseData.{u, v}
        (CommRingCat.of R) (CommRingCat.of A)
        (CommRingCat.of R) (CommRingCat.of A) :=
    FpqcH1ChangeOfBaseData.identity
      (CommRingCat.of R) (CommRingCat.of A)
  have hDE : D.toFun = E.toFun := by
    apply FpqcH1ChangeOfBaseData.toFun_eq_of_refinement D E
      (fun U => U.scalarExtensionSelfRefinement R)
    intro I U ξ
    exact h U ξ
  calc
    _ = D.toFun :=
      (FpqcH1ChangeOfBaseData.comp_toFun_eq
        (fpqcH1CoefficientChangeOfBaseData
          (affineGroupPresheafScalarExtensionSelfIso R A).hom)
        (fpqcH1ScalarExtensionChangeOfBaseData R R A)).symm
    _ = E.toFun := hDE
    _ = id :=
      FpqcH1ChangeOfBaseData.identity_toFun_eq
        (CommRingCat.of R) (CommRingCat.of A)

/-- Normalized scalar extension along the identity base ring is the identity
on global fpqc H¹. -/
theorem FpqcH1.scalarExtension_self
    (R A : Type u)
    [CommRing R] [CommRing A] [HopfAlgebra R A] :
    FpqcH1.mapCoefficients.{u, v}
        (affineGroupPresheafScalarExtensionSelfIso R A).hom ∘
      FpqcH1.scalarExtension R R A = id :=
  FpqcH1.scalarExtension_self_of_fixedCover R A
    (fun U ξ => FpqcCechH1.scalarExtension_self R A U ξ)

/-- The normalized composition law on global fpqc H¹ follows from the
explicit fixed-cover compatibility square. -/
theorem FpqcH1.scalarExtension_comp_of_fixedCover
    (R S T A : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [HopfAlgebra R A]
    (h : ∀ {I : Type v}
      (U : FpqcCover (CommRingCat.of R) I)
      (ξ : FpqcCechH1 (CommRingCat.of R) (CommRingCat.of A) U),
      PresheafH1.map
          (affineGroupPresheafScalarExtensionCompIso R S T A).hom
          (FpqcCechH1.scalarExtension S T (TensorProduct R S A)
            (U.baseChangeAlong (scalarExtensionSpecMap R S))
            (FpqcCechH1.scalarExtension R S A U ξ)) =
        (U.scalarExtensionCompRefinement R S T).pullbackH1
          (FpqcCechH1.scalarExtension R T A U ξ)) :
    FpqcH1.mapCoefficients.{u, v}
        (affineGroupPresheafScalarExtensionCompIso R S T A).hom ∘
      FpqcH1.scalarExtension S T (TensorProduct R S A) ∘
      FpqcH1.scalarExtension R S A =
        FpqcH1.scalarExtension R T A := by
  let D :
      FpqcH1ChangeOfBaseData.{u, v}
        (CommRingCat.of R) (CommRingCat.of A)
        (CommRingCat.of T)
          (CommRingCat.of (TensorProduct R T A)) :=
    (fpqcH1CoefficientChangeOfBaseData
      (affineGroupPresheafScalarExtensionCompIso R S T A).hom).comp
        (fpqcH1IteratedScalarExtensionChangeOfBaseData R S T A)
  let E :
      FpqcH1ChangeOfBaseData.{u, v}
        (CommRingCat.of R) (CommRingCat.of A)
        (CommRingCat.of T)
          (CommRingCat.of (TensorProduct R T A)) :=
    fpqcH1ScalarExtensionChangeOfBaseData R T A
  have hDE : D.toFun = E.toFun := by
    apply FpqcH1ChangeOfBaseData.toFun_eq_of_refinement D E
      (fun U => U.scalarExtensionCompRefinement R S T)
    intro I U ξ
    exact h U ξ
  calc
    _ = (fpqcH1CoefficientChangeOfBaseData
          (affineGroupPresheafScalarExtensionCompIso R S T A).hom).toFun ∘
        (fpqcH1IteratedScalarExtensionChangeOfBaseData R S T A).toFun := by
      change
        (fpqcH1CoefficientChangeOfBaseData
            (affineGroupPresheafScalarExtensionCompIso R S T A).hom).toFun ∘
          FpqcH1.scalarExtension S T (TensorProduct R S A) ∘
          FpqcH1.scalarExtension R S A =
        _
      rw [fpqcH1IteratedScalarExtension_toFun]
    _ = D.toFun :=
      (FpqcH1ChangeOfBaseData.comp_toFun_eq
        (fpqcH1CoefficientChangeOfBaseData
          (affineGroupPresheafScalarExtensionCompIso R S T A).hom)
        (fpqcH1IteratedScalarExtensionChangeOfBaseData R S T A)).symm
    _ = E.toFun := hDE
    _ = FpqcH1.scalarExtension R T A :=
      rfl

/-- Normalized associativity of scalar extension on global fpqc H¹. -/
theorem FpqcH1.scalarExtension_comp
    (R S T A : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [HopfAlgebra R A] :
    FpqcH1.mapCoefficients.{u, v}
        (affineGroupPresheafScalarExtensionCompIso R S T A).hom ∘
      FpqcH1.scalarExtension S T (TensorProduct R S A) ∘
      FpqcH1.scalarExtension R S A =
        FpqcH1.scalarExtension R T A :=
  FpqcH1.scalarExtension_comp_of_fixedCover R S T A
    (fun U xi => FpqcCechH1.scalarExtension_comp R S T A U xi)

end

end RiemannResearch.AlgebraicGeometry
