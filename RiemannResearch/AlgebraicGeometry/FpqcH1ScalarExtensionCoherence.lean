/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.AlgebraicGeometry.FpqcH1CanonicalScalarExtension
import RiemannResearch.AlgebraicGeometry.HopfFpqcH1Action

/-!
# Coherence for canonical scalar extension on fpqc H¹

This module proves the formal identity, composition, and associativity laws
for change-of-base data, identifies the tensor-coordinate unit and
associativity isomorphisms, and constructs the comparison refinements between
once-, twice-, and trivially base-changed fpqc covers.

The normalized global identity and composition laws are proved unconditionally.
Their fixed-cover proofs identify the chosen pullback adjunction with
`pullbackSpecIso'` and the tensor-unit/associativity coordinates, then the
common-refinement quotient transports those identities to global fpqc H¹.
-/

namespace RiemannResearch.AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits CategoryTheory.Over
open scoped TensorProduct

universe u v w

noncomputable section

/-- Pullback along a morphism identified with an identity. -/
def overPullbackIdIsoOfEq
    {C : Type u} [Category.{v, u} C] {X : C}
    (f : X ⟶ X) (hf : f = 𝟙 X) [HasPullbacksAlong f] :
    Over.pullback f ≅ 𝟭 (Over X) := by
  subst f
  exact Over.pullbackId

/-- Mapping along a morphism identified with an identity. -/
def overMapIdIsoOfEq
    {C : Type u} [Category.{v, u} C] {X : C}
    (f : X ⟶ X) (hf : f = 𝟙 X) :
    Over.map f ≅ 𝟭 (Over X) := by
  subst f
  exact Over.mapId X

/-- The right mate defining pullback along an identity has the expected
underlying first projection. -/
theorem overPullbackId_hom_app_left
    {C : Type u} [Category.{v, u} C] {X : C}
    [HasPullbacksAlong (𝟙 X)] (T : Over X) :
    (Over.pullbackId.hom.app T).left =
      pullback.fst T.hom (𝟙 X) := by
  rw [Over.pullbackId, conjugateIsoEquiv_apply_hom,
    conjugateEquiv_adjunction_id]
  change ((Over.mapId X).inv.app _).left ≫
      ((Over.mapPullbackAdj (𝟙 X)).counit.app T).left = _
  simp only [Over.mapId_inv_app_left, Over.mapPullbackAdj_counit_app]
  simp

/-- The transported identity-pullback comparison is still the first
projection. -/
theorem overPullbackIdIsoOfEq_hom_app_left
    {C : Type u} [Category.{v, u} C] {X : C}
    (f : X ⟶ X) (hf : f = 𝟙 X) [HasPullbacksAlong f]
    (T : Over X) :
    ((overPullbackIdIsoOfEq f hf).hom.app T).left =
      pullback.fst T.hom f := by
  subst f
  simpa [overPullbackIdIsoOfEq] using overPullbackId_hom_app_left T

/-- The identity-pullback mate sends a restricted section to
precomposition by the identity-map comparison. -/
theorem overPullbackId_unit_naturality
    {C : Type u} [Category.{v, u} C] {X : C}
    [HasPullbacksAlong (𝟙 X)]
    (T U : Over X)
    (g : (Over.map (𝟙 X)).obj T ⟶ U) :
    (Over.mapPullbackAdj (𝟙 X)).unit.app T ≫
        (Over.pullback (𝟙 X)).map g ≫
        Over.pullbackId.hom.app U =
      (Over.mapId X).inv.app T ≫ g := by
  rw [Over.pullbackId.hom.naturality g]
  have h := unit_conjugateEquiv
    (Over.mapPullbackAdj (𝟙 X)) Adjunction.id
    (Over.mapId X).inv T
  rw [← Category.assoc, show
    (Over.mapPullbackAdj (𝟙 X)).unit.app T ≫
      Over.pullbackId.hom.app ((Over.map (𝟙 X)).obj T) =
        (Over.mapId X).inv.app T by
      simpa [Over.pullbackId] using h]
  simp

/-- The preceding mate identity transported along an equality with the
identity base morphism. -/
theorem overPullbackIdIsoOfEq_unit_naturality
    {C : Type u} [Category.{v, u} C] {X : C}
    (f : X ⟶ X) (hf : f = 𝟙 X) [HasPullbacksAlong f]
    (T U : Over X) (g : (Over.map f).obj T ⟶ U) :
    (Over.mapPullbackAdj f).unit.app T ≫
        (Over.pullback f).map g ≫
        (overPullbackIdIsoOfEq f hf).hom.app U =
      (overMapIdIsoOfEq f hf).inv.app T ≫ g := by
  subst f
  simpa [overPullbackIdIsoOfEq, overMapIdIsoOfEq] using
    overPullbackId_unit_naturality T U g

/-- The cover argument obtained from the identity-base-change adjunction is
the argument obtained from the canonical pullback comparison. -/
theorem overMapIdIsoOfEq_inv_app_comp_map_comp_counit
    {C : Type u} [Category.{v, u} C] {X : C}
    (f : X ⟶ X) (hf : f = 𝟙 X) [HasPullbacksAlong f]
    (T U : Over X) (a : T ⟶ (Over.pullback f).obj U) :
    (overMapIdIsoOfEq f hf).inv.app T ≫
        (Over.map f).map a ≫
        (Over.mapPullbackAdj f).counit.app U =
      a ≫ (overPullbackIdIsoOfEq f hf).hom.app U := by
  let g := (Over.map f).map a ≫
    (Over.mapPullbackAdj f).counit.app U
  have hm := overPullbackIdIsoOfEq_unit_naturality f hf T U g
  have ha :
      (Over.mapPullbackAdj f).unit.app T ≫
          (Over.pullback f).map g = a := by
    change (Over.mapPullbackAdj f).homEquiv T U g = a
    change (Over.mapPullbackAdj f).homEquiv T U
      (((Over.mapPullbackAdj f).homEquiv T U).symm a) = a
    exact Equiv.apply_symm_apply _ a
  rw [← Category.assoc, ha] at hm
  simpa [g, Category.assoc] using hm.symm

/-- Pullback-composition coherence transported along an equality of the
composite base morphism. -/
def overPullbackCompIsoOfEq
    {C : Type u} [Category.{v, u} C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (e : f ≫ g = h)
    [HasPullbacksAlong f] [HasPullbacksAlong g] [HasPullbacksAlong h] :
    Over.pullback h ≅ Over.pullback g ⋙ Over.pullback f := by
  subst h
  exact Over.pullbackComp f g

/-- Mapping-composition coherence transported along an equality of the
composite base morphism. -/
def overMapCompIsoOfEq
    {C : Type u} [Category.{v, u} C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (e : f ≫ g = h) :
    Over.map h ≅ Over.map f ⋙ Over.map g := by
  subst h
  exact Over.mapComp f g

/-- First-projection characterization of the inverse component of
pullback-composition coherence. -/
theorem overPullbackComp_inv_app_fst
    {C : Type u} [Category.{v, u} C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasPullbacksAlong f] [HasPullbacksAlong g]
    (T : Over Z) :
    ((Over.pullbackComp f g).inv.app T).left ≫
        pullback.fst T.hom (f ≫ g) =
      pullback.fst (pullback.snd T.hom g) f ≫
        pullback.fst T.hom g := by
  have h := conjugateEquiv_counit
    ((Over.mapPullbackAdj f).comp (Over.mapPullbackAdj g))
    (Over.mapPullbackAdj (f ≫ g))
    (Over.mapComp f g).hom T
  have h' := congrArg Over.Hom.left h
  simpa [Over.pullbackComp, Adjunction.comp_counit_app] using h'

/-- First-projection characterization after transporting the composite base
morphism along an equality. -/
theorem overPullbackCompIsoOfEq_inv_app_fst
    {C : Type u} [Category.{v, u} C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (e : f ≫ g = h)
    [HasPullbacksAlong f] [HasPullbacksAlong g] [HasPullbacksAlong h]
    (T : Over Z) :
    ((overPullbackCompIsoOfEq f g h e).inv.app T).left ≫
        pullback.fst T.hom h =
      pullback.fst (pullback.snd T.hom g) f ≫
        pullback.fst T.hom g := by
  subst h
  simpa [overPullbackCompIsoOfEq] using
    overPullbackComp_inv_app_fst f g T

/-- Second-projection characterization of the inverse component of
pullback-composition coherence. -/
theorem overPullbackComp_inv_app_snd
    {C : Type u} [Category.{v, u} C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasPullbacksAlong f] [HasPullbacksAlong g]
    (T : Over Z) :
    ((Over.pullbackComp f g).inv.app T).left ≫
        pullback.snd T.hom (f ≫ g) =
      pullback.snd (pullback.snd T.hom g) f := by
  simpa using Over.w ((Over.pullbackComp f g).inv.app T)

/-- The inverse component of pullback-composition coherence is the canonical
nested pullback lift. -/
theorem overPullbackComp_inv_app_left
    {C : Type u} [Category.{v, u} C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasPullbacksAlong f] [HasPullbacksAlong g]
    (T : Over Z) :
    ((Over.pullbackComp f g).inv.app T).left =
      pullback.lift
        (pullback.fst (pullback.snd T.hom g) f ≫
          pullback.fst T.hom g)
        (pullback.snd (pullback.snd T.hom g) f)
        (by
          rw [Category.assoc, pullback.condition]
          rw [← Category.assoc, pullback.condition]
          rw [Category.assoc]) := by
  apply pullback.hom_ext
  · rw [pullback.lift_fst]
    exact overPullbackComp_inv_app_fst f g T
  · rw [pullback.lift_snd]
    exact overPullbackComp_inv_app_snd f g T

@[reassoc] theorem overPullback_map_fst
    {C : Type u} [Category.{v, u} C] [HasPullbacks C]
    {X Y : C} (f : X ⟶ Y) {U V : Over Y} (a : U ⟶ V) :
    ((Over.pullback f).map a).left ≫ pullback.fst V.hom f =
      pullback.fst U.hom f ≫ a.left := by
  change pullback.lift (pullback.fst U.hom f ≫ a.left)
      (pullback.snd U.hom f) _ ≫ pullback.fst V.hom f =
    pullback.fst U.hom f ≫ a.left
  rw [pullback.lift_fst]

@[reassoc] theorem overPullback_map_snd
    {C : Type u} [Category.{v, u} C] [HasPullbacks C]
    {X Y : C} (f : X ⟶ Y) {U V : Over Y} (a : U ⟶ V) :
    ((Over.pullback f).map a).left ≫ pullback.snd V.hom f =
      pullback.snd U.hom f := by
  change pullback.lift (pullback.fst U.hom f ≫ a.left)
      (pullback.snd U.hom f) _ ≫ pullback.snd V.hom f =
    pullback.snd U.hom f
  rw [pullback.lift_snd]

theorem overPullbackCompIsoOfEq_hom_app_fst_fst
    {C : Type u} [Category.{v, u} C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (e : f ≫ g = h)
    [HasPullbacksAlong f] [HasPullbacksAlong g] [HasPullbacksAlong h]
    (U : Over Z) :
    ((overPullbackCompIsoOfEq f g h e).hom.app U).left ≫
        pullback.fst (pullback.snd U.hom g) f ≫ pullback.fst U.hom g =
      pullback.fst U.hom h := by
  rw [← overPullbackCompIsoOfEq_inv_app_fst f g h e U, ← Category.assoc]
  rw [show ((overPullbackCompIsoOfEq f g h e).hom.app U).left ≫
        ((overPullbackCompIsoOfEq f g h e).inv.app U).left = 𝟙 _ from
      congrArg Over.Hom.left
        ((overPullbackCompIsoOfEq f g h e).hom_inv_id_app U)]
  simp

theorem overPullbackCompIsoOfEq_hom_app_snd
    {C : Type u} [Category.{v, u} C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (e : f ≫ g = h)
    [HasPullbacksAlong f] [HasPullbacksAlong g] [HasPullbacksAlong h]
    (U : Over Z) :
    ((overPullbackCompIsoOfEq f g h e).hom.app U).left ≫
        pullback.snd (pullback.snd U.hom g) f =
      pullback.snd U.hom h := by
  simpa using Over.w ((overPullbackCompIsoOfEq f g h e).hom.app U)

theorem overPullbackCompIsoOfEq_hom_app_fst_snd
    {C : Type u} [Category.{v, u} C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (e : f ≫ g = h)
    [HasPullbacksAlong f] [HasPullbacksAlong g] [HasPullbacksAlong h]
    (U : Over Z) :
    ((overPullbackCompIsoOfEq f g h e).hom.app U).left ≫
        pullback.fst (pullback.snd U.hom g) f ≫ pullback.snd U.hom g =
      pullback.snd U.hom h ≫ f := by
  rw [pullback.condition, ← Category.assoc,
    overPullbackCompIsoOfEq_hom_app_snd]

/-- The unit of the composite map/pullback adjunction is compatible with
the canonical pullback-composition comparison. -/
theorem overPullbackComp_unit_naturality
    {C : Type u} [Category.{v, u} C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasPullbacksAlong f] [HasPullbacksAlong g]
    (T : Over X) (U : Over Z)
    (z : (Over.map f ⋙ Over.map g).obj T ⟶ U) :
    ((Over.mapPullbackAdj f).comp (Over.mapPullbackAdj g)).unit.app T ≫
        (Over.pullback g ⋙ Over.pullback f).map z ≫
        (Over.pullbackComp f g).inv.app U =
      (Over.mapPullbackAdj (f ≫ g)).unit.app T ≫
        (Over.pullback (f ≫ g)).map
          ((Over.mapComp f g).hom.app T ≫ z) := by
  rw [(Over.pullbackComp f g).inv.naturality z]
  rw [← Category.assoc]
  have h := unit_conjugateEquiv
    ((Over.mapPullbackAdj f).comp (Over.mapPullbackAdj g))
    (Over.mapPullbackAdj (f ≫ g))
    (Over.mapComp f g).hom T
  rw [show
    ((Over.mapPullbackAdj f).comp (Over.mapPullbackAdj g)).unit.app T ≫
        (Over.pullbackComp f g).inv.app
          ((Over.map f ⋙ Over.map g).obj T) =
      (Over.mapPullbackAdj (f ≫ g)).unit.app T ≫
        (Over.pullback (f ≫ g)).map
          ((Over.mapComp f g).hom.app T) by
      simpa [Over.pullbackComp] using h]
  simp

/-- The preceding unit identity transported along an equality of the
composite base morphism. -/
theorem overPullbackCompIsoOfEq_unit_naturality
    {C : Type u} [Category.{v, u} C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (e : f ≫ g = h)
    [HasPullbacksAlong f] [HasPullbacksAlong g] [HasPullbacksAlong h]
    (T : Over X) (U : Over Z)
    (z : (Over.map f ⋙ Over.map g).obj T ⟶ U) :
    ((Over.mapPullbackAdj f).comp (Over.mapPullbackAdj g)).unit.app T ≫
        (Over.pullback g ⋙ Over.pullback f).map z ≫
        (overPullbackCompIsoOfEq f g h e).inv.app U =
      (Over.mapPullbackAdj h).unit.app T ≫
        (Over.pullback h).map
          ((overMapCompIsoOfEq f g h e).hom.app T ≫ z) := by
  subst h
  simpa [overPullbackCompIsoOfEq, overMapCompIsoOfEq] using
    overPullbackComp_unit_naturality f g T U z

/-- Cover arguments obtained by two successive map/pullback counits agree
with the directly pulled argument after the composition comparison. -/
theorem overMapComp_hom_app_comp_map_comp_counit
    {C : Type u} [Category.{v, u} C] [HasPullbacks C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (T : Over X) (U : Over Z)
    (a : T ⟶ (Over.pullback g ⋙ Over.pullback f).obj U) :
    (Over.mapComp f g).hom.app T ≫
      (Over.map f ⋙ Over.map g).map a ≫
      (Over.map g).map
        ((Over.mapPullbackAdj f).counit.app ((Over.pullback g).obj U)) ≫
      (Over.mapPullbackAdj g).counit.app U =
    (Over.map (f ≫ g)).map (a ≫ (Over.pullbackComp f g).inv.app U) ≫
      (Over.mapPullbackAdj (f ≫ g)).counit.app U := by
  ext
  simp [Over.pullbackComp, Over.mapComp, Over.mapPullbackAdj]
  simp only [Category.assoc, pullback.lift_fst_assoc, pullback.lift_fst]
  simp

/-- The preceding cover-argument identity transported along an equality of
the composite base morphism. -/
theorem overMapCompIsoOfEq_hom_app_comp_map_comp_counit
    {C : Type u} [Category.{v, u} C] [HasPullbacks C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (e : f ≫ g = h)
    (T : Over X) (U : Over Z)
    (a : T ⟶ (Over.pullback g ⋙ Over.pullback f).obj U) :
    (overMapCompIsoOfEq f g h e).hom.app T ≫
      (Over.map f ⋙ Over.map g).map a ≫
      (Over.map g).map
        ((Over.mapPullbackAdj f).counit.app ((Over.pullback g).obj U)) ≫
      (Over.mapPullbackAdj g).counit.app U =
    (Over.map h).map
        (a ≫ (overPullbackCompIsoOfEq f g h e).inv.app U) ≫
      (Over.mapPullbackAdj h).counit.app U := by
  subst h
  simpa [overPullbackCompIsoOfEq, overMapCompIsoOfEq] using
    overMapComp_hom_app_comp_map_comp_counit f g T U a

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

@[simp] theorem scalarExtensionSpecMap_self
    (R : Type u) [CommRing R] :
    scalarExtensionSpecMap R R =
      𝟙 (_root_.AlgebraicGeometry.Spec (CommRingCat.of R)) := by
  simp [scalarExtensionSpecMap]

@[simp] theorem scalarExtensionSpecMap_comp
    (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] :
    scalarExtensionSpecMap S T ≫ scalarExtensionSpecMap R S =
      scalarExtensionSpecMap R T := by
  simp [scalarExtensionSpecMap, IsScalarTower.algebraMap_eq R S T]

/-- The affine tensor-unit comparison is the first projection from the
corresponding scheme pullback. -/
theorem pullbackSpecIso_scalarExtensionSelf_hom
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    (pullbackSymmetry
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of A) ↘
          _root_.AlgebraicGeometry.Spec (CommRingCat.of R))
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of R) ↘
          _root_.AlgebraicGeometry.Spec (CommRingCat.of R)) ≪≫
      _root_.AlgebraicGeometry.pullbackSpecIso' R R A).hom ≫
        _root_.AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight.toRingHom :
              A →+* TensorProduct R R A)) =
      pullback.fst
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of A) ↘
          _root_.AlgebraicGeometry.Spec (CommRingCat.of R))
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of R) ↘
          _root_.AlgebraicGeometry.Spec (CommRingCat.of R)) := by
  have hs :
      (_root_.AlgebraicGeometry.pullbackSpecIso' R R A).hom ≫
        _root_.AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight.toRingHom :
              A →+* TensorProduct R R A)) =
      pullback.snd
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of R) ↘
          _root_.AlgebraicGeometry.Spec (CommRingCat.of R))
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of A) ↘
          _root_.AlgebraicGeometry.Spec (CommRingCat.of R)) :=
    _root_.AlgebraicGeometry.pullbackSpecIso_hom_snd R R A
  rw [Iso.trans_hom, Category.assoc, hs,
    pullbackSymmetry_hom_comp_snd]

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

/-! ## Tensor-coordinate coherence -/

/-- A bialgebra equivalence as an isomorphism in commutative Hopf algebras. -/
def commHopfAlgIsoOfBialgEquiv
    {R A B : Type u}
    [CommRing R] [CommRing A] [CommRing B]
    [HopfAlgebra R A] [HopfAlgebra R B]
    (e : A ≃ₐc[R] B) :
    CommHopfAlgCat.of R A ≅ CommHopfAlgCat.of R B where
  hom := CommHopfAlgCat.ofHom e.toBialgHom
  inv := CommHopfAlgCat.ofHom e.symm.toBialgHom
  hom_inv_id := by
    ext x
    exact e.symm_apply_apply x
  inv_hom_id := by
    ext x
    exact e.apply_symm_apply x

/-- Tensor-unit comparison as an isomorphism of affine group schemes. -/
def affineGroupScalarExtensionSelfGroupIso
    (R A : Type u)
    [CommRing R] [CommRing A] [HopfAlgebra R A] :
    affineGroupScalarExtensionGroup R R A ≅
      affineGroupSchemeGroup R A :=
  ((_root_.AlgebraicGeometry.hopfSpec (CommRingCat.of R)).mapIso
    (commHopfAlgIsoOfBialgEquiv
      (Bialgebra.TensorProduct.lid R A)).op).symm

/-- The affine tensor-unit comparison agrees with the canonical identity
pullback isomorphism. -/
theorem affineGroupScalarExtensionSelfGroupIso_hom
    (R A : Type u)
    [CommRing R] [CommRing A] [HopfAlgebra R A] :
    (affineGroupBaseChangeGroupIso R R A ≪≫
        affineGroupScalarExtensionSelfGroupIso R A).hom.hom.hom =
      (overPullbackIdIsoOfEq (scalarExtensionSpecMap R R)
        (scalarExtensionSpecMap_self R)).hom.app
          (affineGroupSchemeGroup R A).X := by
  ext
  rw [show
    ((affineGroupBaseChangeGroupIso R R A ≪≫
      affineGroupScalarExtensionSelfGroupIso R A).hom.hom.hom).left =
        (pullbackSymmetry
          (_root_.AlgebraicGeometry.Spec (CommRingCat.of A) ↘
            _root_.AlgebraicGeometry.Spec (CommRingCat.of R))
          (_root_.AlgebraicGeometry.Spec (CommRingCat.of R) ↘
            _root_.AlgebraicGeometry.Spec (CommRingCat.of R)) ≪≫
         _root_.AlgebraicGeometry.pullbackSpecIso' R R A).hom ≫
        _root_.AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight.toRingHom :
              A →+* TensorProduct R R A)) from rfl]
  rw [overPullbackIdIsoOfEq_hom_app_left]
  exact pullbackSpecIso_scalarExtensionSelf_hom R A

/-- Associativity of scalar extension as a bialgebra equivalence. -/
def affineGroupScalarExtensionCompBialgEquiv
    (R S T A : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [HopfAlgebra R A] :
    TensorProduct S T (TensorProduct R S A) ≃ₐc[T]
      TensorProduct R T A := by
  apply BialgEquiv.ofAlgEquiv
    (Algebra.TensorProduct.cancelBaseChange R S T T A)
  · ext x
    simp [Bialgebra.TensorProduct.counitAlgHom_def]
    rw [TensorProduct.smul_tmul']
    rw [Algebra.TensorProduct.rid_tmul]
    simp
  · ext x
    simp [Bialgebra.TensorProduct.comulAlgHom_def]
    generalize hz :
      CoalgebraStruct.comul (R := R) (A := A) x = z
    clear hz
    induction z using TensorProduct.induction_on with
    | zero =>
        simp only [TensorProduct.tmul_zero, map_zero]
    | tmul a b =>
        simp only [
          Algebra.TensorProduct.tensorTensorTensorComm_tmul,
          Algebra.TensorProduct.map_tmul]
        have ha :
            ((Algebra.TensorProduct.cancelBaseChange R S T T A :
              TensorProduct S T (TensorProduct R S A) →ₐ[T]
                TensorProduct R T A)
              (1 ⊗ₜ[S] (1 ⊗ₜ[R] a))) =
                (1 ⊗ₜ[R] a) := by
          change
            (Algebra.TensorProduct.cancelBaseChange R S T T A)
              (1 ⊗ₜ[S] (1 ⊗ₜ[R] a)) = (1 ⊗ₜ[R] a)
          simpa only [one_smul] using
            (Algebra.TensorProduct.cancelBaseChange_tmul
              R S T T A (1 : T) (1 : S) a)
        have hb :
            ((Algebra.TensorProduct.cancelBaseChange R S T T A :
              TensorProduct S T (TensorProduct R S A) →ₐ[T]
                TensorProduct R T A)
              (1 ⊗ₜ[S] (1 ⊗ₜ[R] b))) =
                (1 ⊗ₜ[R] b) := by
          change
            (Algebra.TensorProduct.cancelBaseChange R S T T A)
              (1 ⊗ₜ[S] (1 ⊗ₜ[R] b)) = (1 ⊗ₜ[R] b)
          simpa only [one_smul] using
            (Algebra.TensorProduct.cancelBaseChange_tmul
              R S T T A (1 : T) (1 : S) b)
        rw [ha, hb]
    | add x y hx hy =>
        simp only [TensorProduct.tmul_add, map_add, hx, hy]

set_option maxHeartbeats 800000

/-- The affine base-change comparison sends the first pullback projection
to the tensor-product inclusion of the original Hopf algebra. -/
@[reassoc] theorem affineGroupBaseChangeOverIso_inv_fst
    (R S A : Type u) [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [HopfAlgebra R A] :
    (affineGroupBaseChangeOverIso R S A).inv.left ≫
      pullback.fst
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of A) ↘
          _root_.AlgebraicGeometry.Spec (CommRingCat.of R))
        (scalarExtensionSpecMap R S) =
    _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight :
        A →ₐ[R] TensorProduct R S A).toRingHom) := by
  change ((_root_.AlgebraicGeometry.pullbackSpecIso' R S A).inv ≫
      (pullbackSymmetry
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of A) ↘
          _root_.AlgebraicGeometry.Spec (CommRingCat.of R))
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of S) ↘
          _root_.AlgebraicGeometry.Spec (CommRingCat.of R))).inv) ≫
    pullback.fst
      (_root_.AlgebraicGeometry.Spec (CommRingCat.of A) ↘
        _root_.AlgebraicGeometry.Spec (CommRingCat.of R))
      (_root_.AlgebraicGeometry.Spec (CommRingCat.of S) ↘
        _root_.AlgebraicGeometry.Spec (CommRingCat.of R)) = _
  rw [Category.assoc, pullbackSymmetry_inv_comp_fst]
  change (_root_.AlgebraicGeometry.pullbackSpecIso R S A).inv ≫
      pullback.snd
        (_root_.AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap R S)))
        (_root_.AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap R A))) = _
  rw [_root_.AlgebraicGeometry.pullbackSpecIso_inv_snd]
  apply congrArg _root_.AlgebraicGeometry.Spec.map
  ext x
  rfl

/-- The affine base-change comparison sends the second pullback projection
to the tensor-product inclusion of the new base ring. -/
@[reassoc] theorem affineGroupBaseChangeOverIso_inv_snd
    (R S A : Type u) [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [HopfAlgebra R A] :
    (affineGroupBaseChangeOverIso R S A).inv.left ≫
      pullback.snd
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of A) ↘
          _root_.AlgebraicGeometry.Spec (CommRingCat.of R))
        (scalarExtensionSpecMap R S) =
    _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom :
        S →+* TensorProduct R S A)) := by
  change ((_root_.AlgebraicGeometry.pullbackSpecIso' R S A).inv ≫
      (pullbackSymmetry
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of A) ↘
          _root_.AlgebraicGeometry.Spec (CommRingCat.of R))
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of S) ↘
          _root_.AlgebraicGeometry.Spec (CommRingCat.of R))).inv) ≫
    pullback.snd
      (_root_.AlgebraicGeometry.Spec (CommRingCat.of A) ↘
        _root_.AlgebraicGeometry.Spec (CommRingCat.of R))
      (_root_.AlgebraicGeometry.Spec (CommRingCat.of S) ↘
        _root_.AlgebraicGeometry.Spec (CommRingCat.of R)) = _
  rw [Category.assoc, pullbackSymmetry_inv_comp_snd]
  change (_root_.AlgebraicGeometry.pullbackSpecIso R S A).inv ≫
      pullback.fst
        (_root_.AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap R S)))
        (_root_.AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap R A))) = _
  rw [_root_.AlgebraicGeometry.pullbackSpecIso_inv_fst]

/-- Tensor associativity as an isomorphism of represented affine group
objects. -/
def affineGroupScalarExtensionCompGroupIso
    (R S T A : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [HopfAlgebra R A] :
    affineGroupScalarExtensionGroup S T (TensorProduct R S A) ≅
      affineGroupScalarExtensionGroup R T A :=
  (_root_.AlgebraicGeometry.hopfSpec (CommRingCat.of T)).mapIso
    (commHopfAlgIsoOfBialgEquiv
      (affineGroupScalarExtensionCompBialgEquiv R S T A)).symm.op

theorem cancelBaseChange_comp_includeRight_includeRight
    (R S T A : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra S T] [Algebra R T] [Algebra R A]
    [IsScalarTower R S T] :
    let c := Algebra.TensorProduct.cancelBaseChange R S T T A
    c.toAlgHom.toRingHom.comp
      ((Algebra.TensorProduct.includeRight :
          TensorProduct R S A →ₐ[S]
            TensorProduct S T (TensorProduct R S A)).toRingHom.comp
        (Algebra.TensorProduct.includeRight :
          A →ₐ[R] TensorProduct R S A).toRingHom) =
      (Algebra.TensorProduct.includeRight :
        A →ₐ[R] TensorProduct R T A).toRingHom := by
  dsimp
  ext a
  change (Algebra.TensorProduct.cancelBaseChange R S T T A)
      (1 ⊗ₜ[S] (1 ⊗ₜ[R] a)) = 1 ⊗ₜ[R] a
  simpa only [one_smul] using
    (Algebra.TensorProduct.cancelBaseChange_tmul
      R S T T A (1 : T) (1 : S) a)

theorem cancelBaseChange_comp_includeRight_includeLeft
    (R S T A : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra S T] [Algebra R T] [Algebra R A]
    [IsScalarTower R S T] :
    let c := Algebra.TensorProduct.cancelBaseChange R S T T A
    c.toAlgHom.toRingHom.comp
      ((Algebra.TensorProduct.includeRight :
          TensorProduct R S A →ₐ[S]
            TensorProduct S T (TensorProduct R S A)).toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom :
          S →+* TensorProduct R S A)) =
      (Algebra.TensorProduct.includeLeftRingHom :
        T →+* TensorProduct R T A).comp (algebraMap S T) := by
  dsimp
  ext s
  change (Algebra.TensorProduct.cancelBaseChange R S T T A)
      (1 ⊗ₜ[S] (s ⊗ₜ[R] 1)) =
    (algebraMap S T s) ⊗ₜ[R] 1
  simpa only [Algebra.smul_def, mul_one] using
    (Algebra.TensorProduct.cancelBaseChange_tmul
      R S T T A (1 : T) s (1 : A))

theorem cancelBaseChange_comp_includeLeft
    (R S T A : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra S T] [Algebra R T] [Algebra R A]
    [IsScalarTower R S T] :
    let c := Algebra.TensorProduct.cancelBaseChange R S T T A
    c.toAlgHom.toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom :
        T →+* TensorProduct S T (TensorProduct R S A)) =
      (Algebra.TensorProduct.includeLeftRingHom :
        T →+* TensorProduct R T A) := by
  dsimp
  ext t
  change (Algebra.TensorProduct.cancelBaseChange R S T T A)
      (t ⊗ₜ[S] 1) = t ⊗ₜ[R] 1
  rw [Algebra.TensorProduct.one_def]
  simpa only [one_smul] using
    (Algebra.TensorProduct.cancelBaseChange_tmul
      R S T T A t (1 : S) (1 : A))

/-- Scheme-level form of associativity for affine scalar extension. -/
theorem affineGroupScalarExtensionCompOverIso
    (R S T A : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [HopfAlgebra R A] :
    (Over.pullback (scalarExtensionSpecMap S T)).mapIso
        (affineGroupBaseChangeOverIso R S A) ≪≫
      affineGroupBaseChangeOverIso S T (TensorProduct R S A) ≪≫
      (Grp.forget (Over (_root_.AlgebraicGeometry.Spec
        (CommRingCat.of T)))).mapIso
          (affineGroupScalarExtensionCompGroupIso R S T A) =
    (overPullbackCompIsoOfEq (scalarExtensionSpecMap S T)
        (scalarExtensionSpecMap R S) (scalarExtensionSpecMap R T)
        (scalarExtensionSpecMap_comp R S T)).symm.app
          ((_root_.AlgebraicGeometry.Spec
            (CommRingCat.of A)).asOver
              (_root_.AlgebraicGeometry.Spec (CommRingCat.of R))) ≪≫
      affineGroupBaseChangeOverIso R T A := by
  apply Iso.ext
  apply (Iso.inv_eq_inv _ _).mp
  ext
  let cSpec :
      ((_root_.AlgebraicGeometry.Spec
          (CommRingCat.of (TensorProduct R T A))).asOver
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of T))).left ⟶
      ((_root_.AlgebraicGeometry.Spec
          (CommRingCat.of
            (TensorProduct S T (TensorProduct R S A)))).asOver
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of T))).left :=
    _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.cancelBaseChange R S T T A).toRingHom)
  change
    ((cSpec ≫
        (affineGroupBaseChangeOverIso S T (TensorProduct R S A)).inv.left) ≫
      ((Over.pullback (scalarExtensionSpecMap S T)).map
        (affineGroupBaseChangeOverIso R S A).inv).left) =
    (affineGroupBaseChangeOverIso R T A).inv.left ≫
      ((overPullbackCompIsoOfEq (scalarExtensionSpecMap S T)
        (scalarExtensionSpecMap R S) (scalarExtensionSpecMap R T)
        (scalarExtensionSpecMap_comp R S T)).hom.app
          ((_root_.AlgebraicGeometry.Spec
            (CommRingCat.of A)).asOver
              (_root_.AlgebraicGeometry.Spec
                (CommRingCat.of R)))).left
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · let innerRight :
          ((_root_.AlgebraicGeometry.Spec
              (CommRingCat.of (TensorProduct R S A))).asOver
            (_root_.AlgebraicGeometry.Spec (CommRingCat.of S))).left ⟶
          ((_root_.AlgebraicGeometry.Spec
              (CommRingCat.of A)).asOver
            (_root_.AlgebraicGeometry.Spec (CommRingCat.of R))).left :=
        _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight :
            A →ₐ[R] TensorProduct R S A).toRingHom)
      have hRSRight :
          (affineGroupBaseChangeOverIso R S A).inv.left ≫
            pullback.fst
              (_root_.AlgebraicGeometry.Spec (CommRingCat.of A) ↘
                _root_.AlgebraicGeometry.Spec (CommRingCat.of R))
              (scalarExtensionSpecMap R S) = innerRight := by
        change (affineGroupBaseChangeOverIso R S A).inv.left ≫
          pullback.fst _ _ = _root_.AlgebraicGeometry.Spec.map _
        exact affineGroupBaseChangeOverIso_inv_fst R S A
      let outerRight :
          ((_root_.AlgebraicGeometry.Spec
              (CommRingCat.of
                (TensorProduct S T (TensorProduct R S A)))).asOver
            (_root_.AlgebraicGeometry.Spec (CommRingCat.of T))).left ⟶
          ((_root_.AlgebraicGeometry.Spec
              (CommRingCat.of (TensorProduct R S A))).asOver
            (_root_.AlgebraicGeometry.Spec (CommRingCat.of S))).left :=
        _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight :
            TensorProduct R S A →ₐ[S]
              TensorProduct S T (TensorProduct R S A)).toRingHom)
      have hSTRight :
          (affineGroupBaseChangeOverIso S T
              (TensorProduct R S A)).inv.left ≫
            pullback.fst
              (_root_.AlgebraicGeometry.Spec
                  (CommRingCat.of (TensorProduct R S A)) ↘
                _root_.AlgebraicGeometry.Spec (CommRingCat.of S))
              (scalarExtensionSpecMap S T) = outerRight := by
        change (affineGroupBaseChangeOverIso S T
            (TensorProduct R S A)).inv.left ≫
          pullback.fst _ _ = _root_.AlgebraicGeometry.Spec.map _
        exact affineGroupBaseChangeOverIso_inv_fst
          S T (TensorProduct R S A)
      let directRight :
          ((_root_.AlgebraicGeometry.Spec
              (CommRingCat.of (TensorProduct R T A))).asOver
            (_root_.AlgebraicGeometry.Spec (CommRingCat.of T))).left ⟶
          ((_root_.AlgebraicGeometry.Spec
              (CommRingCat.of A)).asOver
            (_root_.AlgebraicGeometry.Spec (CommRingCat.of R))).left :=
        _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight :
            A →ₐ[R] TensorProduct R T A).toRingHom)
      have hRTRight :
          (affineGroupBaseChangeOverIso R T A).inv.left ≫
            pullback.fst
              (_root_.AlgebraicGeometry.Spec (CommRingCat.of A) ↘
                _root_.AlgebraicGeometry.Spec (CommRingCat.of R))
              (scalarExtensionSpecMap R T) = directRight := by
        change (affineGroupBaseChangeOverIso R T A).inv.left ≫
          pullback.fst _ _ = _root_.AlgebraicGeometry.Spec.map _
        exact affineGroupBaseChangeOverIso_inv_fst R T A
      slice_lhs 3 4 =>
        exact overPullback_map_fst (scalarExtensionSpecMap S T)
          (affineGroupBaseChangeOverIso R S A).inv
      slice_lhs 4 5 => exact hRSRight
      slice_lhs 2 3 => exact hSTRight
      slice_rhs 2 4 =>
        exact overPullbackCompIsoOfEq_hom_app_fst_fst
          (scalarExtensionSpecMap S T) (scalarExtensionSpecMap R S)
          (scalarExtensionSpecMap R T) (scalarExtensionSpecMap_comp R S T)
          ((_root_.AlgebraicGeometry.Spec
            (CommRingCat.of A)).asOver
              (_root_.AlgebraicGeometry.Spec (CommRingCat.of R)))
      slice_rhs 1 2 => exact hRTRight
      change
        _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.cancelBaseChange R S T T A).toRingHom) ≫
          _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight :
              TensorProduct R S A →ₐ[S]
                TensorProduct S T (TensorProduct R S A)).toRingHom) ≫
          _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight :
              A →ₐ[R] TensorProduct R S A).toRingHom) =
        _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight :
            A →ₐ[R] TensorProduct R T A).toRingHom)
      rw [← _root_.AlgebraicGeometry.Spec.map_comp,
        ← _root_.AlgebraicGeometry.Spec.map_comp]
      exact congrArg _root_.AlgebraicGeometry.Spec.map
        (congrArg CommRingCat.ofHom
          (cancelBaseChange_comp_includeRight_includeRight R S T A))
    · let innerLeft :
          ((_root_.AlgebraicGeometry.Spec
              (CommRingCat.of (TensorProduct R S A))).asOver
            (_root_.AlgebraicGeometry.Spec (CommRingCat.of S))).left ⟶
          _root_.AlgebraicGeometry.Spec (CommRingCat.of S) :=
        _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom :
            S →+* TensorProduct R S A))
      have hRSLeft :
          (affineGroupBaseChangeOverIso R S A).inv.left ≫
            pullback.snd
              (_root_.AlgebraicGeometry.Spec (CommRingCat.of A) ↘
                _root_.AlgebraicGeometry.Spec (CommRingCat.of R))
              (scalarExtensionSpecMap R S) = innerLeft := by
        change (affineGroupBaseChangeOverIso R S A).inv.left ≫
          pullback.snd _ _ = _root_.AlgebraicGeometry.Spec.map _
        exact affineGroupBaseChangeOverIso_inv_snd R S A
      let outerRight :
          ((_root_.AlgebraicGeometry.Spec
              (CommRingCat.of
                (TensorProduct S T (TensorProduct R S A)))).asOver
            (_root_.AlgebraicGeometry.Spec (CommRingCat.of T))).left ⟶
          ((_root_.AlgebraicGeometry.Spec
              (CommRingCat.of (TensorProduct R S A))).asOver
            (_root_.AlgebraicGeometry.Spec (CommRingCat.of S))).left :=
        _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight :
            TensorProduct R S A →ₐ[S]
              TensorProduct S T (TensorProduct R S A)).toRingHom)
      have hSTRight :
          (affineGroupBaseChangeOverIso S T
              (TensorProduct R S A)).inv.left ≫
            pullback.fst
              (_root_.AlgebraicGeometry.Spec
                  (CommRingCat.of (TensorProduct R S A)) ↘
                _root_.AlgebraicGeometry.Spec (CommRingCat.of S))
              (scalarExtensionSpecMap S T) = outerRight := by
        change (affineGroupBaseChangeOverIso S T
            (TensorProduct R S A)).inv.left ≫
          pullback.fst _ _ = _root_.AlgebraicGeometry.Spec.map _
        exact affineGroupBaseChangeOverIso_inv_fst
          S T (TensorProduct R S A)
      let directLeft :
          ((_root_.AlgebraicGeometry.Spec
              (CommRingCat.of (TensorProduct R T A))).asOver
            (_root_.AlgebraicGeometry.Spec (CommRingCat.of T))).left ⟶
          _root_.AlgebraicGeometry.Spec (CommRingCat.of T) :=
        _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom :
            T →+* TensorProduct R T A))
      have hRTLeft :
          (affineGroupBaseChangeOverIso R T A).inv.left ≫
            pullback.snd
              (_root_.AlgebraicGeometry.Spec (CommRingCat.of A) ↘
                _root_.AlgebraicGeometry.Spec (CommRingCat.of R))
              (scalarExtensionSpecMap R T) = directLeft := by
        change (affineGroupBaseChangeOverIso R T A).inv.left ≫
          pullback.snd _ _ = _root_.AlgebraicGeometry.Spec.map _
        exact affineGroupBaseChangeOverIso_inv_snd R T A
      slice_lhs 3 4 =>
        exact overPullback_map_fst (scalarExtensionSpecMap S T)
          (affineGroupBaseChangeOverIso R S A).inv
      slice_lhs 4 5 => exact hRSLeft
      slice_lhs 2 3 => exact hSTRight
      slice_rhs 2 4 =>
        exact overPullbackCompIsoOfEq_hom_app_fst_snd
          (scalarExtensionSpecMap S T) (scalarExtensionSpecMap R S)
          (scalarExtensionSpecMap R T) (scalarExtensionSpecMap_comp R S T)
          ((_root_.AlgebraicGeometry.Spec
            (CommRingCat.of A)).asOver
              (_root_.AlgebraicGeometry.Spec (CommRingCat.of R)))
      slice_rhs 1 2 => exact hRTLeft
      change
        _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.cancelBaseChange R S T T A).toRingHom) ≫
          _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight :
              TensorProduct R S A →ₐ[S]
                TensorProduct S T (TensorProduct R S A)).toRingHom) ≫
          _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeLeftRingHom :
              S →+* TensorProduct R S A)) =
        _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeLeftRingHom :
              T →+* TensorProduct R T A)) ≫
          _root_.AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (algebraMap S T))
      rw [← _root_.AlgebraicGeometry.Spec.map_comp,
        ← _root_.AlgebraicGeometry.Spec.map_comp,
        ← _root_.AlgebraicGeometry.Spec.map_comp]
      exact congrArg _root_.AlgebraicGeometry.Spec.map
        (congrArg CommRingCat.ofHom
          (cancelBaseChange_comp_includeRight_includeLeft R S T A))
  · let outerLeft :
        ((_root_.AlgebraicGeometry.Spec
            (CommRingCat.of
              (TensorProduct S T (TensorProduct R S A)))).asOver
          (_root_.AlgebraicGeometry.Spec (CommRingCat.of T))).left ⟶
        _root_.AlgebraicGeometry.Spec (CommRingCat.of T) :=
      _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom :
          T →+* TensorProduct S T (TensorProduct R S A)))
    have hSTLeft :
        (affineGroupBaseChangeOverIso S T
            (TensorProduct R S A)).inv.left ≫
          pullback.snd
            (_root_.AlgebraicGeometry.Spec
                (CommRingCat.of (TensorProduct R S A)) ↘
              _root_.AlgebraicGeometry.Spec (CommRingCat.of S))
            (scalarExtensionSpecMap S T) = outerLeft := by
      change (affineGroupBaseChangeOverIso S T
          (TensorProduct R S A)).inv.left ≫
        pullback.snd _ _ = _root_.AlgebraicGeometry.Spec.map _
      exact affineGroupBaseChangeOverIso_inv_snd
        S T (TensorProduct R S A)
    let directLeft :
        ((_root_.AlgebraicGeometry.Spec
            (CommRingCat.of (TensorProduct R T A))).asOver
          (_root_.AlgebraicGeometry.Spec (CommRingCat.of T))).left ⟶
        _root_.AlgebraicGeometry.Spec (CommRingCat.of T) :=
      _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom :
          T →+* TensorProduct R T A))
    have hRTLeft :
        (affineGroupBaseChangeOverIso R T A).inv.left ≫
          pullback.snd
            (_root_.AlgebraicGeometry.Spec (CommRingCat.of A) ↘
              _root_.AlgebraicGeometry.Spec (CommRingCat.of R))
            (scalarExtensionSpecMap R T) = directLeft := by
      change (affineGroupBaseChangeOverIso R T A).inv.left ≫
        pullback.snd _ _ = _root_.AlgebraicGeometry.Spec.map _
      exact affineGroupBaseChangeOverIso_inv_snd R T A
    slice_lhs 3 4 =>
      exact overPullback_map_snd (scalarExtensionSpecMap S T)
        (affineGroupBaseChangeOverIso R S A).inv
    slice_lhs 2 3 => exact hSTLeft
    slice_rhs 2 3 =>
      exact overPullbackCompIsoOfEq_hom_app_snd
        (scalarExtensionSpecMap S T) (scalarExtensionSpecMap R S)
        (scalarExtensionSpecMap R T) (scalarExtensionSpecMap_comp R S T)
        ((_root_.AlgebraicGeometry.Spec
          (CommRingCat.of A)).asOver
            (_root_.AlgebraicGeometry.Spec (CommRingCat.of R)))
    slice_rhs 1 2 => exact hRTLeft
    change
      _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.cancelBaseChange R S T T A).toRingHom) ≫
        _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom :
            T →+* TensorProduct S T (TensorProduct R S A))) =
      _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom :
          T →+* TensorProduct R T A))
    rw [← _root_.AlgebraicGeometry.Spec.map_comp]
    exact congrArg _root_.AlgebraicGeometry.Spec.map
      (congrArg CommRingCat.ofHom
        (cancelBaseChange_comp_includeLeft R S T A))

/-- The iterated affine base-change comparisons agree with the canonical
pullback-composition isomorphism and tensor associativity. -/
theorem affineGroupScalarExtensionCompGroupIso_hom
    (R S T A : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [HopfAlgebra R A] :
    (Over.pullback (scalarExtensionSpecMap S T)).map
        (affineGroupBaseChangeGroupIso R S A).hom.hom.hom ≫
      (affineGroupBaseChangeGroupIso S T
        (TensorProduct R S A)).hom.hom.hom ≫
      (affineGroupScalarExtensionCompGroupIso R S T A).hom.hom.hom =
    (overPullbackCompIsoOfEq (scalarExtensionSpecMap S T)
        (scalarExtensionSpecMap R S) (scalarExtensionSpecMap R T)
        (scalarExtensionSpecMap_comp R S T)).inv.app
          (affineGroupSchemeGroup R A).X ≫
      (affineGroupBaseChangeGroupIso R T A).hom.hom.hom := by
  exact congrArg Iso.hom
    (affineGroupScalarExtensionCompOverIso R S T A)

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
