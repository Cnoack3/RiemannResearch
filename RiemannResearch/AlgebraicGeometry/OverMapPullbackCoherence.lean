/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Pullback coherence in over categories

Generic identity and composition coherence lemmas for the map/pullback adjunction
in over categories.
-/

namespace RiemannResearch.AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits CategoryTheory.Over

universe u v

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

end

end RiemannResearch.AlgebraicGeometry
