/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.FpqcModuleDescent

/-!
# Transport from comonadic affine module descent

This file constructs the generic transport map used to turn a coalgebra for
the extension--restriction comonad into choice-free affine module descent
data. Given two maps out of the cover algebra that agree over the base, the
transport combines extension of scalars, the coalgebra coaction, and the
adjunction counit.

The construction isolates the functorial core of the triple-overlap argument.
Its identity and composition laws follow from the counit and coassociativity
structure of the adjunction, without choosing a model of the triple overlap.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory

namespace RiemannResearch.AlgebraicGeometry

private noncomputable def extendScalarsCongr
    {R S : Type u} [CommRing R] [CommRing S]
    {f g : R →+* S} (h : f = g) :
    ModuleCat.extendScalars f ≅ ModuleCat.extendScalars g := by
  subst g
  exact Iso.refl _

private theorem extendScalarsCongr_hom_trans
    {R S : Type u} [CommRing R] [CommRing S]
    {f₁ f₂ f₃ : R →+* S}
    (h₁₂ : f₁ = f₂) (h₂₃ : f₂ = f₃) (h₁₃ : f₁ = f₃) :
    (extendScalarsCongr h₁₂).hom ≫ (extendScalarsCongr h₂₃).hom =
      (extendScalarsCongr h₁₃).hom := by
  subst f₂
  subst f₃
  rfl

/-- Transport the extension of a comonad value along two algebra maps that
agree after composition with the base map. The associators and
extension-of-scalars composition isomorphisms expose the adjunction counit. -/
noncomputable def affineModuleComonadicTransport
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g₁ g₂ : A →+* B)
    (h : g₁.comp f = g₂.comp f) :
    (ModuleCat.extendRestrictScalarsAdj f).toComonad.toFunctor ⋙
        ModuleCat.extendScalars g₁ ⟶
      ModuleCat.extendScalars g₂ :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (ModuleCat.restrictScalars f)
      (ModuleCat.extendScalarsComp f g₁).inv ≫
    Functor.whiskerLeft (ModuleCat.restrictScalars f)
      (extendScalarsCongr h).hom ≫
    Functor.whiskerLeft (ModuleCat.restrictScalars f)
      (ModuleCat.extendScalarsComp f g₂).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (ModuleCat.extendRestrictScalarsAdj f).counit
      (ModuleCat.extendScalars g₂) ≫
    (Functor.leftUnitor _).hom

/-- The component of comonadic transport, with the coherence isomorphisms
made explicit. -/
@[simp]
theorem affineModuleComonadicTransport_app
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g₁ g₂ : A →+* B)
    (h : g₁.comp f = g₂.comp f) (M : ModuleCat A) :
    (affineModuleComonadicTransport f g₁ g₂ h).app M =
      (ModuleCat.extendScalarsComp f g₁).inv.app
          ((ModuleCat.restrictScalars f).obj M) ≫
        (extendScalarsCongr h).hom.app ((ModuleCat.restrictScalars f).obj M) ≫
        (ModuleCat.extendScalarsComp f g₂).hom.app
          ((ModuleCat.restrictScalars f).obj M) ≫
        (ModuleCat.extendScalars g₂).map
          ((ModuleCat.extendRestrictScalarsAdj f).counit.app M) := by
  rfl

/-- Along a single algebra map, comonadic transport is the image of the
comonad counit. This is the identity law needed for choice-free descent data. -/
@[simp]
theorem affineModuleComonadicTransport_self
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : A →+* B) (M : ModuleCat A) :
    (affineModuleComonadicTransport f g g rfl).app M =
      (ModuleCat.extendScalars g).map
        ((ModuleCat.extendRestrictScalarsAdj f).toComonad.ε.app M) := by
  change
    (Functor.associator
        (ModuleCat.restrictScalars f)
        (ModuleCat.extendScalars f)
        (ModuleCat.extendScalars g)).hom.app M ≫
      (Functor.whiskerLeft (ModuleCat.restrictScalars f)
        (ModuleCat.extendScalarsComp f g).inv).app M ≫
      (Functor.whiskerLeft (ModuleCat.restrictScalars f)
        (extendScalarsCongr rfl).hom).app M ≫
      (Functor.whiskerLeft (ModuleCat.restrictScalars f)
        (ModuleCat.extendScalarsComp f g).hom).app M ≫
      (Functor.associator
        (ModuleCat.restrictScalars f)
        (ModuleCat.extendScalars f)
        (ModuleCat.extendScalars g)).inv.app M ≫
      (Functor.whiskerRight
        (ModuleCat.extendRestrictScalarsAdj f).counit
        (ModuleCat.extendScalars g)).app M ≫
      (Functor.leftUnitor (ModuleCat.extendScalars g)).hom.app M =
        (ModuleCat.extendScalars g).map
          ((ModuleCat.extendRestrictScalarsAdj f).toComonad.ε.app M)
  simp [extendScalarsCongr]
  rfl

set_option maxRecDepth 10000 in
/-- Comonadic transport composes on triple overlaps. This is the generic
coassociativity calculation needed for choice-free affine descent data. -/
theorem affineModuleComonadicTransport_comp
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g₁ g₂ g₃ : A →+* B)
    (h₁₂ : g₁.comp f = g₂.comp f)
    (h₂₃ : g₂.comp f = g₃.comp f)
    (h₁₃ : g₁.comp f = g₃.comp f)
    (M : ModuleCat A) :
    (ModuleCat.extendScalars g₁).map
        ((ModuleCat.extendRestrictScalarsAdj f).toComonad.δ.app M) ≫
      (affineModuleComonadicTransport f g₁ g₂ h₁₂).app
        ((ModuleCat.extendRestrictScalarsAdj f).toComonad.obj M) ≫
      (affineModuleComonadicTransport f g₂ g₃ h₂₃).app M =
        (affineModuleComonadicTransport f g₁ g₃ h₁₃).app M := by
  rw [affineModuleComonadicTransport_app,
    affineModuleComonadicTransport_app,
    affineModuleComonadicTransport_app]
  let X := (ModuleCat.restrictScalars f).obj M
  let Y := (ModuleCat.restrictScalars f).obj
    ((ModuleCat.extendScalars f).obj X)
  change
    (ModuleCat.extendScalars g₁).map
        ((ModuleCat.extendScalars f).map
          ((ModuleCat.extendRestrictScalarsAdj f).unit.app X)) ≫
      (ModuleCat.extendScalarsComp f g₁).inv.app Y ≫
      (extendScalarsCongr h₁₂).hom.app Y ≫
      (ModuleCat.extendScalarsComp f g₂).hom.app Y ≫
      (ModuleCat.extendScalars g₂).map
        ((ModuleCat.extendRestrictScalarsAdj f).counit.app
          ((ModuleCat.extendScalars f).obj X)) ≫
      (ModuleCat.extendScalarsComp f g₂).inv.app X ≫
      (extendScalarsCongr h₂₃).hom.app X ≫
      (ModuleCat.extendScalarsComp f g₃).hom.app X ≫
      (ModuleCat.extendScalars g₃).map
        ((ModuleCat.extendRestrictScalarsAdj f).counit.app M) =
      (ModuleCat.extendScalarsComp f g₁).inv.app X ≫
      (extendScalarsCongr h₁₃).hom.app X ≫
      (ModuleCat.extendScalarsComp f g₃).hom.app X ≫
      (ModuleCat.extendScalars g₃).map
        ((ModuleCat.extendRestrictScalarsAdj f).counit.app M)
  have hc₁ :
      (ModuleCat.extendScalars f ⋙ ModuleCat.extendScalars g₁).map
          ((ModuleCat.extendRestrictScalarsAdj f).unit.app X) ≫
        (ModuleCat.extendScalarsComp f g₁).inv.app
          ((ModuleCat.restrictScalars f).obj
            ((ModuleCat.extendScalars f).obj X)) =
      (ModuleCat.extendScalarsComp f g₁).inv.app X ≫
        (ModuleCat.extendScalars (g₁.comp f)).map
          ((ModuleCat.extendRestrictScalarsAdj f).unit.app X) := by
    exact (ModuleCat.extendScalarsComp f g₁).inv.naturality _
  have ht₁₂ :
      (ModuleCat.extendScalars (g₁.comp f)).map
          ((ModuleCat.extendRestrictScalarsAdj f).unit.app X) ≫
        (extendScalarsCongr h₁₂).hom.app
          ((ModuleCat.restrictScalars f).obj
            ((ModuleCat.extendScalars f).obj X)) =
      (extendScalarsCongr h₁₂).hom.app X ≫
        (ModuleCat.extendScalars (g₂.comp f)).map
          ((ModuleCat.extendRestrictScalarsAdj f).unit.app X) := by
    exact (extendScalarsCongr h₁₂).hom.naturality _
  have hc₂ :
      (ModuleCat.extendScalars (g₂.comp f)).map
          ((ModuleCat.extendRestrictScalarsAdj f).unit.app X) ≫
        (ModuleCat.extendScalarsComp f g₂).hom.app
          ((ModuleCat.restrictScalars f).obj
            ((ModuleCat.extendScalars f).obj X)) =
      (ModuleCat.extendScalarsComp f g₂).hom.app X ≫
        (ModuleCat.extendScalars f ⋙ ModuleCat.extendScalars g₂).map
          ((ModuleCat.extendRestrictScalarsAdj f).unit.app X) := by
    exact (ModuleCat.extendScalarsComp f g₂).hom.naturality _
  have htriangle :
      (ModuleCat.extendScalars f ⋙ ModuleCat.extendScalars g₂).map
          ((ModuleCat.extendRestrictScalarsAdj f).unit.app X) ≫
        (ModuleCat.extendScalars g₂).map
          ((ModuleCat.extendRestrictScalarsAdj f).counit.app
            ((ModuleCat.extendScalars f).obj X)) =
      𝟙 ((ModuleCat.extendScalars f ⋙
        ModuleCat.extendScalars g₂).obj X) := by
    calc
      _ = (ModuleCat.extendScalars g₂).map
          (𝟙 ((ModuleCat.extendScalars f).obj X)) := by
        simpa only [Functor.comp_map, ← Functor.map_comp] using
          congrArg (fun q => (ModuleCat.extendScalars g₂).map q)
            ((ModuleCat.extendRestrictScalarsAdj f).left_triangle_components X)
      _ = 𝟙 ((ModuleCat.extendScalars g₂).obj
          ((ModuleCat.extendScalars f).obj X)) :=
        (ModuleCat.extendScalars g₂).map_id _
      _ = _ := rfl
  have ht :
      (extendScalarsCongr h₁₂).hom.app X ≫
        (extendScalarsCongr h₂₃).hom.app X =
      (extendScalarsCongr h₁₃).hom.app X := by
    exact NatTrans.congr_app
      (extendScalarsCongr_hom_trans h₁₂ h₂₃ h₁₃) X
  have hc₂cancel :
      (ModuleCat.extendScalarsComp f g₂).hom.app X ≫
        𝟙 ((ModuleCat.extendScalars f ⋙
          ModuleCat.extendScalars g₂).obj X) ≫
        (ModuleCat.extendScalarsComp f g₂).inv.app X =
      𝟙 ((ModuleCat.extendScalars (g₂.comp f)).obj X) := by
    rw [Category.id_comp]
    exact (ModuleCat.extendScalarsComp f g₂).hom_inv_id_app X
  have ht' :
      (extendScalarsCongr h₁₂).hom.app X ≫
        𝟙 ((ModuleCat.extendScalars (g₂.comp f)).obj X) ≫
        (extendScalarsCongr h₂₃).hom.app X =
      (extendScalarsCongr h₁₃).hom.app X := by
    rw [Category.id_comp]
    exact ht
  slice_lhs 1 2 => exact hc₁
  slice_lhs 2 3 => exact ht₁₂
  slice_lhs 3 4 => exact hc₂
  slice_lhs 4 5 => exact htriangle
  slice_lhs 3 5 => exact hc₂cancel
  slice_lhs 2 4 => exact ht'
  simp only [Category.assoc]

/-- The descent transport map associated to a coalgebra. It first applies the
coaction and then evaluates the generic comonadic transport. -/
noncomputable def comonadicModuleDescentTransportMap
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g₁ g₂ : A →+* B)
    (h : g₁.comp f = g₂.comp f)
    (Q : ComonadicModuleDescentData f) :
    (ModuleCat.extendScalars g₁).obj Q.A ⟶
      (ModuleCat.extendScalars g₂).obj Q.A :=
  (ModuleCat.extendScalars g₁).map Q.a ≫
    (affineModuleComonadicTransport f g₁ g₂ h).app Q.A

/-- The descent transport attached to the same map at both ends is the
identity. This packages the coalgebra counit law in descent-data form. -/
@[simp]
theorem comonadicModuleDescentTransportMap_self
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : A →+* B)
    (Q : ComonadicModuleDescentData f) :
    comonadicModuleDescentTransportMap f g g rfl Q =
      𝟙 ((ModuleCat.extendScalars g).obj Q.A) := by
  rw [comonadicModuleDescentTransportMap,
    affineModuleComonadicTransport_self, ← Functor.map_comp,
    Q.counit]
  simp

/-- Coalgebra transport composes for three compatible algebra maps. This is
the choice-free descent cocycle law obtained from coalgebra coassociativity. -/
theorem comonadicModuleDescentTransportMap_comp
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g₁ g₂ g₃ : A →+* B)
    (h₁₂ : g₁.comp f = g₂.comp f)
    (h₂₃ : g₂.comp f = g₃.comp f)
    (h₁₃ : g₁.comp f = g₃.comp f)
    (Q : ComonadicModuleDescentData f) :
    comonadicModuleDescentTransportMap f g₁ g₂ h₁₂ Q ≫
        comonadicModuleDescentTransportMap f g₂ g₃ h₂₃ Q =
      comonadicModuleDescentTransportMap f g₁ g₃ h₁₃ Q := by
  dsimp only [comonadicModuleDescentTransportMap]
  simp only [Category.assoc]
  have hn :=
    ((affineModuleComonadicTransport f g₁ g₂ h₁₂).naturality Q.a).symm
  change
    (affineModuleComonadicTransport f g₁ g₂ h₁₂).app Q.A ≫
        (ModuleCat.extendScalars g₂).map Q.a =
      (ModuleCat.extendScalars g₁).map
          ((ModuleCat.extendRestrictScalarsAdj f).toComonad.map Q.a) ≫
        (affineModuleComonadicTransport f g₁ g₂ h₁₂).app
          ((ModuleCat.extendRestrictScalarsAdj f).toComonad.obj Q.A) at hn
  slice_lhs 2 3 => exact hn
  have hco :
      (ModuleCat.extendScalars g₁).map Q.a ≫
          (ModuleCat.extendScalars g₁).map
            ((ModuleCat.extendRestrictScalarsAdj f).toComonad.map Q.a) =
        (ModuleCat.extendScalars g₁).map Q.a ≫
          (ModuleCat.extendScalars g₁).map
            ((ModuleCat.extendRestrictScalarsAdj f).toComonad.δ.app Q.A) := by
    rw [← Functor.map_comp, ← Functor.map_comp, Q.coassoc]
  slice_lhs 1 2 => exact hco
  slice_lhs 2 4 =>
    exact affineModuleComonadicTransport_comp
      f g₁ g₂ g₃ h₁₂ h₂₃ h₁₃ Q.A

/-- The transport maps commute with morphisms of
extension--restriction coalgebras. -/
theorem comonadicModuleDescentTransportMap_natural
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g₁ g₂ : A →+* B)
    (h : g₁.comp f = g₂.comp f)
    {Q Q' : ComonadicModuleDescentData f} (q : Q ⟶ Q') :
    comonadicModuleDescentTransportMap f g₁ g₂ h Q ≫
        (ModuleCat.extendScalars g₂).map q.f =
      (ModuleCat.extendScalars g₁).map q.f ≫
        comonadicModuleDescentTransportMap f g₁ g₂ h Q' := by
  dsimp only [comonadicModuleDescentTransportMap]
  rw [Category.assoc,
    ← (affineModuleComonadicTransport f g₁ g₂ h).naturality q.f]
  simp only [Functor.comp_map]
  rw [← Category.assoc, ← Functor.map_comp, q.h, Functor.map_comp,
    Category.assoc]

end RiemannResearch.AlgebraicGeometry
