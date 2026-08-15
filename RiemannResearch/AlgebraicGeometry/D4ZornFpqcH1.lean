/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.FpqcH1Functoriality
import RiemannResearch.LinearAlgebra.RootSystem.D4ZornFiniteEquations

/-!
# The finite Zorn related-triple presheaf and fpqc Čech H¹

A covariant group-valued functor on commutative rings becomes a presheaf on
schemes over an affine base by evaluation on global sections. This file
constructs that adapter, its fixed-cover nonabelian Čech H¹, and the witnessed
common-refinement quotient over all fpqc covers. The natural diagram-symmetry
action of the finite-equation Zorn functor acts on both constructions.

This is the direct point-functor route to the honest presheaf boundary. The
set-valued point functor is represented by the explicit coordinate algebra in
`D4ZornCoordinateRing`, and its compatible Hopf structure is supplied
downstream; the constructions here deliberately remain independent of that
structure and act directly on the finite-equation functor. Neither this route
nor the downstream represented route by itself proves the fpqc sheaf
condition or identifies the Čech quotient with a torsor classification.
-/

namespace RiemannResearch.AlgebraicGeometry

open CategoryTheory

universe u v w

noncomputable section

/-- Global sections restricted to schemes over the affine base. -/
def pointFunctorGlobalSections (R : CommRingCat.{u}) :
    (Over (_root_.AlgebraicGeometry.Spec R))ᵒᵖ ⥤ CommRingCat.{u} :=
  (Over.forget (_root_.AlgebraicGeometry.Spec R)).op ⋙
    _root_.AlgebraicGeometry.Scheme.Γ

/-- Extend a covariant group-valued functor on commutative rings to a
presheaf on schemes over the affine base by evaluation on global sections. -/
def pointFunctorPresheaf (R : CommRingCat.{u})
    (P : CommRingCat.{u} ⥤ GrpCat.{u}) :
    (Over (_root_.AlgebraicGeometry.Spec R))ᵒᵖ ⥤ GrpCat.{u} :=
  pointFunctorGlobalSections R ⋙ P

/-- Precomposition with global sections sends point-functor automorphisms
to automorphisms of the associated presheaf. -/
def pointFunctorPresheafAut
    (R : CommRingCat.{u}) (P : CommRingCat.{u} ⥤ GrpCat.{u}) :
    CategoryTheory.Aut P →*
      CategoryTheory.Aut (pointFunctorPresheaf R P) where
  toFun e := (pointFunctorGlobalSections R).isoWhiskerLeft e
  map_one' := by
    apply CategoryTheory.Aut.ext
    apply NatTrans.ext
    funext X
    rfl
  map_mul' e f := by
    apply CategoryTheory.Aut.ext
    apply NatTrans.ext
    funext X
    rfl

/-- Fixed-cover nonabelian Čech H¹ after the point-functor adapter. -/
abbrev PointFunctorFpqcCechH1
    (R : CommRingCat.{u}) (P : CommRingCat.{u} ⥤ GrpCat.{u})
    {I : Type v} (U : FpqcCover R I) :=
  PresheafOfGroups.H1 (pointFunctorPresheaf R P) U.obj

/-- A fixed-cover class for an arbitrary group presheaf, together with its
witnessed fpqc cover. -/
structure PresheafFpqcH1Representative
    (R : CommRingCat.{u})
    (G : (Over (_root_.AlgebraicGeometry.Spec R))ᵒᵖ ⥤ GrpCat.{u}) where
  I : Type v
  cover : FpqcCover R I
  value : PresheafOfGroups.H1 G cover.obj

namespace PresheafFpqcH1Representative

variable (R : CommRingCat.{u})
variable
  (G : (Over (_root_.AlgebraicGeometry.Spec R))ᵒᵖ ⥤ GrpCat.{u})

/-- Two representatives agree if their pullbacks agree on a common
refinement. -/
def Equivalent
    (a b : PresheafFpqcH1Representative.{u, v} R G) : Prop :=
  ∃ (K : Type v) (W : FpqcCover R K)
    (ra : W.Refinement a.cover) (rb : W.Refinement b.cover),
    ra.pullbackH1 a.value = rb.pullbackH1 b.value

theorem equivalent_refl
    (a : PresheafFpqcH1Representative.{u, v} R G) :
    Equivalent R G a a := by
  exact ⟨a.I, a.cover, FpqcCover.Refinement.refl a.cover,
    FpqcCover.Refinement.refl a.cover, rfl⟩

theorem equivalent_symm
    {a b : PresheafFpqcH1Representative.{u, v} R G}
    (h : Equivalent R G a b) :
    Equivalent R G b a := by
  rcases h with ⟨K, W, ra, rb, hab⟩
  exact ⟨K, W, rb, ra, hab.symm⟩

theorem equivalent_trans
    {a b c : PresheafFpqcH1Representative.{u, v} R G}
    (hab : Equivalent R G a b)
    (hbc : Equivalent R G b c) :
    Equivalent R G a c := by
  rcases hab with ⟨K₁, W₁, ra, rb₁, hab⟩
  rcases hbc with ⟨K₂, W₂, rb₂, rc, hbc⟩
  let D := FpqcCover.commonRefinementData W₁ W₂
  refine ⟨D.K, D.cover, D.toLeft.comp ra, D.toRight.comp rc, ?_⟩
  calc
    (D.toLeft.comp ra).pullbackH1 a.value =
        D.toLeft.pullbackH1 (ra.pullbackH1 a.value) :=
      (FpqcCover.Refinement.pullbackH1_comp ra D.toLeft a.value).symm
    _ = D.toLeft.pullbackH1 (rb₁.pullbackH1 b.value) :=
      congrArg D.toLeft.pullbackH1 hab
    _ = (D.toLeft.comp rb₁).pullbackH1 b.value :=
      FpqcCover.Refinement.pullbackH1_comp rb₁ D.toLeft b.value
    _ = (D.toRight.comp rb₂).pullbackH1 b.value :=
      FpqcCover.Refinement.pullbackH1_eq
        (D.toLeft.comp rb₁) (D.toRight.comp rb₂) b.value
    _ = D.toRight.pullbackH1 (rb₂.pullbackH1 b.value) :=
      (FpqcCover.Refinement.pullbackH1_comp rb₂ D.toRight b.value).symm
    _ = D.toRight.pullbackH1 (rc.pullbackH1 c.value) :=
      congrArg D.toRight.pullbackH1 hbc
    _ = (D.toRight.comp rc).pullbackH1 c.value :=
      FpqcCover.Refinement.pullbackH1_comp rc D.toRight c.value

def setoid :
    Setoid (PresheafFpqcH1Representative.{u, v} R G) where
  r := Equivalent R G
  iseqv :=
    { refl := equivalent_refl R G
      symm := fun h => equivalent_symm R G h
      trans := fun h₁ h₂ => equivalent_trans R G h₁ h₂ }

end PresheafFpqcH1Representative

/-- Global common-refinement fpqc Čech H¹ for an arbitrary group presheaf.
No sheaf or representability assertion is part of this definition. -/
def PresheafFpqcH1
    (R : CommRingCat.{u})
    (G : (Over (_root_.AlgebraicGeometry.Spec R))ᵒᵖ ⥤ GrpCat.{u}) :
    Type _ :=
  Quotient (PresheafFpqcH1Representative.setoid R G)

namespace PresheafFpqcH1

variable (R : CommRingCat.{u})
variable {G H J :
  (Over (_root_.AlgebraicGeometry.Spec R))ᵒᵖ ⥤ GrpCat.{u}}

def classOf (G :
    (Over (_root_.AlgebraicGeometry.Spec R))ᵒᵖ ⥤ GrpCat.{u})
    {I : Type v} (U : FpqcCover R I)
    (ξ : PresheafOfGroups.H1 G U.obj) :
    PresheafFpqcH1.{u, v} R G :=
  Quotient.mk (PresheafFpqcH1Representative.setoid R G)
    { I := I, cover := U, value := ξ }

/-- The distinguished neutral global class. -/
def neutral (G :
    (Over (_root_.AlgebraicGeometry.Spec R))ᵒᵖ ⥤ GrpCat.{u}) :
    PresheafFpqcH1.{u, v} R G :=
  classOf R G (FpqcH1.trivialCover R) 1

def mapRepresentative (η : G ⟶ H)
    (a : PresheafFpqcH1Representative.{u, v} R G) :
    PresheafFpqcH1Representative.{u, v} R H where
  I := a.I
  cover := a.cover
  value := PresheafH1.map η a.value

theorem mapRepresentative_equivalent (η : G ⟶ H)
    {a b : PresheafFpqcH1Representative.{u, v} R G}
    (h : PresheafFpqcH1Representative.Equivalent R G a b) :
    PresheafFpqcH1Representative.Equivalent R H
      (mapRepresentative R η a) (mapRepresentative R η b) := by
  rcases h with ⟨K, W, ra, rb, hab⟩
  refine ⟨K, W, ra, rb, ?_⟩
  change
    ra.pullbackH1 (PresheafH1.map η a.value) =
      rb.pullbackH1 (PresheafH1.map η b.value)
  calc
    _ = PresheafH1.map η (ra.pullbackH1 a.value) :=
      (FpqcCover.Refinement.map_pullbackH1 ra η a.value).symm
    _ = PresheafH1.map η (rb.pullbackH1 b.value) :=
      congrArg (PresheafH1.map η) hab
    _ = _ :=
      FpqcCover.Refinement.map_pullbackH1 rb η b.value

/-- A natural coefficient morphism acts on the global quotient. -/
def map (η : G ⟶ H) :
    PresheafFpqcH1.{u, v} R G →
      PresheafFpqcH1.{u, v} R H :=
  Quotient.map (mapRepresentative R η)
    (fun _ _ h => mapRepresentative_equivalent R η h)

@[simp] theorem map_classOf (η : G ⟶ H)
    {I : Type v} (U : FpqcCover R I)
    (ξ : PresheafOfGroups.H1 G U.obj) :
    map R η (classOf R G U ξ) =
      classOf R H U (PresheafH1.map η ξ) :=
  rfl

@[simp] theorem map_id :
    map R (𝟙 G) = id := by
  funext x
  refine Quotient.inductionOn x ?_
  intro a
  change classOf R G a.cover
      (PresheafH1.map (𝟙 G) a.value) =
    classOf R G a.cover a.value
  rw [PresheafH1.map_id]
  rfl

theorem map_comp (η : G ⟶ H) (θ : H ⟶ J) :
    map R (η ≫ θ) =
      map R θ ∘ map R η := by
  funext x
  refine Quotient.inductionOn x ?_
  intro a
  change classOf R J a.cover
      (PresheafH1.map (η ≫ θ) a.value) =
    classOf R J a.cover
      (PresheafH1.map θ (PresheafH1.map η a.value))
  rw [PresheafH1.map_comp]
  rfl

@[simp] theorem map_neutral (η : G ⟶ H) :
    map R η (neutral R G) = neutral R H := by
  change classOf R H (FpqcH1.trivialCover R)
      (PresheafH1.map η 1) =
    classOf R H (FpqcH1.trivialCover R) 1
  rw [PresheafH1.map_one]

def equiv (e : G ≅ H) :
    PresheafFpqcH1.{u, v} R G ≃
      PresheafFpqcH1.{u, v} R H where
  toFun := map R e.hom
  invFun := map R e.inv
  left_inv x := by
    have h := congrFun (map_comp R e.hom e.inv) x
    rw [e.hom_inv_id, map_id] at h
    exact h.symm
  right_inv x := by
    have h := congrFun (map_comp R e.inv e.hom) x
    rw [e.inv_hom_id, map_id] at h
    exact h.symm

def autAction :
    CategoryTheory.Aut G →*
      Equiv.Perm (PresheafFpqcH1.{u, v} R G) where
  toFun e := equiv R e
  map_one' := by
    apply Equiv.ext
    intro ξ
    change map R (𝟙 G) ξ = ξ
    exact congrFun (map_id R) ξ
  map_mul' e f := by
    apply Equiv.ext
    intro ξ
    change map R (e * f).hom ξ =
      map R e.hom (map R f.hom ξ)
    exact congrFun (map_comp R f.hom e.hom) ξ

def action {Γ : Type w} [Group Γ]
    (ρ : Γ →* CategoryTheory.Aut G) :
    Γ →* Equiv.Perm (PresheafFpqcH1.{u, v} R G) :=
  (autAction R).comp ρ

@[simp] theorem action_neutral {Γ : Type w} [Group Γ]
    (ρ : Γ →* CategoryTheory.Aut G) (g : Γ) :
    action R ρ g (neutral R G) = neutral R G :=
  map_neutral R (ρ g).hom

end PresheafFpqcH1

/-- Global common-refinement Čech H¹ after the point-functor adapter. -/
abbrev PointFunctorFpqcH1
    (R : CommRingCat.{u}) (P : CommRingCat.{u} ⥤ GrpCat.{u}) :
    Type _ :=
  PresheafFpqcH1.{u, v} R (pointFunctorPresheaf R P)

open RiemannResearch.LinearAlgebra.RootSystem.D4Triality
open RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn

/-- The natural diagram automorphism of the finite-equation related-triple
point functor. -/
def coefficientRelatedTriplePointOuterIso
    (σ : DiagramSymmetry) :
    coefficientRelatedTriplePointFunctor.{u} ≅
      coefficientRelatedTriplePointFunctor.{u} :=
  NatIso.ofComponents
    (fun R => (coefficientRelatedTripleOuterAction R σ).toGrpIso)
    (by
      intro R S f
      apply GrpCat.hom_ext
      apply MonoidHom.ext
      intro g
      exact
        (coefficientRelatedTripleBaseChange_relabel f.hom σ g).symm)

/-- The base-change-compatible diagram action on the finite-equation point
functor. -/
def coefficientRelatedTriplePointOuterAction :
    DiagramSymmetry →*
      CategoryTheory.Aut coefficientRelatedTriplePointFunctor.{u} where
  toFun := coefficientRelatedTriplePointOuterIso
  map_one' := by
    apply CategoryTheory.Aut.ext
    apply NatTrans.ext
    funext R
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    change coefficientRelatedTripleOuterAction R 1 g = g
    exact DFunLike.congr_fun
      ((coefficientRelatedTripleOuterAction R).map_one) g
  map_mul' σ τ := by
    apply CategoryTheory.Aut.ext
    apply NatTrans.ext
    funext R
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    change coefficientRelatedTripleOuterAction R (σ * τ) g =
      coefficientRelatedTripleOuterAction R σ
        (coefficientRelatedTripleOuterAction R τ g)
    exact DFunLike.congr_fun
      ((coefficientRelatedTripleOuterAction R).map_mul σ τ) g

/-- The finite-equation related-triple presheaf on schemes over the affine
base. -/
def coefficientRelatedTriplePresheaf (R : CommRingCat.{u}) :
    (Over (_root_.AlgebraicGeometry.Spec R))ᵒᵖ ⥤ GrpCat.{u} :=
  pointFunctorPresheaf R coefficientRelatedTriplePointFunctor

/-- The compatible diagram action on the related-triple presheaf. -/
def coefficientRelatedTriplePresheafOuterAction
    (R : CommRingCat.{u}) :
    DiagramSymmetry →*
      CategoryTheory.Aut (coefficientRelatedTriplePresheaf R) :=
  (pointFunctorPresheafAut R
    coefficientRelatedTriplePointFunctor).comp
      coefficientRelatedTriplePointOuterAction

/-- Fixed-cover fpqc Čech H¹ with coefficients in the finite-equation Zorn
related-triple presheaf. -/
abbrev CoefficientRelatedTripleFpqcCechH1
    (R : CommRingCat.{u}) {I : Type v} (U : FpqcCover R I) :=
  PointFunctorFpqcCechH1 R
    coefficientRelatedTriplePointFunctor U

/-- Global common-refinement fpqc Čech H¹ with coefficients in the
finite-equation Zorn related-triple presheaf. -/
abbrev CoefficientRelatedTripleFpqcH1
    (R : CommRingCat.{u}) : Type _ :=
  PointFunctorFpqcH1.{u, v} R
    coefficientRelatedTriplePointFunctor

/-- The diagram symmetry group acts on fixed-cover Čech H¹. -/
def coefficientRelatedTripleFixedCoverOuterAction
    (R : CommRingCat.{u}) {I : Type v} (U : FpqcCover R I) :
    DiagramSymmetry →*
      Equiv.Perm (CoefficientRelatedTripleFpqcCechH1 R U) :=
  PresheafH1.action
    (coefficientRelatedTriplePresheafOuterAction R)

@[simp] theorem coefficientRelatedTripleFixedCoverOuterAction_neutral
    (R : CommRingCat.{u}) {I : Type v} (U : FpqcCover R I)
    (σ : DiagramSymmetry) :
    coefficientRelatedTripleFixedCoverOuterAction R U σ
        (1 : CoefficientRelatedTripleFpqcCechH1 R U) =
      1 :=
  PresheafH1.action_one
    (coefficientRelatedTriplePresheafOuterAction R) σ

/-- The fixed-cover action commutes with refinement pullback. -/
theorem coefficientRelatedTripleFixedCoverOuterAction_pullback
    (R : CommRingCat.{u}) {I : Type v} {J : Type w}
    {U : FpqcCover R I} {V : FpqcCover R J}
    (r : V.Refinement U) (σ : DiagramSymmetry)
    (ξ : CoefficientRelatedTripleFpqcCechH1 R U) :
    coefficientRelatedTripleFixedCoverOuterAction R V σ
        (r.pullbackH1 ξ) =
      r.pullbackH1
        (coefficientRelatedTripleFixedCoverOuterAction R U σ ξ) :=
  FpqcCover.Refinement.map_pullbackH1 r
    ((coefficientRelatedTriplePresheafOuterAction R) σ).hom ξ

/-- The diagram symmetry group acts on the global common-refinement
Čech H¹ quotient. -/
def coefficientRelatedTripleGlobalOuterAction
    (R : CommRingCat.{u}) :
    DiagramSymmetry →*
      Equiv.Perm (CoefficientRelatedTripleFpqcH1.{u, v} R) :=
  PresheafFpqcH1.action R
    (coefficientRelatedTriplePresheafOuterAction R)

@[simp] theorem coefficientRelatedTripleGlobalOuterAction_neutral
    (R : CommRingCat.{u}) (σ : DiagramSymmetry) :
    coefficientRelatedTripleGlobalOuterAction R σ
        (PresheafFpqcH1.neutral R
          (coefficientRelatedTriplePresheaf R)) =
      PresheafFpqcH1.neutral R
        (coefficientRelatedTriplePresheaf R) :=
  PresheafFpqcH1.action_neutral R
    (coefficientRelatedTriplePresheafOuterAction R) σ

end

end RiemannResearch.AlgebraicGeometry
