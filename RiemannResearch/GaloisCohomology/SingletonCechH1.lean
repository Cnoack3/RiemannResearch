/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Sites.NonabelianCohomology.H1

/-!
# Čech cocycles for a singleton cover

Mathlib defines a nonabelian one-cochain on a family `U : ι → C` as a
natural family of values indexed by all pairs of maps into members of the
family.  For a singleton family, the Yoneda argument says that such a family
is exactly one section over `U × U`.

This file proves that argument directly for every presheaf of groups.  It
also identifies the cocycle equation with one equation over `U × U × U`,
and identifies Mathlib's cohomology relation with the usual equation over
`U × U` involving one section over `U`.

These results isolate the category-theoretic part of the comparison between
fixed-cover fpqc Čech H¹ for `Spec L → Spec K` and nonabelian Galois H¹.
The remaining specialization consists only of transporting sections through
the affine fiber-product and finite-Galois tensor decompositions.
-/

namespace RiemannResearch.GaloisCohomology

open CategoryTheory CategoryTheory.Limits

universe u v w

noncomputable section

variable {C : Type u} [Category.{v} C]
variable (P : Cᵒᵖ ⥤ GrpCat.{w}) (U : C)
variable [HasBinaryProduct U U]

/-- A section over `U × U` determines a one-cochain on the singleton family
with value `U`, by pullback along every pair of maps into `U`. -/
def singletonOneCochainOfSection
    (s : P.obj (Opposite.op (U ⨯ U))) :
    PresheafOfGroups.OneCochain P (fun _ : PUnit => U) where
  ev := fun _ _ _ a b => P.map (prod.lift a b).op s
  ev_precomp := by
    intro i j T T' φ a b
    simp only [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp,
      prod.comp_lift]

/-- Evaluate a singleton-family one-cochain at the two projections from
`U × U`.  This is its universal section. -/
def singletonOneCochainSection
    (γ : PresheafOfGroups.OneCochain P (fun _ : PUnit => U)) :
    P.obj (Opposite.op (U ⨯ U)) :=
  γ.ev PUnit.unit PUnit.unit prod.fst prod.snd

/-- Every value of a singleton-family one-cochain is the pullback of its
universal section. -/
@[simp]
theorem map_singletonOneCochainSection
    (γ : PresheafOfGroups.OneCochain P (fun _ : PUnit => U))
    {T : C} (a b : T ⟶ U) :
    P.map (prod.lift a b).op (singletonOneCochainSection P U γ) =
      γ.ev PUnit.unit PUnit.unit a b := by
  simpa only [singletonOneCochainSection, prod.lift_fst, prod.lift_snd] using
    γ.ev_precomp PUnit.unit PUnit.unit (prod.lift a b) prod.fst prod.snd

/-- Taking the universal section after constructing a one-cochain recovers
the original section. -/
@[simp]
theorem singletonOneCochainSection_ofSection
    (s : P.obj (Opposite.op (U ⨯ U))) :
    singletonOneCochainSection P U
        (singletonOneCochainOfSection P U s) = s := by
  change P.map (prod.lift prod.fst prod.snd).op s = s
  simp

/-- Constructing a one-cochain from its universal section recovers the
original one-cochain. -/
@[simp]
theorem singletonOneCochainOfSection_section
    (γ : PresheafOfGroups.OneCochain P (fun _ : PUnit => U)) :
    singletonOneCochainOfSection P U
        (singletonOneCochainSection P U γ) = γ := by
  apply PresheafOfGroups.OneCochain.ext
  funext i j T a b
  cases i
  cases j
  exact map_singletonOneCochainSection P U γ a b

/-- Multiplicative Yoneda equivalence between one-cochains for a singleton
family and sections over its double overlap. -/
def singletonOneCochainMulEquiv :
    PresheafOfGroups.OneCochain P (fun _ : PUnit => U) ≃*
      P.obj (Opposite.op (U ⨯ U)) where
  toFun := singletonOneCochainSection P U
  invFun := singletonOneCochainOfSection P U
  left_inv := singletonOneCochainOfSection_section P U
  right_inv := singletonOneCochainSection_ofSection P U
  map_mul' := by
    intro γ δ
    rfl

/-- Multiplicative equivalence between zero-cochains for a singleton family
and sections over its sole member. -/
def singletonZeroCochainMulEquiv :
    PresheafOfGroups.ZeroCochain P (fun _ : PUnit => U) ≃*
      P.obj (Opposite.op U) where
  toFun := fun α => α PUnit.unit
  invFun := fun g _ => g
  left_inv := by
    intro α
    funext i
    cases i
    rfl
  right_inv := by
    intro g
    rfl
  map_mul' := by
    intro α β
    rfl

/-- On a singleton family, Mathlib's relation between two one-cochains is
equivalent to its single universal equation over the double overlap. -/
theorem singleton_oneCohomologyRelation_iff
    (γ₁ γ₂ : PresheafOfGroups.OneCochain P (fun _ : PUnit => U))
    (α : PresheafOfGroups.ZeroCochain P (fun _ : PUnit => U)) :
    PresheafOfGroups.OneCohomologyRelation γ₁ γ₂ α ↔
      P.map prod.fst.op (α PUnit.unit) *
          singletonOneCochainSection P U γ₁ =
        singletonOneCochainSection P U γ₂ *
          P.map prod.snd.op (α PUnit.unit) := by
  constructor
  · intro h
    exact h PUnit.unit PUnit.unit prod.fst prod.snd
  · intro h i j T a b
    cases i
    cases j
    let ℓ : T ⟶ U ⨯ U := prod.lift a b
    have h' := congrArg (fun z => P.map ℓ.op z) h
    have hf :
        P.map ℓ.op (P.map prod.fst.op (α PUnit.unit)) =
          P.map a.op (α PUnit.unit) := by
      simp only [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp,
        ℓ, prod.lift_fst]
    have hs :
        P.map ℓ.op (P.map prod.snd.op (α PUnit.unit)) =
          P.map b.op (α PUnit.unit) := by
      simp only [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp,
        ℓ, prod.lift_snd]
    simpa only [map_mul, hf, hs, ℓ,
      map_singletonOneCochainSection] using h'

/-- Two singleton-family cocycles are cohomologous exactly when their
universal sections differ by one universal zero-cochain section. -/
theorem singleton_isCohomologous_iff
    (γ₁ γ₂ : PresheafOfGroups.OneCocycle P (fun _ : PUnit => U)) :
    γ₁.IsCohomologous γ₂ ↔
      ∃ g : P.obj (Opposite.op U),
        P.map prod.fst.op g *
            singletonOneCochainSection P U γ₁.toOneCochain =
          singletonOneCochainSection P U γ₂.toOneCochain *
            P.map prod.snd.op g := by
  constructor
  · rintro ⟨α, hα⟩
    exact ⟨α PUnit.unit,
      (singleton_oneCohomologyRelation_iff P U _ _ α).mp hα⟩
  · rintro ⟨g, hg⟩
    let α : PresheafOfGroups.ZeroCochain P (fun _ : PUnit => U) :=
      fun _ => g
    exact ⟨α,
      (singleton_oneCohomologyRelation_iff P U _ _ α).mpr hg⟩

variable [HasBinaryProduct (U ⨯ U) U]

/-- Projection to the zeroth factor of the chosen left-associated triple
product `(U × U) × U`. -/
def singletonTripleProj0 : (U ⨯ U) ⨯ U ⟶ U :=
  prod.fst ≫ prod.fst

/-- Projection to the first factor of the chosen left-associated triple
product `(U × U) × U`. -/
def singletonTripleProj1 : (U ⨯ U) ⨯ U ⟶ U :=
  prod.fst ≫ prod.snd

/-- Projection to the second factor of the chosen left-associated triple
product `(U × U) × U`. -/
def singletonTripleProj2 : (U ⨯ U) ⨯ U ⟶ U :=
  prod.snd

/-- The zero-one face from the triple overlap to the double overlap. -/
def singletonTripleFace01 : (U ⨯ U) ⨯ U ⟶ U ⨯ U :=
  prod.lift (singletonTripleProj0 U) (singletonTripleProj1 U)

/-- The one-two face from the triple overlap to the double overlap. -/
def singletonTripleFace12 : (U ⨯ U) ⨯ U ⟶ U ⨯ U :=
  prod.lift (singletonTripleProj1 U) (singletonTripleProj2 U)

/-- The zero-two face from the triple overlap to the double overlap. -/
def singletonTripleFace02 : (U ⨯ U) ⨯ U ⟶ U ⨯ U :=
  prod.lift (singletonTripleProj0 U) (singletonTripleProj2 U)

variable [HasBinaryProduct U (U ⨯ U)]

/-- The canonical reassociation from the left-associated singleton triple
overlap to the right-associated triple overlap used by tensor coordinates. -/
def singletonTripleAssociatorIso :
    ((U ⨯ U) ⨯ U) ≅ (U ⨯ (U ⨯ U)) where
  hom :=
    prod.lift (prod.fst ≫ prod.fst)
      (prod.lift (prod.fst ≫ prod.snd) prod.snd)
  inv :=
    prod.lift (prod.lift prod.fst (prod.snd ≫ prod.fst))
      (prod.snd ≫ prod.snd)
  hom_inv_id := by
    ext <;> simp only [prod.lift_snd_assoc, prod.lift_fst,
      prod.lift_snd, prod.comp_lift, Category.id_comp]
  inv_hom_id := by
    ext <;> simp only [prod.lift_fst_assoc, prod.lift_fst,
      prod.lift_snd, prod.comp_lift, Category.id_comp]

/-- Projection to the zeroth factor of `U × (U × U)`. -/
def singletonRightTripleProj0 : U ⨯ (U ⨯ U) ⟶ U :=
  prod.fst

/-- Projection to the first factor of `U × (U × U)`. -/
def singletonRightTripleProj1 : U ⨯ (U ⨯ U) ⟶ U :=
  prod.snd ≫ prod.fst

/-- Projection to the second factor of `U × (U × U)`. -/
def singletonRightTripleProj2 : U ⨯ (U ⨯ U) ⟶ U :=
  prod.snd ≫ prod.snd

/-- The zero-one face on the right-associated triple overlap. -/
def singletonRightTripleFace01 : U ⨯ (U ⨯ U) ⟶ U ⨯ U :=
  prod.lift (singletonRightTripleProj0 U) (singletonRightTripleProj1 U)

/-- The one-two face on the right-associated triple overlap. -/
def singletonRightTripleFace12 : U ⨯ (U ⨯ U) ⟶ U ⨯ U :=
  prod.lift (singletonRightTripleProj1 U) (singletonRightTripleProj2 U)

/-- The zero-two face on the right-associated triple overlap. -/
def singletonRightTripleFace02 : U ⨯ (U ⨯ U) ⟶ U ⨯ U :=
  prod.lift (singletonRightTripleProj0 U) (singletonRightTripleProj2 U)

/-- Reassociation carries the right-associated zero-one face to the
left-associated zero-one face. -/
@[simp]
theorem singletonTripleAssociatorIso_hom_comp_rightFace01 :
    (singletonTripleAssociatorIso U).hom ≫ singletonRightTripleFace01 U =
      singletonTripleFace01 U := by
  ext <;> simp only [singletonTripleAssociatorIso,
    singletonRightTripleFace01, singletonRightTripleProj0,
    singletonRightTripleProj1, singletonTripleFace01,
    singletonTripleProj0, singletonTripleProj1, prod.lift_snd_assoc,
    prod.lift_fst, prod.lift_snd, prod.comp_lift]

/-- Reassociation carries the right-associated one-two face to the
left-associated one-two face. -/
@[simp]
theorem singletonTripleAssociatorIso_hom_comp_rightFace12 :
    (singletonTripleAssociatorIso U).hom ≫ singletonRightTripleFace12 U =
      singletonTripleFace12 U := by
  ext <;> simp only [singletonTripleAssociatorIso,
    singletonRightTripleFace12, singletonRightTripleProj1,
    singletonRightTripleProj2, singletonTripleFace12,
    singletonTripleProj1, singletonTripleProj2, prod.lift_snd_assoc,
    prod.lift_fst, prod.lift_snd, prod.comp_lift]

/-- Reassociation carries the right-associated zero-two face to the
left-associated zero-two face. -/
@[simp]
theorem singletonTripleAssociatorIso_hom_comp_rightFace02 :
    (singletonTripleAssociatorIso U).hom ≫ singletonRightTripleFace02 U =
      singletonTripleFace02 U := by
  ext <;> simp only [singletonTripleAssociatorIso,
    singletonRightTripleFace02, singletonRightTripleProj0,
    singletonRightTripleProj2, singletonTripleFace02,
    singletonTripleProj0, singletonTripleProj2, prod.lift_snd_assoc,
    prod.lift_fst, prod.lift_snd, prod.comp_lift]

/-- Inverse reassociation carries the left-associated zero-one face to the
right-associated zero-one face. -/
@[simp]
theorem singletonTripleAssociatorIso_inv_comp_face01 :
    (singletonTripleAssociatorIso U).inv ≫ singletonTripleFace01 U =
      singletonRightTripleFace01 U := by
  rw [← singletonTripleAssociatorIso_hom_comp_rightFace01 U,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Inverse reassociation carries the left-associated one-two face to the
right-associated one-two face. -/
@[simp]
theorem singletonTripleAssociatorIso_inv_comp_face12 :
    (singletonTripleAssociatorIso U).inv ≫ singletonTripleFace12 U =
      singletonRightTripleFace12 U := by
  rw [← singletonTripleAssociatorIso_hom_comp_rightFace12 U,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Inverse reassociation carries the left-associated zero-two face to the
right-associated zero-two face. -/
@[simp]
theorem singletonTripleAssociatorIso_inv_comp_face02 :
    (singletonTripleAssociatorIso U).inv ≫ singletonTripleFace02 U =
      singletonRightTripleFace02 U := by
  rw [← singletonTripleAssociatorIso_hom_comp_rightFace02 U,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The singleton Čech cocycle equation is independent of whether the triple
overlap is parenthesized as `(U × U) × U` or `U × (U × U)`. -/
theorem singletonCocycleCondition_iff_rightAssociated
    (s : P.obj (Opposite.op (U ⨯ U))) :
    P.map (singletonTripleFace01 U).op s *
          P.map (singletonTripleFace12 U).op s =
        P.map (singletonTripleFace02 U).op s ↔
      P.map (singletonRightTripleFace01 U).op s *
          P.map (singletonRightTripleFace12 U).op s =
        P.map (singletonRightTripleFace02 U).op s := by
  constructor
  · intro h
    have h' := congrArg
      (fun z => P.map (singletonTripleAssociatorIso U).inv.op z) h
    simpa only [map_mul, ← ConcreteCategory.comp_apply, ← P.map_comp,
      ← op_comp, singletonTripleAssociatorIso_inv_comp_face01,
      singletonTripleAssociatorIso_inv_comp_face12,
      singletonTripleAssociatorIso_inv_comp_face02] using h'
  · intro h
    have h' := congrArg
      (fun z => P.map (singletonTripleAssociatorIso U).hom.op z) h
    simpa only [map_mul, ← ConcreteCategory.comp_apply, ← P.map_comp,
      ← op_comp, singletonTripleAssociatorIso_hom_comp_rightFace01,
      singletonTripleAssociatorIso_hom_comp_rightFace12,
      singletonTripleAssociatorIso_hom_comp_rightFace02] using h'

/-- A section on the double overlap satisfying the single universal
triple-overlap cocycle equation. -/
@[ext]
structure SingletonCocycleSection where
  /-- The section on `U × U`. -/
  val : P.obj (Opposite.op (U ⨯ U))
  /-- The cocycle equation after pullback to `(U × U) × U`. -/
  cocycle_condition :
    P.map (singletonTripleFace01 U).op val *
        P.map (singletonTripleFace12 U).op val =
      P.map (singletonTripleFace02 U).op val

/-- Send a Mathlib one-cocycle on a singleton family to its universal section
on the double overlap. -/
def singletonOneCocycleToSection
    (γ : PresheafOfGroups.OneCocycle P (fun _ : PUnit => U)) :
    SingletonCocycleSection P U where
  val := singletonOneCochainSection P U γ.toOneCochain
  cocycle_condition := by
    simpa only [singletonTripleFace01, singletonTripleFace12,
      singletonTripleFace02, map_singletonOneCochainSection] using
      γ.ev_trans PUnit.unit PUnit.unit PUnit.unit
        (singletonTripleProj0 U) (singletonTripleProj1 U)
        (singletonTripleProj2 U)

/-- Construct a Mathlib one-cocycle from a section satisfying the universal
triple-overlap equation. -/
def singletonOneCocycleOfSection
    (s : SingletonCocycleSection P U) :
    PresheafOfGroups.OneCocycle P (fun _ : PUnit => U) where
  toOneCochain := singletonOneCochainOfSection P U s.val
  ev_trans := by
    intro i j k T a b c
    cases i
    cases j
    cases k
    let ℓ : T ⟶ (U ⨯ U) ⨯ U := prod.lift (prod.lift a b) c
    have h := congrArg (fun z => P.map ℓ.op z) s.cocycle_condition
    change
      P.map (prod.lift a b).op s.val *
          P.map (prod.lift b c).op s.val =
        P.map (prod.lift a c).op s.val
    simpa only [map_mul, ← ConcreteCategory.comp_apply, ← P.map_comp,
      ← op_comp, ℓ, singletonTripleFace01, singletonTripleFace12,
      singletonTripleFace02, singletonTripleProj0, singletonTripleProj1,
      singletonTripleProj2, prod.comp_lift, Category.assoc,
      prod.lift_fst_assoc, prod.lift_snd_assoc, prod.lift_fst,
      prod.lift_snd] using h

omit [HasBinaryProduct U U] [HasBinaryProduct (U ⨯ U) U] in
/-- Extensionality for Mathlib one-cocycles through their one-cochain field. -/
theorem singletonOneCocycle_ext
    {γ δ : PresheafOfGroups.OneCocycle P (fun _ : PUnit => U)}
    (h : γ.toOneCochain = δ.toOneCochain) : γ = δ := by
  cases γ
  cases δ
  simpa only [PresheafOfGroups.OneCocycle.mk.injEq] using h

/-- Yoneda equivalence between Mathlib one-cocycles for a singleton family
and sections on the double overlap satisfying one equation on the triple
overlap. -/
def singletonOneCocycleEquiv :
    PresheafOfGroups.OneCocycle P (fun _ : PUnit => U) ≃
      SingletonCocycleSection P U where
  toFun := singletonOneCocycleToSection P U
  invFun := singletonOneCocycleOfSection P U
  left_inv := by
    intro γ
    apply singletonOneCocycle_ext P U
    exact singletonOneCochainOfSection_section P U γ.toOneCochain
  right_inv := by
    rintro ⟨s, hs⟩
    apply SingletonCocycleSection.ext
    change P.map (prod.lift prod.fst prod.snd).op s = s
    simp

end

end RiemannResearch.GaloisCohomology
