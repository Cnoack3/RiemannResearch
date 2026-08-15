/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.FpqcH1

/-!
# Coefficient functoriality of nonabelian fpqc Cech H1

A natural transformation of presheaves of groups maps zero-cochains,
one-cocycles, the nonabelian cohomology relation, and fixed-cover H1.
Natural isomorphisms therefore induce equivalences on H1. The map commutes
with refinement pullback, which is the key fact needed to descend an affine
group-scheme automorphism to the global common-refinement quotient.

This is coefficient functoriality. It does not construct a coordinate Hopf
algebra or an automorphism of a particular reductive group scheme.
-/

namespace RiemannResearch.AlgebraicGeometry

open CategoryTheory

universe u v w

noncomputable section

namespace PresheafH1

variable {C : Type u} [Category.{v, u} C]
variable {G H J : Cᵒᵖ ⥤ GrpCat}
variable {I : Type w} {U : I → C}

def mapZeroCochain (η : G ⟶ H)
    (α : PresheafOfGroups.ZeroCochain G U) :
    PresheafOfGroups.ZeroCochain H U :=
  fun i => (η.app (Opposite.op (U i))).hom (α i)

def mapOneCochain (η : G ⟶ H)
    (γ : PresheafOfGroups.OneCochain G U) :
    PresheafOfGroups.OneCochain H U where
  ev i j T a b :=
    (η.app (Opposite.op T)).hom (γ.ev i j a b)
  ev_precomp i j T T' φ a b := by
    change
      (H.map φ.op).hom
          ((η.app (Opposite.op T')).hom (γ.ev i j a b)) =
        (η.app (Opposite.op T)).hom
          (γ.ev i j (φ ≫ a) (φ ≫ b))
    calc
      _ = ConcreteCategory.hom
          (η.app (Opposite.op T') ≫ H.map φ.op)
          (γ.ev i j a b) := by rw [GrpCat.comp_apply]
      _ = ConcreteCategory.hom
          (G.map φ.op ≫ η.app (Opposite.op T))
          (γ.ev i j a b) :=
        ConcreteCategory.congr_hom (η.naturality φ.op).symm _
      _ = (η.app (Opposite.op T)).hom
          ((G.map φ.op).hom (γ.ev i j a b)) := by
        rw [GrpCat.comp_apply]
      _ = _ := congrArg (η.app (Opposite.op T)).hom
        (γ.ev_precomp i j φ a b)

def mapOneCocycle (η : G ⟶ H)
    (γ : PresheafOfGroups.OneCocycle G U) :
    PresheafOfGroups.OneCocycle H U where
  toOneCochain := mapOneCochain η γ.toOneCochain
  ev_trans i j k T a b c := by
    change
      (η.app (Opposite.op T)).hom (γ.ev i j a b) *
          (η.app (Opposite.op T)).hom (γ.ev j k b c) =
        (η.app (Opposite.op T)).hom (γ.ev i k a c)
    rw [← map_mul, γ.ev_trans]

theorem cocycle_ext
    {γ δ : PresheafOfGroups.OneCocycle G U}
    (h : γ.toOneCochain = δ.toOneCochain) : γ = δ := by
  cases γ
  cases δ
  cases h
  rfl

theorem naturality_apply (η : G ⟶ H) {X Y : Cᵒᵖ}
    (f : X ⟶ Y) (g : G.obj X) :
    (H.map f).hom ((η.app X).hom g) =
      (η.app Y).hom ((G.map f).hom g) := by
  calc
    _ = ConcreteCategory.hom (η.app X ≫ H.map f) g := by
      rw [GrpCat.comp_apply]
    _ = ConcreteCategory.hom (G.map f ≫ η.app Y) g :=
      ConcreteCategory.congr_hom (η.naturality f).symm g
    _ = _ := by rw [GrpCat.comp_apply]

theorem map_isCohomologous (η : G ⟶ H)
    {γ₁ γ₂ : PresheafOfGroups.OneCocycle G U}
    (h : γ₁.IsCohomologous γ₂) :
    (mapOneCocycle η γ₁).IsCohomologous
      (mapOneCocycle η γ₂) := by
  rcases h with ⟨α, hα⟩
  refine ⟨mapZeroCochain η α, ?_⟩
  intro i j T a b
  change
    (H.map a.op).hom
          ((η.app (Opposite.op (U i))).hom (α i)) *
        (η.app (Opposite.op T)).hom (γ₁.ev i j a b) =
      (η.app (Opposite.op T)).hom (γ₂.ev i j a b) *
        (H.map b.op).hom
          ((η.app (Opposite.op (U j))).hom (α j))
  rw [naturality_apply, naturality_apply]
  rw [← map_mul, ← map_mul, hα i j a b]

def map (η : G ⟶ H) :
    PresheafOfGroups.H1 G U → PresheafOfGroups.H1 H U :=
  Quot.map (mapOneCocycle η) fun _ _ =>
    map_isCohomologous η

theorem mapOneCocycle_id
    (γ : PresheafOfGroups.OneCocycle G U) :
    mapOneCocycle (𝟙 G) γ = γ := by
  apply cocycle_ext
  apply PresheafOfGroups.OneCochain.ext
  funext i j T a b
  rfl

theorem mapOneCocycle_comp (η : G ⟶ H) (θ : H ⟶ J)
    (γ : PresheafOfGroups.OneCocycle G U) :
    mapOneCocycle (η ≫ θ) γ =
      mapOneCocycle θ (mapOneCocycle η γ) := by
  apply cocycle_ext
  apply PresheafOfGroups.OneCochain.ext
  funext i j T a b
  rfl

@[simp] theorem map_id :
    map (U := U) (𝟙 G) = id := by
  funext ξ
  refine Quot.inductionOn ξ ?_
  intro γ
  exact congrArg PresheafOfGroups.OneCocycle.class
    (mapOneCocycle_id γ)

theorem map_comp (η : G ⟶ H) (θ : H ⟶ J) :
    map (U := U) (η ≫ θ) =
      map θ ∘ map η := by
  funext ξ
  refine Quot.inductionOn ξ ?_
  intro γ
  exact congrArg PresheafOfGroups.OneCocycle.class
    (mapOneCocycle_comp η θ γ)

theorem mapOneCocycle_one (η : G ⟶ H) :
    mapOneCocycle (U := U) η 1 = 1 := by
  apply cocycle_ext
  apply PresheafOfGroups.OneCochain.ext
  funext i j T a b
  exact map_one (η.app (Opposite.op T)).hom

@[simp] theorem map_one (η : G ⟶ H) :
    map (U := U) η 1 = 1 := by
  exact congrArg PresheafOfGroups.OneCocycle.class
    (mapOneCocycle_one (U := U) η)

def equiv (e : G ≅ H) :
    PresheafOfGroups.H1 G U ≃ PresheafOfGroups.H1 H U where
  toFun := map e.hom
  invFun := map e.inv
  left_inv ξ := by
    have h := congrFun (map_comp (U := U) e.hom e.inv) ξ
    rw [e.hom_inv_id, map_id] at h
    exact h.symm
  right_inv ξ := by
    have h := congrFun (map_comp (U := U) e.inv e.hom) ξ
    rw [e.inv_hom_id, map_id] at h
    exact h.symm

end PresheafH1

namespace FpqcCover.Refinement

variable {R : CommRingCat.{u}} {I : Type v} {J : Type w}
variable {U : FpqcCover R I} {V : FpqcCover R J}
variable (r : V.Refinement U)
variable
  {G H : (Over (_root_.AlgebraicGeometry.Spec R))ᵒᵖ ⥤ GrpCat}

theorem map_pullbackH1 (η : G ⟶ H)
    (ξ : PresheafOfGroups.H1 G U.obj) :
    PresheafH1.map η (r.pullbackH1 ξ) =
      r.pullbackH1 (PresheafH1.map η ξ) := by
  refine Quot.inductionOn ξ ?_
  intro γ
  change
    (PresheafH1.mapOneCocycle η
      (pullbackOneCocycle r γ)).class =
      (pullbackOneCocycle r
        (PresheafH1.mapOneCocycle η γ)).class
  apply congrArg PresheafOfGroups.OneCocycle.class
  apply PresheafH1.cocycle_ext
  apply PresheafOfGroups.OneCochain.ext
  funext j k T a b
  rfl

end FpqcCover.Refinement

namespace FpqcH1

variable {R A : CommRingCat.{u}} [HopfAlgebra R A]

/-- Apply a coefficient endomorphism to the cohomology class carried by one
global representative, without changing its witnessed cover. -/
def mapRepresentative
    (η : affineGroupPresheaf R A ⟶ affineGroupPresheaf R A)
    (a : FpqcH1Representative.{u, v} R A) :
    FpqcH1Representative.{u, v} R A where
  I := a.I
  cover := a.cover
  value := PresheafH1.map η a.value

/-- Coefficient maps preserve equality after common refinement. -/
theorem mapRepresentative_equivalent
    (η : affineGroupPresheaf R A ⟶ affineGroupPresheaf R A)
    {a b : FpqcH1Representative.{u, v} R A}
    (h : FpqcH1Representative.Equivalent R A a b) :
    FpqcH1Representative.Equivalent R A
      (mapRepresentative η a) (mapRepresentative η b) := by
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

/-- A natural endomorphism of a represented affine group presheaf acts on
global common-refinement fpqc Cech H1. -/
def map
    (η : affineGroupPresheaf R A ⟶ affineGroupPresheaf R A) :
    FpqcH1.{u, v} R A → FpqcH1.{u, v} R A :=
  Quotient.map (mapRepresentative η)
    (fun _ _ h => mapRepresentative_equivalent η h)

@[simp] theorem map_classOf
    (η : affineGroupPresheaf R A ⟶ affineGroupPresheaf R A)
    {I : Type v} (U : FpqcCover R I) (ξ : FpqcCechH1 R A U) :
    map η (classOf R A U ξ) =
      classOf R A U (PresheafH1.map η ξ) :=
  rfl

/-- The identity coefficient map acts identically on global fpqc H1. -/
@[simp] theorem map_id :
    map (R := R) (A := A)
      (𝟙 (affineGroupPresheaf R A)) = id := by
  funext x
  refine Quotient.inductionOn x ?_
  intro a
  change classOf R A a.cover
      (PresheafH1.map
        (𝟙 (affineGroupPresheaf R A)) a.value) =
    classOf R A a.cover a.value
  rw [PresheafH1.map_id]
  rfl

/-- Global coefficient maps compose in function-composition order. -/
theorem map_comp
    (η θ : affineGroupPresheaf R A ⟶ affineGroupPresheaf R A) :
    map (η ≫ θ) = map θ ∘ map η := by
  funext x
  refine Quotient.inductionOn x ?_
  intro a
  change classOf R A a.cover
      (PresheafH1.map (η ≫ θ) a.value) =
    classOf R A a.cover
      (PresheafH1.map θ (PresheafH1.map η a.value))
  rw [PresheafH1.map_comp]
  rfl

/-- Every coefficient endomorphism fixes the global neutral class. -/
@[simp] theorem map_neutral
    (η : affineGroupPresheaf R A ⟶ affineGroupPresheaf R A) :
    map η (neutral R A) = neutral R A := by
  rw [neutral, map_classOf]
  apply congrArg (classOf R A (trivialCover R))
  change PresheafH1.map η
      (1 : FpqcCechH1 R A (trivialCover R)) = 1
  exact PresheafH1.map_one η

/-- A natural automorphism of the represented affine group presheaf induces
an equivalence of global fpqc H1. -/
def equiv
    (e : affineGroupPresheaf R A ≅ affineGroupPresheaf R A) :
    FpqcH1.{u, v} R A ≃ FpqcH1.{u, v} R A where
  toFun := map e.hom
  invFun := map e.inv
  left_inv x := by
    have h := congrFun (map_comp e.hom e.inv) x
    rw [e.hom_inv_id, map_id] at h
    exact h.symm
  right_inv x := by
    have h := congrFun (map_comp e.inv e.hom) x
    rw [e.inv_hom_id, map_id] at h
    exact h.symm

end FpqcH1

end

end RiemannResearch.AlgebraicGeometry


namespace RiemannResearch.AlgebraicGeometry

open CategoryTheory

universe u v w

noncomputable section

namespace PresheafH1

variable {C : Type u} [Category.{v, u} C]
variable {G : Cᵒᵖ ⥤ GrpCat}
variable {I : Type w} {U : I → C}

/-- Every natural automorphism of a presheaf of groups acts on its
nonabelian Cech H1. -/
def autAction :
    CategoryTheory.Aut G →* Equiv.Perm (PresheafOfGroups.H1 G U) where
  toFun e := equiv e
  map_one' := by
    apply Equiv.ext
    intro ξ
    change map (𝟙 G) ξ = ξ
    exact congrFun map_id ξ
  map_mul' e f := by
    apply Equiv.ext
    intro ξ
    change map (e * f).hom ξ =
      map e.hom (map f.hom ξ)
    exact congrFun (map_comp f.hom e.hom) ξ

/-- Any group action by presheaf automorphisms acts on fixed-cover H1. -/
def action {Γ : Type*} [Group Γ]
    (ρ : Γ →* CategoryTheory.Aut G) :
    Γ →* Equiv.Perm (PresheafOfGroups.H1 G U) :=
  autAction.comp ρ

@[simp] theorem action_one {Γ : Type*} [Group Γ]
    (ρ : Γ →* CategoryTheory.Aut G) (g : Γ) :
    action (U := U) ρ g (1 : PresheafOfGroups.H1 G U) = 1 :=
  map_one (ρ g).hom

end PresheafH1

namespace FpqcH1

variable {R A : CommRingCat.{u}} [HopfAlgebra R A]

/-- Natural automorphisms of a represented affine group presheaf act on the
global common-refinement fpqc H1 quotient. -/
def autAction :
    CategoryTheory.Aut (affineGroupPresheaf R A) →*
      Equiv.Perm (FpqcH1.{u, v} R A) where
  toFun e := equiv e
  map_one' := by
    apply Equiv.ext
    intro ξ
    change map (𝟙 (affineGroupPresheaf R A)) ξ = ξ
    exact congrFun map_id ξ
  map_mul' e f := by
    apply Equiv.ext
    intro ξ
    change map (e * f).hom ξ =
      map e.hom (map f.hom ξ)
    exact congrFun (map_comp f.hom e.hom) ξ

/-- Any action on a represented affine group presheaf descends to global
common-refinement fpqc H1. -/
def action {Γ : Type w} [Group Γ]
    (ρ : Γ →* CategoryTheory.Aut (affineGroupPresheaf R A)) :
    Γ →* Equiv.Perm (FpqcH1.{u, v} R A) :=
  autAction.comp ρ

@[simp] theorem action_neutral {Γ : Type w} [Group Γ]
    (ρ : Γ →* CategoryTheory.Aut (affineGroupPresheaf R A))
    (g : Γ) :
    action ρ g (neutral R A) = neutral R A :=
  map_neutral (ρ g).hom

end FpqcH1

end

end RiemannResearch.AlgebraicGeometry
