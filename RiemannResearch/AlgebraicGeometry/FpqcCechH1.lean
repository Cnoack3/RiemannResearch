/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.NonabelianCohomology.H1

/-!
# Fixed-cover fpqc nonabelian Čech H¹

This module packages an indexed fpqc covering family of an affine base
`Spec R`, and defines the nonabelian Čech `H¹` of an affine group scheme on
that fixed cover using Mathlib's `PresheafOfGroups.H1`.

This is deliberately fixed-cover cohomology. It is not yet the colimit over
all fpqc covers and refinements, nor a classification of fpqc torsors.
-/

namespace RiemannResearch.AlgebraicGeometry

open CategoryTheory

universe u v w

noncomputable section

/-- An indexed family in `Over (Spec R)` whose underlying scheme morphisms
form a cover in Mathlib's fpqc precoverage. -/
structure FpqcCover (R : CommRingCat.{u}) (I : Type v) where
  /-- The covering objects, including their structure morphisms to `Spec R`. -/
  obj : I → Over (_root_.AlgebraicGeometry.Spec R)
  /-- The assertion that the underlying arrow family is fpqc-covering. -/
  mem_fpqc :
    Presieve.ofArrows (fun i => (obj i).left) (fun i => (obj i).hom) ∈
      _root_.AlgebraicGeometry.Scheme.fpqcPrecoverage.coverings
        (_root_.AlgebraicGeometry.Spec R)

namespace FpqcCover

/-- A flat, surjective, quasi-compact morphism to `Spec R`, regarded as a
singleton fpqc cover. -/
def singleton {R : CommRingCat.{u}}
    {X : _root_.AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ _root_.AlgebraicGeometry.Spec R)
    [_root_.AlgebraicGeometry.Flat f]
    [_root_.AlgebraicGeometry.Surjective f]
    [_root_.AlgebraicGeometry.QuasiCompact f] :
    FpqcCover R PUnit where
  obj := fun _ => Over.mk f
  mem_fpqc := by
    change
      Presieve.ofArrows (fun _ : PUnit => X) (fun _ => f) ∈
        _root_.AlgebraicGeometry.Scheme.fpqcPrecoverage.coverings
          (_root_.AlgebraicGeometry.Spec R)
    rw [Presieve.ofArrows_pUnit]
    exact _root_.AlgebraicGeometry.Scheme.Hom.singleton_mem_fpqcPrecoverage f

/-- A refinement of fpqc covering families. Each object of `V` maps over the
base to a selected object of `U`. -/
structure Refinement {R : CommRingCat.{u}} {I : Type v} {J : Type w}
    (V : FpqcCover R J) (U : FpqcCover R I) where
  /-- The selected old index for each refined covering object. -/
  index : J → I
  /-- The refining morphism over `Spec R`. -/
  hom : ∀ j, V.obj j ⟶ U.obj (index j)

namespace Refinement

variable {R : CommRingCat.{u}} {I : Type v} {J : Type w}
variable {U : FpqcCover R I} {V : FpqcCover R J}
variable (r : V.Refinement U)
variable {G : (Over (_root_.AlgebraicGeometry.Spec R))ᵒᵖ ⥤ GrpCat}

/-- Pull a nonabelian one-cochain back along a refinement. -/
def pullbackOneCochain
    (γ : PresheafOfGroups.OneCochain G U.obj) :
    PresheafOfGroups.OneCochain G V.obj where
  ev := fun j k {T} a b =>
    γ.ev (r.index j) (r.index k) (a ≫ r.hom j) (b ≫ r.hom k)
  ev_precomp := by
    intro j k T T' φ a b
    simpa only [Category.assoc] using
      γ.ev_precomp (r.index j) (r.index k) φ
        (a ≫ r.hom j) (b ≫ r.hom k)

/-- Pull a nonabelian one-cocycle back along a refinement. -/
def pullbackOneCocycle
    (γ : PresheafOfGroups.OneCocycle G U.obj) :
    PresheafOfGroups.OneCocycle G V.obj where
  toOneCochain := pullbackOneCochain r γ.toOneCochain
  ev_trans := by
    intro j k l T a b c
    exact γ.ev_trans (r.index j) (r.index k) (r.index l)
      (a ≫ r.hom j) (b ≫ r.hom k) (c ≫ r.hom l)

/-- Pull a zero-cochain back along a refinement. -/
def pullbackZeroCochain
    (α : PresheafOfGroups.ZeroCochain G U.obj) :
    PresheafOfGroups.ZeroCochain G V.obj :=
  fun j => G.map (r.hom j).op (α (r.index j))

/-- Pullback along a refinement preserves the nonabelian cohomology relation. -/
theorem pullback_oneCohomologyRelation
    {γ₁ γ₂ : PresheafOfGroups.OneCocycle G U.obj}
    {α : PresheafOfGroups.ZeroCochain G U.obj}
    (h : PresheafOfGroups.OneCohomologyRelation
      γ₁.toOneCochain γ₂.toOneCochain α) :
    PresheafOfGroups.OneCohomologyRelation
      (pullbackOneCocycle r γ₁).toOneCochain
      (pullbackOneCocycle r γ₂).toOneCochain
      (pullbackZeroCochain r α) := by
  intro j k T a b
  simpa only [pullbackOneCocycle, pullbackOneCochain,
    pullbackZeroCochain, ← ConcreteCategory.comp_apply,
    ← G.map_comp, ← op_comp] using
    h (r.index j) (r.index k) (a ≫ r.hom j) (b ≫ r.hom k)

/-- Pullback along a refinement preserves cohomologous one-cocycles. -/
theorem pullback_isCohomologous
    {γ₁ γ₂ : PresheafOfGroups.OneCocycle G U.obj}
    (h : γ₁.IsCohomologous γ₂) :
    (pullbackOneCocycle r γ₁).IsCohomologous
      (pullbackOneCocycle r γ₂) := by
  rcases h with ⟨α, hα⟩
  exact ⟨pullbackZeroCochain r α, pullback_oneCohomologyRelation r hα⟩

/-- The map on fixed-cover nonabelian `H¹` induced by a refinement. -/
def pullbackH1 :
    PresheafOfGroups.H1 G U.obj → PresheafOfGroups.H1 G V.obj :=
  Quot.lift
    (fun γ => (pullbackOneCocycle r γ).class)
    (fun _ _ h => (pullback_isCohomologous r h).class_eq)

/-- Refinement pullback sends a cocycle class to the class of the pulled-back
cocycle. -/
@[simp] theorem pullbackH1_class
    (γ : PresheafOfGroups.OneCocycle G U.obj) :
    pullbackH1 r γ.class = (pullbackOneCocycle r γ).class :=
  rfl

/-- Refinement pullback preserves the distinguished neutral class. -/
@[simp] theorem pullbackH1_one :
    pullbackH1 r (1 : PresheafOfGroups.H1 G U.obj) =
      (1 : PresheafOfGroups.H1 G V.obj) := by
  rfl

end Refinement
end FpqcCover

/-- The presheaf of groups represented by the affine group scheme
`Spec A → Spec R` associated to a Hopf algebra `A` over `R`. -/
abbrev affineGroupPresheaf (R A : CommRingCat.{u}) [HopfAlgebra R A] :
    (Over (_root_.AlgebraicGeometry.Spec R))ᵒᵖ ⥤ GrpCat :=
  yonedaGrpObj
    ((_root_.AlgebraicGeometry.Spec A).asOver
      (_root_.AlgebraicGeometry.Spec R))

/-- Nonabelian Čech `H¹` of the affine group scheme `Spec A → Spec R` on
the fixed fpqc cover `U`. -/
abbrev FpqcCechH1 (R A : CommRingCat.{u}) [HopfAlgebra R A]
    {I : Type v} (U : FpqcCover R I) : Type _ :=
  PresheafOfGroups.H1 (affineGroupPresheaf R A) U.obj

namespace FpqcCechH1

variable (R A : CommRingCat.{u}) [HopfAlgebra R A]
variable {I : Type v} (U : FpqcCover R I)

/-- The distinguished neutral class, represented by the trivial
nonabelian one-cocycle. -/
def neutral : FpqcCechH1 R A U :=
  1

/-- The explicit neutral class is the distinguished `One` element supplied by
Mathlib's fixed-cover `H¹`. -/
@[simp] theorem neutral_eq_one :
    neutral R A U = (1 : FpqcCechH1 R A U) :=
  rfl

/-- The neutral class is represented by the trivial one-cocycle. -/
theorem neutral_eq_trivialCocycleClass :
    neutral R A U =
      PresheafOfGroups.OneCocycle.class
        (1 : PresheafOfGroups.OneCocycle
          (affineGroupPresheaf R A) U.obj) :=
  rfl

/-- Neutrality of a fixed-cover cohomology class. -/
def IsNeutral (ξ : FpqcCechH1 R A U) : Prop :=
  ξ = neutral R A U

/-- The distinguished class is neutral. -/
@[simp] theorem isNeutral_neutral :
    IsNeutral R A U (neutral R A U) :=
  rfl

/-- Refinement pullback for the fixed-cover cohomology of an affine group
scheme. -/
def pullback {J : Type w} {V : FpqcCover R J}
    (r : V.Refinement U) :
    FpqcCechH1 R A U → FpqcCechH1 R A V :=
  r.pullbackH1

/-- Refinement pullback preserves the explicit neutral class. -/
@[simp] theorem pullback_neutral {J : Type w} {V : FpqcCover R J}
    (r : V.Refinement U) :
    pullback R A U r (neutral R A U) = neutral R A V :=
  r.pullbackH1_one

/-- A neutral fixed-cover class remains neutral after refinement. -/
theorem IsNeutral.pullback {J : Type w} {V : FpqcCover R J}
    {ξ : FpqcCechH1 R A U} (hξ : IsNeutral R A U ξ)
    (r : V.Refinement U) :
    IsNeutral R A V (pullback R A U r ξ) := by
  rw [IsNeutral] at hξ ⊢
  rw [hξ, pullback_neutral]

end FpqcCechH1

end

end RiemannResearch.AlgebraicGeometry
