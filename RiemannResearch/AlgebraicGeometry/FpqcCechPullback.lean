/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.CategoryTheory.Sites.NonabelianCohomology.H1
import RiemannResearch.AlgebraicGeometry.FpqcCover

/-!
# Čech pullback along fpqc-cover refinements

Generic pullback of nonabelian Čech cochains, cocycles, and H¹ classes along
an indexed fpqc-cover refinement.
-/

namespace RiemannResearch.AlgebraicGeometry

open CategoryTheory

universe u v w

noncomputable section

namespace FpqcCover

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

end

end RiemannResearch.AlgebraicGeometry
