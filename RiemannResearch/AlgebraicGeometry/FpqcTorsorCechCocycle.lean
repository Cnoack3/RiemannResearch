/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.AlgebraicGeometry.FpqcTorsor
import RiemannResearch.AlgebraicGeometry.FpqcCechH1

/-!
# Čech cocycles from local sections of fpqc torsors

This module constructs the elementary direction from local trivializations of
a simply transitive action to a represented-presheaf Čech cocycle. The
transition element `torsorTransition hP x y` is oriented by

`torsorTransition hP x y • y = x`.

Thus the transition from the `j`-section to the `i`-section satisfies the
existing cocycle convention `γᵢⱼ * γⱼₖ = γᵢₖ`. The resulting cocycle is
independent of the chosen local sections up to Mathlib's nonabelian gauge
relation, is natural under equivariant morphisms of simply transitive actions,
and is compatible with refinement of the fixed fpqc cover.

No effective descent, global torsor class, or torsor classifier is constructed
here.

Source: user-provided construction and proof strategy.
-/

open CategoryTheory
open scoped CategoryTheory.MonObj CategoryTheory.ModObj

universe u v w

noncomputable section

namespace RiemannResearch.AlgebraicGeometry

/-- The unique group-valued generalized point carrying `y` to `x` in a simply
transitive action. The order of `x` and `y` fixes the Čech orientation. -/
noncomputable def torsorTransition
    {X : _root_.AlgebraicGeometry.Scheme.{u}}
    {G : Over X} [GrpObj G]
    {P : CategoryTheory.Mod (Over X) G}
    (hP : IsSimplyTransitive X G P)
    {Z : Over X} (x y : Z ⟶ P.X) : Z ⟶ G :=
  (((isSimplyTransitive_iff X G P).mp hP Z y x).exists).choose

/-- The transition element carries its second generalized torsor point to its
first. -/
@[simp] theorem torsorTransition_smul
    {X : _root_.AlgebraicGeometry.Scheme.{u}}
    {G : Over X} [GrpObj G]
    {P : CategoryTheory.Mod (Over X) G}
    (hP : IsSimplyTransitive X G P)
    {Z : Over X} (x y : Z ⟶ P.X) :
    torsorTransition hP x y • y = x :=
  (((isSimplyTransitive_iff X G P).mp hP Z y x).exists).choose_spec

/-- A generalized group point carrying `y` to `x` is the transition element
from `y` to `x`. -/
theorem torsorTransition_unique
    {X : _root_.AlgebraicGeometry.Scheme.{u}}
    {G : Over X} [GrpObj G]
    {P : CategoryTheory.Mod (Over X) G}
    (hP : IsSimplyTransitive X G P)
    {Z : Over X} (x y : Z ⟶ P.X)
    (m : Z ⟶ G) (hm : m • y = x) :
    m = torsorTransition hP x y :=
  ((isSimplyTransitive_iff X G P).mp hP Z y x).unique
    hm (torsorTransition_smul hP x y)

/-- Transition elements commute with precomposition of generalized points. -/
@[simp, reassoc] theorem torsorTransition_precomp
    {X : _root_.AlgebraicGeometry.Scheme.{u}}
    {G : Over X} [GrpObj G]
    {P : CategoryTheory.Mod (Over X) G}
    (hP : IsSimplyTransitive X G P)
    {W Z : Over X} (f : W ⟶ Z) (x y : Z ⟶ P.X) :
    f ≫ torsorTransition hP x y =
      torsorTransition hP (f ≫ x) (f ≫ y) := by
  apply torsorTransition_unique hP
  rw [← ModObj.comp_smul, torsorTransition_smul]

/-- Oriented transition elements compose in Čech order. -/
@[simp] theorem torsorTransition_mul
    {X : _root_.AlgebraicGeometry.Scheme.{u}}
    {G : Over X} [GrpObj G]
    {P : CategoryTheory.Mod (Over X) G}
    (hP : IsSimplyTransitive X G P)
    {Z : Over X} (x y z : Z ⟶ P.X) :
    torsorTransition hP x y * torsorTransition hP y z =
      torsorTransition hP x z := by
  apply torsorTransition_unique hP
  rw [show
    (torsorTransition hP x y * torsorTransition hP y z) • z =
      torsorTransition hP x y • (torsorTransition hP y z • z) by
      simp only [mul_smul]]
  rw [torsorTransition_smul, torsorTransition_smul]

/-- An equivariant morphism between simply transitive actions preserves every
transition element. -/
theorem torsorTransition_comp_modHom
    {X : _root_.AlgebraicGeometry.Scheme.{u}}
    {G : Over X} [GrpObj G]
    {P Q : CategoryTheory.Mod (Over X) G}
    (hP : IsSimplyTransitive X G P)
    (hQ : IsSimplyTransitive X G Q)
    (f : P ⟶ Q)
    {Z : Over X} (x y : Z ⟶ P.X) :
    torsorTransition hP x y =
      torsorTransition hQ (x ≫ f.hom) (y ≫ f.hom) := by
  apply torsorTransition_unique hQ
  rw [← IsModHom.map_smul, torsorTransition_smul]

/-- A choice of one section of a torsor over every member of an fpqc cover. -/
abbrev FpqcCover.TorsorLocalSections
    {R : CommRingCat.{u}} {I : Type v} (U : FpqcCover R I)
    {G : Over (_root_.AlgebraicGeometry.Spec R)} [GrpObj G]
    (P : CategoryTheory.Mod
      (Over (_root_.AlgebraicGeometry.Spec R)) G) :=
  ∀ i, U.obj i ⟶ P.X

/-- The represented-presheaf Čech cocycle determined by local torsor
sections. -/
noncomputable def torsorCocycle
    {R : CommRingCat.{u}} {I : Type v} (U : FpqcCover R I)
    {G : Over (_root_.AlgebraicGeometry.Spec R)} [GrpObj G]
    {P : CategoryTheory.Mod
      (Over (_root_.AlgebraicGeometry.Spec R)) G}
    (hP : IsSimplyTransitive (_root_.AlgebraicGeometry.Spec R) G P)
    (p : U.TorsorLocalSections P) :
    PresheafOfGroups.OneCocycle (yonedaGrpObj G) U.obj where
  toOneCochain :=
    { ev := fun i j {T} a b =>
        torsorTransition hP (a ≫ p i) (b ≫ p j)
      ev_precomp := by
        intro i j T T' φ a b
        change φ ≫ torsorTransition hP (a ≫ p i) (b ≫ p j) =
          torsorTransition hP ((φ ≫ a) ≫ p i) ((φ ≫ b) ≫ p j)
        simpa only [Category.assoc] using
          torsorTransition_precomp hP φ (a ≫ p i) (b ≫ p j) }
  ev_trans := by
    intro i j k T a b c
    exact torsorTransition_mul hP
      (a ≫ p i) (b ≫ p j) (c ≫ p k)

/-- The zero-cochain carrying the old local sections `p` to the new local
sections `q`. -/
noncomputable def torsorGauge
    {R : CommRingCat.{u}} {I : Type v} (U : FpqcCover R I)
    {G : Over (_root_.AlgebraicGeometry.Spec R)} [GrpObj G]
    {P : CategoryTheory.Mod
      (Over (_root_.AlgebraicGeometry.Spec R)) G}
    (hP : IsSimplyTransitive (_root_.AlgebraicGeometry.Spec R) G P)
    (p q : U.TorsorLocalSections P) :
    PresheafOfGroups.ZeroCochain (yonedaGrpObj G) U.obj :=
  fun i => torsorTransition hP (q i) (p i)

/-- The cocycles from two choices of local sections satisfy the standard
nonabelian zero-cochain gauge relation. -/
theorem torsorCocycle_oneCohomologyRelation
    {R : CommRingCat.{u}} {I : Type v} (U : FpqcCover R I)
    {G : Over (_root_.AlgebraicGeometry.Spec R)} [GrpObj G]
    {P : CategoryTheory.Mod
      (Over (_root_.AlgebraicGeometry.Spec R)) G}
    (hP : IsSimplyTransitive (_root_.AlgebraicGeometry.Spec R) G P)
    (p q : U.TorsorLocalSections P) :
    PresheafOfGroups.OneCohomologyRelation
      (torsorCocycle U hP p).toOneCochain
      (torsorCocycle U hP q).toOneCochain
      (torsorGauge U hP p q) := by
  intro i j T a b
  change
    (a ≫ torsorTransition hP (q i) (p i)) *
        torsorTransition hP (a ≫ p i) (b ≫ p j) =
      torsorTransition hP (a ≫ q i) (b ≫ q j) *
        (b ≫ torsorTransition hP (q j) (p j))
  rw [torsorTransition_precomp, torsorTransition_precomp,
    torsorTransition_mul, torsorTransition_mul]

/-- Cocycles obtained from two choices of local sections are cohomologous. -/
theorem torsorCocycle_isCohomologous
    {R : CommRingCat.{u}} {I : Type v} (U : FpqcCover R I)
    {G : Over (_root_.AlgebraicGeometry.Spec R)} [GrpObj G]
    {P : CategoryTheory.Mod
      (Over (_root_.AlgebraicGeometry.Spec R)) G}
    (hP : IsSimplyTransitive (_root_.AlgebraicGeometry.Spec R) G P)
    (p q : U.TorsorLocalSections P) :
    (torsorCocycle U hP p).IsCohomologous
      (torsorCocycle U hP q) :=
  ⟨torsorGauge U hP p q,
    torsorCocycle_oneCohomologyRelation U hP p q⟩

/-- The represented fixed-cover `H¹` class is independent of the chosen local
sections. -/
theorem torsorCocycle_class_eq
    {R : CommRingCat.{u}} {I : Type v} (U : FpqcCover R I)
    {G : Over (_root_.AlgebraicGeometry.Spec R)} [GrpObj G]
    {P : CategoryTheory.Mod
      (Over (_root_.AlgebraicGeometry.Spec R)) G}
    (hP : IsSimplyTransitive (_root_.AlgebraicGeometry.Spec R) G P)
    (p q : U.TorsorLocalSections P) :
    (torsorCocycle U hP p).class =
      (torsorCocycle U hP q).class :=
  (torsorCocycle_isCohomologous U hP p q).class_eq

/-- For an affine group scheme, local-section independence is an equality in
the project's fixed-cover `FpqcCechH1`. -/
theorem affineGroupTorsorCocycle_class_eq
    (R A : CommRingCat.{u}) [HopfAlgebra R A]
    {I : Type v} (U : FpqcCover R I)
    {P : CategoryTheory.Mod
      (Over (_root_.AlgebraicGeometry.Spec R))
      ((_root_.AlgebraicGeometry.Spec A).asOver
        (_root_.AlgebraicGeometry.Spec R))}
    (hP : IsSimplyTransitive
      (_root_.AlgebraicGeometry.Spec R)
      ((_root_.AlgebraicGeometry.Spec A).asOver
        (_root_.AlgebraicGeometry.Spec R)) P)
    (p q : U.TorsorLocalSections P) :
    ((torsorCocycle U hP p).class : FpqcCechH1 R A U) =
      (torsorCocycle U hP q).class :=
  torsorCocycle_class_eq U hP p q

private theorem oneCocycle_ext
    {C : Type u} [Category.{v} C]
    {G : Cᵒᵖ ⥤ GrpCat} {I : Type w} {U : I → C}
    {cocycle₁ cocycle₂ : PresheafOfGroups.OneCocycle G U}
    (h : cocycle₁.toOneCochain = cocycle₂.toOneCochain) :
    cocycle₁ = cocycle₂ := by
  cases cocycle₁ with
  | mk cochain₁ h₁ =>
    cases cocycle₂ with
    | mk cochain₂ h₂ =>
      dsimp at h
      cases h
      rfl

/-- Applying an equivariant morphism to all local sections leaves the
represented-presheaf torsor cocycle unchanged. -/
theorem torsorCocycle_comp_modHom
    {R : CommRingCat.{u}} {I : Type v} (U : FpqcCover R I)
    {G : Over (_root_.AlgebraicGeometry.Spec R)} [GrpObj G]
    {P Q : CategoryTheory.Mod
      (Over (_root_.AlgebraicGeometry.Spec R)) G}
    (hP : IsSimplyTransitive (_root_.AlgebraicGeometry.Spec R) G P)
    (hQ : IsSimplyTransitive (_root_.AlgebraicGeometry.Spec R) G Q)
    (f : P ⟶ Q)
    (p : U.TorsorLocalSections P) :
    torsorCocycle U hP p =
      torsorCocycle U hQ (fun i => p i ≫ f.hom) := by
  apply oneCocycle_ext
  apply PresheafOfGroups.OneCochain.ext
  funext i j Z a b
  change torsorTransition hP (a ≫ p i) (b ≫ p j) =
    torsorTransition hQ (a ≫ p i ≫ f.hom) (b ≫ p j ≫ f.hom)
  simpa only [Category.assoc] using
    torsorTransition_comp_modHom hP hQ f
      (a ≫ p i) (b ≫ p j)

namespace FpqcCover.Refinement

/-- Pull local torsor sections back along a refinement. -/
def pullbackTorsorLocalSections
    {R : CommRingCat.{u}} {I : Type v} {J : Type w}
    {U : FpqcCover R I} {V : FpqcCover R J}
    (r : V.Refinement U)
    {G : Over (_root_.AlgebraicGeometry.Spec R)} [GrpObj G]
    {P : CategoryTheory.Mod
      (Over (_root_.AlgebraicGeometry.Spec R)) G}
    (p : U.TorsorLocalSections P) :
    V.TorsorLocalSections P :=
  fun j => r.hom j ≫ p (r.index j)

/-- Pulling back a torsor cocycle is the cocycle of the pulled-back local
sections. -/
theorem pullbackOneCocycle_torsorCocycle
    {R : CommRingCat.{u}} {I : Type v} {J : Type w}
    {U : FpqcCover R I} {V : FpqcCover R J}
    (r : V.Refinement U)
    {G : Over (_root_.AlgebraicGeometry.Spec R)} [GrpObj G]
    {P : CategoryTheory.Mod
      (Over (_root_.AlgebraicGeometry.Spec R)) G}
    (hP : IsSimplyTransitive (_root_.AlgebraicGeometry.Spec R) G P)
    (p : U.TorsorLocalSections P) :
    r.pullbackOneCocycle (torsorCocycle U hP p) =
      torsorCocycle V hP (r.pullbackTorsorLocalSections p) := by
  apply oneCocycle_ext
  apply PresheafOfGroups.OneCochain.ext
  funext j k T a b
  simp only [pullbackOneCocycle, pullbackOneCochain, torsorCocycle,
    pullbackTorsorLocalSections, Category.assoc]
  rfl

/-- Refinement pullback preserves the `H¹` class represented by the torsor
cocycle. -/
theorem pullbackH1_torsorCocycle_class
    {R : CommRingCat.{u}} {I : Type v} {J : Type w}
    {U : FpqcCover R I} {V : FpqcCover R J}
    (r : V.Refinement U)
    {G : Over (_root_.AlgebraicGeometry.Spec R)} [GrpObj G]
    {P : CategoryTheory.Mod
      (Over (_root_.AlgebraicGeometry.Spec R)) G}
    (hP : IsSimplyTransitive (_root_.AlgebraicGeometry.Spec R) G P)
    (p : U.TorsorLocalSections P) :
    r.pullbackH1 (torsorCocycle U hP p).class =
      (torsorCocycle V hP (r.pullbackTorsorLocalSections p)).class := by
  rw [r.pullbackH1_class, r.pullbackOneCocycle_torsorCocycle hP p]

end FpqcCover.Refinement

end RiemannResearch.AlgebraicGeometry
