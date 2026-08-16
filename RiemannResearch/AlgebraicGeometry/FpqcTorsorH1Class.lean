/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.AlgebraicGeometry.FpqcTorsorCechCocycle
import RiemannResearch.AlgebraicGeometry.FpqcH1TorsorClassification

/-!
# The global fpqc H¹ class of an fpqc torsor

This module continues the elementary torsor-to-cocycle direction through the
global common-refinement quotient. It equips the canonical singleton
self-cover of an fpqc torsor with its tautological section, forms the resulting
fixed-cover Čech class, maps that class to `FpqcH1`, and proves invariance
under equivariant torsor isomorphism.

This supplies only the torsor-to-class assignment on objects. It does not
construct a torsor from a cocycle, invoke effective fpqc descent, prove that
equality of classes implies an equivariant torsor isomorphism, or construct
`FpqcH1TorsorClassifier`.

Source: user-provided continuation handoff and proof strategy.
-/

open CategoryTheory
open CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.ModObj

universe u v

namespace RiemannResearch.AlgebraicGeometry

noncomputable section

/-- The tautological section of an fpqc torsor over its singleton self-cover. -/
def fpqcTorsorSelfCoverSection
    (R : CommRingCat.{u})
    (G : Over (_root_.AlgebraicGeometry.Spec R)) [GrpObj G]
    (P : CategoryTheory.Mod
      (Over (_root_.AlgebraicGeometry.Spec R)) G)
    (hP : IsFpqcTorsor (_root_.AlgebraicGeometry.Spec R) G P) :
    (fpqcTorsorSelfCover R G P hP).TorsorLocalSections P :=
  fun _ => 𝟙 P.X

/-- A morphism of fpqc torsors refines the source self-cover by the target
self-cover. -/
def fpqcTorsorSelfCoverRefinement
    (R : CommRingCat.{u})
    (G : Over (_root_.AlgebraicGeometry.Spec R)) [GrpObj G]
    {P Q : CategoryTheory.Mod
      (Over (_root_.AlgebraicGeometry.Spec R)) G}
    (hP : IsFpqcTorsor (_root_.AlgebraicGeometry.Spec R) G P)
    (hQ : IsFpqcTorsor (_root_.AlgebraicGeometry.Spec R) G Q)
    (f : P ⟶ Q) :
    (fpqcTorsorSelfCover R G P hP).Refinement
      (fpqcTorsorSelfCover R G Q hQ) where
  index := fun _ => PUnit.unit
  hom := fun _ => f.hom

/-- The fixed-cover Čech class of an affine-group fpqc torsor on its canonical
self-cover. -/
def affineGroupTorsorSelfCechClass
    (R A : CommRingCat.{u}) [HopfAlgebra R A]
    (P : CategoryTheory.Mod
      (Over (_root_.AlgebraicGeometry.Spec R)) (affineGroupScheme R A))
    (hP : IsFpqcTorsor (_root_.AlgebraicGeometry.Spec R)
      (affineGroupScheme R A) P) :
    FpqcCechH1 R A
      (fpqcTorsorSelfCover R (affineGroupScheme R A) P hP) :=
  (torsorCocycle
    (fpqcTorsorSelfCover R (affineGroupScheme R A) P hP)
    hP.1
    (fpqcTorsorSelfCoverSection R (affineGroupScheme R A) P hP)).class

/-- The global fpqc Čech `H¹` class of an affine-group fpqc torsor. -/
def affineGroupTorsorH1Class
    (R A : CommRingCat.{u}) [HopfAlgebra R A]
    (P : CategoryTheory.Mod
      (Over (_root_.AlgebraicGeometry.Spec R)) (affineGroupScheme R A))
    (hP : IsFpqcTorsor (_root_.AlgebraicGeometry.Spec R)
      (affineGroupScheme R A) P) :
    FpqcH1.{u, v} R A :=
  FpqcH1.classOf R A
    (fpqcTorsorSelfCover R (affineGroupScheme R A) P hP)
    (affineGroupTorsorSelfCechClass R A P hP)

/-- Isomorphic affine-group fpqc torsors determine the same global fpqc Čech
`H¹` class. -/
theorem affineGroupTorsorH1Class_eq_of_iso
    (R A : CommRingCat.{u}) [HopfAlgebra R A]
    {P Q : CategoryTheory.Mod
      (Over (_root_.AlgebraicGeometry.Spec R)) (affineGroupScheme R A)}
    (hP : IsFpqcTorsor (_root_.AlgebraicGeometry.Spec R)
      (affineGroupScheme R A) P)
    (hQ : IsFpqcTorsor (_root_.AlgebraicGeometry.Spec R)
      (affineGroupScheme R A) Q)
    (e : P ≅ Q) :
    affineGroupTorsorH1Class.{u, v} R A P hP =
      affineGroupTorsorH1Class.{u, v} R A Q hQ := by
  let U := fpqcTorsorSelfCover R (affineGroupScheme R A) P hP
  let V := fpqcTorsorSelfCover R (affineGroupScheme R A) Q hQ
  let p := fpqcTorsorSelfCoverSection R (affineGroupScheme R A) P hP
  let q := fpqcTorsorSelfCoverSection R (affineGroupScheme R A) Q hQ
  let r : U.Refinement V :=
    fpqcTorsorSelfCoverRefinement R (affineGroupScheme R A) hP hQ e.hom
  have hcocycle :
      torsorCocycle U hP.1 p =
        torsorCocycle U hQ.1 (r.pullbackTorsorLocalSections q) := by
    calc
      torsorCocycle U hP.1 p =
          torsorCocycle U hQ.1 (fun i => p i ≫ e.hom.hom) :=
        torsorCocycle_comp_modHom U hP.1 hQ.1 e.hom p
      _ = torsorCocycle U hQ.1 (r.pullbackTorsorLocalSections q) := by
        apply congrArg (torsorCocycle U hQ.1)
        funext i
        ext
        change Over.Hom.left (p i) ≫ e.hom.hom.left =
          Over.Hom.left (r.hom i ≫ q (r.index i))
        rw [Over.comp_left]
        change Over.Hom.left (𝟙 P.X) ≫ e.hom.hom.left =
          e.hom.hom.left ≫ Over.Hom.left (𝟙 Q.X)
        rw [Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
  have hfixed :
      affineGroupTorsorSelfCechClass R A P hP =
        r.pullbackH1 (affineGroupTorsorSelfCechClass R A Q hQ) := by
    change (torsorCocycle U hP.1 p).class =
      r.pullbackH1 (torsorCocycle V hQ.1 q).class
    rw [r.pullbackH1_torsorCocycle_class]
    exact congrArg PresheafOfGroups.OneCocycle.class hcocycle
  change FpqcH1.classOf R A U
      (affineGroupTorsorSelfCechClass R A P hP) =
    FpqcH1.classOf R A V
      (affineGroupTorsorSelfCechClass R A Q hQ)
  calc
    FpqcH1.classOf R A U
        (affineGroupTorsorSelfCechClass R A P hP) =
      FpqcH1.classOf R A U
        (r.pullbackH1 (affineGroupTorsorSelfCechClass R A Q hQ)) :=
      congrArg (FpqcH1.classOf R A U) hfixed
    _ = FpqcH1.classOf R A V
        (affineGroupTorsorSelfCechClass R A Q hQ) :=
      (FpqcH1.classOf_pullback R A r
        (affineGroupTorsorSelfCechClass R A Q hQ)).symm

end

end RiemannResearch.AlgebraicGeometry
