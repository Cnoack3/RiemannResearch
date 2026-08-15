/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.AlgebraicGeometry.FpqcTorsor
import RiemannResearch.AlgebraicGeometry.FpqcH1
import RiemannResearch.AlgebraicGeometry.FpqcCover

/-!
# The fpqc-H¹/torsor classification interface

This module isolates the exact effective-descent package needed to identify
global nonabelian fpqc Čech `H¹` with isomorphism classes of fpqc torsors.
It also proves the classifier's pointed consequence: a class is neutral
exactly when its classified torsor has a global section.

The structure `FpqcH1TorsorClassifier` is intentionally data, not an
unconditional construction. Constructing it requires effective fpqc descent
for the scheme-valued cocycles used by `FpqcH1`.

The interface assumes `Module.Flat R A`: its neutral object is the regular
torsor, so any inhabitant necessarily requires the representing Hopf algebra
to be flat over the base. A bare `HopfAlgebra R A` does not imply this.
-/

open CategoryTheory
open CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.ModObj

universe u v

namespace RiemannResearch.AlgebraicGeometry

noncomputable section

/-- The structure map of an fpqc torsor is a canonical singleton fpqc cover. -/
def fpqcTorsorSelfCover
    (R : CommRingCat.{u})
    (G : Over (_root_.AlgebraicGeometry.Spec R)) [GrpObj G]
    (P : CategoryTheory.Mod
      (Over (_root_.AlgebraicGeometry.Spec R)) G)
    (hP : IsFpqcTorsor (_root_.AlgebraicGeometry.Spec R) G P) :
    FpqcCover R PUnit := by
  letI : _root_.AlgebraicGeometry.Flat P.X.hom := hP.2.1
  letI : _root_.AlgebraicGeometry.Surjective P.X.hom := hP.2.2.1
  letI : _root_.AlgebraicGeometry.QuasiCompact P.X.hom := hP.2.2.2
  exact FpqcCover.singleton P.X.hom

/-- The affine group scheme represented by a commutative Hopf algebra. -/
abbrev affineGroupScheme
    (R A : CommRingCat.{u}) [HopfAlgebra R A] :
    Over (_root_.AlgebraicGeometry.Spec R) :=
  (_root_.AlgebraicGeometry.Spec A).asOver
    (_root_.AlgebraicGeometry.Spec R)

/-- Effective fpqc descent and its classification properties, packaged as the
precise interface relating global nonabelian Čech `H¹` to fpqc torsors. -/
structure FpqcH1TorsorClassifier
    (R A : CommRingCat.{u}) [HopfAlgebra R A]
    [Module.Flat R A] where
  torsor :
    FpqcH1.{u, v} R A →
      CategoryTheory.Mod (Over (_root_.AlgebraicGeometry.Spec R))
        (affineGroupScheme R A)
  isTorsor : ∀ x,
    IsFpqcTorsor (_root_.AlgebraicGeometry.Spec R)
      (affineGroupScheme R A) (torsor x)
  class_eq_iff_isomorphic : ∀ x y,
    x = y ↔ Nonempty (torsor x ≅ torsor y)
  essentially_surjective :
    ∀ P : CategoryTheory.Mod
        (Over (_root_.AlgebraicGeometry.Spec R)) (affineGroupScheme R A),
      IsFpqcTorsor (_root_.AlgebraicGeometry.Spec R)
        (affineGroupScheme R A) P →
      ∃ x : FpqcH1.{u, v} R A, Nonempty (torsor x ≅ P)
  neutral_trivial :
    Nonempty
      (Mod.regular (affineGroupScheme R A) ≅
        torsor (FpqcH1.neutral R A))

namespace FpqcH1TorsorClassifier

variable {R A : CommRingCat.{u}} [HopfAlgebra R A]
variable [Module.Flat R A]

/-- Under an fpqc-H¹/torsor classifier, the neutral class is exactly the
class whose torsor has a global section. -/
theorem class_eq_neutral_iff_nonempty_section
    (D : FpqcH1TorsorClassifier.{u, v} R A)
    (x : FpqcH1.{u, v} R A) :
    x = FpqcH1.neutral R A ↔
      Nonempty
        (𝟙_ (Over (_root_.AlgebraicGeometry.Spec R)) ⟶
          (D.torsor x).X) := by
  constructor
  · intro hx
    subst x
    rcases D.neutral_trivial with ⟨e⟩
    exact ⟨MonObj.one (X := affineGroupScheme R A) ≫ e.hom.hom⟩
  · rintro ⟨p⟩
    apply (D.class_eq_iff_isomorphic x (FpqcH1.neutral R A)).2
    let ex :=
      fpqcTorsorTrivializationOfSection
        (_root_.AlgebraicGeometry.Spec R) (affineGroupScheme R A)
          (D.torsor x) (D.isTorsor x) p
    rcases D.neutral_trivial with ⟨en⟩
    exact ⟨ex.symm.trans en⟩

end FpqcH1TorsorClassifier

end

end RiemannResearch.AlgebraicGeometry
