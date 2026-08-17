/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Perfect
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import RiemannResearch.AlgebraicGeometry.FpqcH1TorsorClassification
import RiemannResearch.GaloisCohomology.NonabelianH1

/-!
# Serre's Conjecture II as an open problem

This module records Serre's Conjecture II as a proposition. It deliberately
does not assert the proposition, introduce it as an axiom, or supply a
placeholder proof.

The canonical `Conjecture` is stated in torsor form: every torsor has a global
section, equivalently an `F`-rational point. The separate `H1Conjecture` is the
auxiliary Čech-cohomological target used by the existing reduction modules;
identifying it with the canonical statement still requires effective torsor
classification.

The imports make the closest existing foundations available:

* Mathlib's exact `PerfectField` predicate;
* Mathlib's topological `Field.absoluteGaloisGroup`, defined for every field
  and equipped with the Krull topology;
* Mathlib's ordinary `groupCohomology`, providing the homological foundation
  for formulating cohomological-dimension bounds;
* Mathlib's `LieAlgebra.IsSemisimple` predicate;
* the project's scheme-level `IsFpqcTorsor` and `FpqcTorsor` definitions;
* the project's concrete nonabelian fpqc `H¹` type `FpqcH1`.
* the project's discrete nonabelian Galois-cohomology carrier
  `GaloisCohomology.NonabelianH1`.

The Lie-algebra predicate is not a definition of a reductive group scheme.
Moreover, neither Mathlib nor this project yet supplies the intrinsic
reductive-group predicate, its semisimple simply connected specialization, or
the Galois-cohomological-dimension predicate needed here. Consequently the
global statement uses `GroupCondition` as an explicit reductive-group
interface and remains parameterized by the exact missing group-scheme and
field-arithmetic conditions; no Lie-algebra condition is substituted for the
former. The Hopf-algebra arguments are the current coordinate presentation of
this interface.

Mathlib's ordinary group cohomology and the imported discrete `NonabelianH1`
do not by themselves impose continuity for an absolute profinite Galois group.
Thus the exact field cohomological-dimension condition remains part of the
explicit `BaseCondition` interface.
-/

open CategoryTheory
open CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.ModObj

universe u

namespace RiemannResearch.AlgebraicGeometry.SerreII

/-- Predicate selecting perfect fields of cohomological dimension at most two. -/
abbrev BaseCondition := CommRingCat.{u} → Prop

/-- Explicit interface selecting semisimple simply connected reductive group
schemes in the current Hopf-algebra coordinate presentation. -/
abbrev GroupCondition :=
  (R A : CommRingCat.{u}) → [HopfAlgebra R A] → Prop

/-- **Serre's Conjecture II (open problem), in torsor form.**

If `G` is a semisimple simply connected algebraic group over a perfect field
`F` of cohomological dimension at most two, then every `G`-torsor over
`Spec F` has an `F`-rational point.

In the current coordinate presentation, a rational point is a global section
of the scheme-level torsor. This is a definition of the conjectural
proposition, not a proof or an axiom.
-/
def Conjecture
    (IsPerfectFieldCdAtMostTwo : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition) : Prop :=
  ∀ (R A : CommRingCat.{u}) [HopfAlgebra R A],
    IsPerfectFieldCdAtMostTwo R →
    IsSemisimpleSimplyConnected R A →
    ∀ P : CategoryTheory.Mod
        (Over (_root_.AlgebraicGeometry.Spec R)) (affineGroupScheme R A),
      IsFpqcTorsor (_root_.AlgebraicGeometry.Spec R)
        (affineGroupScheme R A) P →
      Nonempty
        (𝟙_ (Over (_root_.AlgebraicGeometry.Spec R)) ⟶ P.X)

/-- A torsor over `Spec F` has an `F`-rational point exactly when it is
equivariantly isomorphic to the regular torsor. -/
theorem conjecture_iff_every_torsor_trivial
    (Base : BaseCondition)
    (Group : GroupCondition) :
    Conjecture Base Group ↔
      ∀ (R A : CommRingCat.{u}) [HopfAlgebra R A],
        Base R →
        Group R A →
        ∀ P : CategoryTheory.Mod
            (Over (_root_.AlgebraicGeometry.Spec R)) (affineGroupScheme R A),
          IsFpqcTorsor (_root_.AlgebraicGeometry.Spec R)
            (affineGroupScheme R A) P →
          Nonempty (CategoryTheory.Mod.regular (affineGroupScheme R A) ≅ P) := by
  constructor
  · intro h R A _ hBase hGroup P hP
    exact
      (isSimplyTransitive_nonempty_section_iff_nonempty_trivialization
        (_root_.AlgebraicGeometry.Spec R) (affineGroupScheme R A) P hP.1).1
        (h R A hBase hGroup P hP)
  · intro h R A _ hBase hGroup P hP
    exact
      (isSimplyTransitive_nonempty_section_iff_nonempty_trivialization
        (_root_.AlgebraicGeometry.Spec R) (affineGroupScheme R A) P hP.1).2
        (h R A hBase hGroup P hP)

/-- Auxiliary cohomological target used by the existing Čech reduction
modules: every global fpqc `H¹` class is neutral.

Identifying this target with `Conjecture` requires the effective
`H¹`/torsor-classification interface; it is therefore kept distinct from the
canonical torsor statement.
-/
def H1Conjecture
    (IsPerfectFieldCdAtMostTwo : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition) : Prop :=
  ∀ (R A : CommRingCat.{u}) [HopfAlgebra R A],
    IsPerfectFieldCdAtMostTwo R →
    IsSemisimpleSimplyConnected R A →
    ∀ ξ : FpqcH1.{u, u} R A, ξ = FpqcH1.neutral R A

/-- The every-class-neutral formulation is equivalent to saying that the
corresponding fpqc `H¹` type is a subsingleton. -/
theorem h1Conjecture_iff_subsingleton
    (IsPerfectFieldCdAtMostTwo : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition) :
    H1Conjecture IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected ↔
      ∀ (R A : CommRingCat.{u}) [HopfAlgebra R A],
        IsPerfectFieldCdAtMostTwo R →
        IsSemisimpleSimplyConnected R A →
        Subsingleton (FpqcH1.{u, u} R A) := by
  constructor
  · intro h R A hHopf hField hGroup
    constructor
    intro x y
    calc
      x = FpqcH1.neutral R A := h R A hField hGroup x
      _ = y := (h R A hField hGroup y).symm
  · intro h R A hHopf hField hGroup ξ
    exact (h R A hField hGroup).allEq ξ (FpqcH1.neutral R A)

/-- The auxiliary `H¹` target is equivalent to neutralizing every fixed-cover
Čech class after pullback along a witnessed fpqc refinement. -/
theorem h1Conjecture_iff_every_class_locally_neutral
    (Base : BaseCondition)
    (Group : GroupCondition) :
    H1Conjecture Base Group ↔
      ∀ (R A : CommRingCat.{u}) [HopfAlgebra R A],
        Base R →
        Group R A →
        ∀ (I : Type u) (U : FpqcCover R I) (ξ : FpqcCechH1 R A U),
          ∃ (K : Type u) (W : FpqcCover R K) (r : W.Refinement U),
            r.pullbackH1 ξ = FpqcCechH1.neutral R A W := by
  rw [h1Conjecture_iff_subsingleton]
  constructor
  · intro h R A _ hBase hGroup
    exact (FpqcH1.subsingleton_iff_every_class_locally_neutral R A).mp
      (h R A hBase hGroup)
  · intro h R A _ hBase hGroup
    exact (FpqcH1.subsingleton_iff_every_class_locally_neutral R A).mpr
      (h R A hBase hGroup)

end RiemannResearch.AlgebraicGeometry.SerreII
