/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.SerreIIConjecture

/-!
# Non-E8 Dynkin-family interfaces for Serre II

This module defines the finite Dynkin-family classifier and neutrality-provider
interfaces used by the non-`E8` Serre-II reduction. The refined assembly
theorem, including the rank and inner/outer form split for type `A_n`, is in
`SerreIITypeA`.

These interfaces do not construct a Dynkin classifier or prove any family
neutrality provider.
-/

universe u

namespace RiemannResearch.AlgebraicGeometry.SerreII

/-- The irreducible Dynkin families. The classical constructors denote the
full series `Aₙ`, `Bₙ`, `Cₙ`, and `Dₙ`. -/
inductive DynkinFamily
  | A
  | B
  | C
  | D
  | E6
  | E7
  | E8
  | F4
  | G2
  deriving DecidableEq

namespace DynkinFamily

/-- The four classical Dynkin series. -/
def IsClassical : DynkinFamily → Prop
  | .A | .B | .C | .D => True
  | _ => False

/-- All five exceptional Dynkin types, including `E8`. -/
def IsExceptional : DynkinFamily → Prop
  | .E6 | .E7 | .E8 | .F4 | .G2 => True
  | _ => False

/-- Exactly the exceptional Dynkin types left after excluding `E8`. -/
def IsRemainingExceptional : DynkinFamily → Prop
  | .E6 | .E7 | .F4 | .G2 => True
  | _ => False

theorem classical_or_exceptional (d : DynkinFamily) :
    d.IsClassical ∨ d.IsExceptional := by
  cases d <;> simp [IsClassical, IsExceptional]

theorem exceptional_iff_e8_or_remainingExceptional (d : DynkinFamily) :
    d.IsExceptional ↔ d = .E8 ∨ d.IsRemainingExceptional := by
  cases d <;> simp [IsExceptional, IsRemainingExceptional]

theorem ne_e8_iff_classical_or_remainingExceptional (d : DynkinFamily) :
    d ≠ .E8 ↔ d.IsClassical ∨ d.IsRemainingExceptional := by
  cases d <;> simp [IsClassical, IsRemainingExceptional]

end DynkinFamily

/-- An abstract classifier for an affine group scheme's irreducible Dynkin
family. Constructing this classifier for concrete semisimple simply connected
group schemes is a separate obligation. -/
abbrev DynkinFamilyClassifier :=
  (R A : CommRingCat.{u}) → [HopfAlgebra R A] → DynkinFamily

/-- Restrict a group predicate to objects whose supplied Dynkin-family
classifier is not `E8`. -/
def NonE8GroupCondition
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier) : GroupCondition :=
  fun R A _ =>
    IsSemisimpleSimplyConnected R A ∧ family R A ≠ .E8

/-- A pointwise provider of the Serre-II neutrality conclusion for the
families selected by `Select`. -/
abbrev NeutralityProvider
    (IsPerfectFieldCdAtMostTwo : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier)
    (Select : DynkinFamily → Prop) : Prop :=
  ∀ (R A : CommRingCat.{u}) [HopfAlgebra R A],
    IsPerfectFieldCdAtMostTwo R →
    IsSemisimpleSimplyConnected R A →
    Select (family R A) →
    Subsingleton (FpqcH1.{u, u} R A)

/-- A neutrality provider for one exact Dynkin family. -/
abbrev ExactFamilyNeutralityProvider
    (IsPerfectFieldCdAtMostTwo : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier)
    (d : DynkinFamily) : Prop :=
  NeutralityProvider IsPerfectFieldCdAtMostTwo
    IsSemisimpleSimplyConnected family (fun e => e = d)

end RiemannResearch.AlgebraicGeometry.SerreII
