/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.Motives.IntegralCycleQuotients

/-!
# Integral correspondence composition

Product-cycle quotient modules and the representative-level bilinear data
needed to descend correspondence composition, associativity, and identities.
-/

noncomputable section

namespace RiemannResearch.Motives

open AlgebraicGeometry
open CategoryTheory Limits

universe u

variable {X Y Z W : Scheme.{u}}

/-- Integral algebraic cycles on the categorical product of two schemes. -/
abbrev IntegralProductCycles (X Y : Scheme.{u}) :=
  AlgebraicCycle (X ⨯ Y) ℤ

/-- Product cycles modulo a supplied relation. This is an ungraded quotient:
the codimension condition required for Chow correspondences is not yet present
in Mathlib's algebraic-cycle API. -/
abbrev IntegralProductCycleClassModule (X Y : Scheme.{u})
    (relations : Submodule ℤ (IntegralProductCycles X Y)) :=
  IntegralProductCycles X Y ⧸ relations

/-- The class of an integral cycle on a product of schemes. -/
def integralProductCycleClass
    (relations : Submodule ℤ (IntegralProductCycles X Y)) :
    IntegralProductCycles X Y →ₗ[ℤ]
      IntegralProductCycleClassModule X Y relations :=
  relations.mkQ

/-- Cycle-level composition data for three schemes.

The intended geometric operation is pullback to the triple product,
intersection, and proper pushforward. This structure asserts no such operation
exists; it records exactly the bilinear map and relation-preservation proofs
needed for it to descend. -/
structure IntegralProductCycleCompositionData
    (X Y Z : Scheme.{u})
    (relationsXY : Submodule ℤ (IntegralProductCycles X Y))
    (relationsYZ : Submodule ℤ (IntegralProductCycles Y Z))
    (relationsXZ : Submodule ℤ (IntegralProductCycles X Z)) where
  cycleComposition :
    IntegralProductCycles X Y →ₗ[ℤ]
      IntegralProductCycles Y Z →ₗ[ℤ] IntegralProductCycles X Z
  map_rel_left :
    ∀ a ∈ relationsXY, ∀ b, cycleComposition a b ∈ relationsXZ
  map_rel_right :
    ∀ a b, b ∈ relationsYZ → cycleComposition a b ∈ relationsXZ

namespace IntegralProductCycleCompositionData

/-- Descend supplied product-cycle composition to the quotient modules. -/
def onClasses
    {relationsXY : Submodule ℤ (IntegralProductCycles X Y)}
    {relationsYZ : Submodule ℤ (IntegralProductCycles Y Z)}
    {relationsXZ : Submodule ℤ (IntegralProductCycles X Z)}
    (c : IntegralProductCycleCompositionData
      X Y Z relationsXY relationsYZ relationsXZ) :
    IntegralProductCycleClassModule X Y relationsXY →ₗ[ℤ]
      IntegralProductCycleClassModule Y Z relationsYZ →ₗ[ℤ]
        IntegralProductCycleClassModule X Z relationsXZ :=
  RiemannResearch.LinearAlgebra.bilinearMapQ
    relationsXY relationsYZ relationsXZ c.cycleComposition
      c.map_rel_left c.map_rel_right

@[simp]
theorem onClasses_mk_mk
    {relationsXY : Submodule ℤ (IntegralProductCycles X Y)}
    {relationsYZ : Submodule ℤ (IntegralProductCycles Y Z)}
    {relationsXZ : Submodule ℤ (IntegralProductCycles X Z)}
    (c : IntegralProductCycleCompositionData
      X Y Z relationsXY relationsYZ relationsXZ)
    (a : IntegralProductCycles X Y)
    (b : IntegralProductCycles Y Z) :
    c.onClasses (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) =
      Submodule.Quotient.mk (c.cycleComposition a b) := by
  exact RiemannResearch.LinearAlgebra.bilinearMapQ_mk_mk
    relationsXY relationsYZ relationsXZ c.cycleComposition
      c.map_rel_left c.map_rel_right a b

/-- Representative-level associativity of compatible cycle compositions
descends to associativity on the quotient modules. -/
theorem onClasses_assoc
    {relationsXY : Submodule ℤ (IntegralProductCycles X Y)}
    {relationsYZ : Submodule ℤ (IntegralProductCycles Y Z)}
    {relationsZW : Submodule ℤ (IntegralProductCycles Z W)}
    {relationsXZ : Submodule ℤ (IntegralProductCycles X Z)}
    {relationsYW : Submodule ℤ (IntegralProductCycles Y W)}
    {relationsXW : Submodule ℤ (IntegralProductCycles X W)}
    (cXYZ : IntegralProductCycleCompositionData
      X Y Z relationsXY relationsYZ relationsXZ)
    (cYZW : IntegralProductCycleCompositionData
      Y Z W relationsYZ relationsZW relationsYW)
    (cXZW : IntegralProductCycleCompositionData
      X Z W relationsXZ relationsZW relationsXW)
    (cXYW : IntegralProductCycleCompositionData
      X Y W relationsXY relationsYW relationsXW)
    (hassoc : ∀ a b d,
      cXZW.cycleComposition (cXYZ.cycleComposition a b) d =
        cXYW.cycleComposition a (cYZW.cycleComposition b d))
    (a : IntegralProductCycleClassModule X Y relationsXY)
    (b : IntegralProductCycleClassModule Y Z relationsYZ)
    (d : IntegralProductCycleClassModule Z W relationsZW) :
    cXZW.onClasses (cXYZ.onClasses a b) d =
      cXYW.onClasses a (cYZW.onClasses b d) := by
  refine Submodule.Quotient.induction_on relationsXY a ?_
  intro a
  refine Submodule.Quotient.induction_on relationsYZ b ?_
  intro b
  refine Submodule.Quotient.induction_on relationsZW d ?_
  intro d
  simp [hassoc]

/-- A representative acting as a left identity for cycle composition gives a
left identity class after quotienting. -/
theorem onClasses_left_identity
    {relationsXX : Submodule ℤ (IntegralProductCycles X X)}
    {relationsXY : Submodule ℤ (IntegralProductCycles X Y)}
    (c : IntegralProductCycleCompositionData
      X X Y relationsXX relationsXY relationsXY)
    (diagonal : IntegralProductCycles X X)
    (hdiagonal : ∀ a, c.cycleComposition diagonal a = a)
    (a : IntegralProductCycleClassModule X Y relationsXY) :
    c.onClasses (Submodule.Quotient.mk diagonal) a = a := by
  refine Submodule.Quotient.induction_on relationsXY a ?_
  intro a
  simp [hdiagonal]

/-- A representative acting as a right identity for cycle composition gives a
right identity class after quotienting. -/
theorem onClasses_right_identity
    {relationsXY : Submodule ℤ (IntegralProductCycles X Y)}
    {relationsYY : Submodule ℤ (IntegralProductCycles Y Y)}
    (c : IntegralProductCycleCompositionData
      X Y Y relationsXY relationsYY relationsXY)
    (diagonal : IntegralProductCycles Y Y)
    (hdiagonal : ∀ a, c.cycleComposition a diagonal = a)
    (a : IntegralProductCycleClassModule X Y relationsXY) :
    c.onClasses a (Submodule.Quotient.mk diagonal) = a := by
  refine Submodule.Quotient.induction_on relationsXY a ?_
  intro a
  simp [hdiagonal]

end IntegralProductCycleCompositionData

end RiemannResearch.Motives
