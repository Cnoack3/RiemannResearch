/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import Mathlib.AlgebraicGeometry.Limits
import RiemannResearch.LinearAlgebra.QuotientMap
import RiemannResearch.Motives.RostNilpotence

/-!
# Integral algebraic-cycle quotients and correspondence descent

This module builds quotient modules from Mathlib's actual integral algebraic
cycles. It deliberately does not call a supplied relation rational equivalence
and does not define Chow groups or Chow motives. Those names become justified
only after the geometric rational-equivalence relation is constructed.

The product-cycle composition interface isolates the remaining geometric input:
a bilinear intersection--pushforward operation on representatives together with
proofs that it preserves the supplied relations.
-/

noncomputable section

namespace RiemannResearch.Motives

open AlgebraicGeometry
open CategoryTheory Limits

universe u

variable {X Y Z W : Scheme.{u}}

/-- A linear relation on Mathlib's integral algebraic cycles. -/
abbrev IntegralCycleRelation (X : Scheme.{u}) :=
  Submodule ℤ (AlgebraicCycle X ℤ)

/-- Mathlib's integral algebraic cycles modulo a supplied linear relation.

When the relation is eventually instantiated by geometric rational
equivalence, this is the underlying quotient module of the integral Chow
group. No such instantiation is asserted here. -/
abbrev IntegralCycleClassModule (X : Scheme.{u})
    (relations : IntegralCycleRelation X) :=
  AlgebraicCycle X ℤ ⧸ relations

/-- Send an integral algebraic cycle to its class modulo a supplied relation. -/
def integralCycleClass (relations : IntegralCycleRelation X) :
    AlgebraicCycle X ℤ →ₗ[ℤ] IntegralCycleClassModule X relations :=
  relations.mkQ

@[simp]
theorem integralCycleClass_apply (relations : IntegralCycleRelation X)
    (z : AlgebraicCycle X ℤ) :
    integralCycleClass relations z = Submodule.Quotient.mk z := by
  rfl

theorem integralCycleClass_surjective (relations : IntegralCycleRelation X) :
    Function.Surjective (integralCycleClass relations) :=
  relations.mkQ_surjective

/-- A linear map of integral cycle modules descends when it preserves the
supplied relations. This is the common quotient step needed by proper
pushforward, flat pullback, and scalar extension after those cycle maps and
their compatibility with rational equivalence have been constructed. -/
def integralCycleQuotientMap
    (relationsX : IntegralCycleRelation X)
    (relationsY : IntegralCycleRelation Y)
    (f : AlgebraicCycle X ℤ →ₗ[ℤ] AlgebraicCycle Y ℤ)
    (hf : relationsX ≤ Submodule.comap f relationsY) :
    IntegralCycleClassModule X relationsX →ₗ[ℤ]
      IntegralCycleClassModule Y relationsY :=
  relationsX.mapQ relationsY f hf

@[simp]
theorem integralCycleQuotientMap_cycleClass
    (relationsX : IntegralCycleRelation X)
    (relationsY : IntegralCycleRelation Y)
    (f : AlgebraicCycle X ℤ →ₗ[ℤ] AlgebraicCycle Y ℤ)
    (hf : relationsX ≤ Submodule.comap f relationsY)
    (z : AlgebraicCycle X ℤ) :
    integralCycleQuotientMap relationsX relationsY f hf
        (integralCycleClass relationsX z) =
      integralCycleClass relationsY (f z) := by
  exact Submodule.mapQ_apply _ _ _ _

@[simp]
theorem integralCycleQuotientMap_id
    (relations : IntegralCycleRelation X) :
    integralCycleQuotientMap relations relations LinearMap.id (by simp) =
      LinearMap.id := by
  exact Submodule.mapQ_id relations _

theorem integralCycleQuotientMap_comp
    (relationsX : IntegralCycleRelation X)
    (relationsY : IntegralCycleRelation Y)
    (relationsZ : IntegralCycleRelation Z)
    (f : AlgebraicCycle X ℤ →ₗ[ℤ] AlgebraicCycle Y ℤ)
    (g : AlgebraicCycle Y ℤ →ₗ[ℤ] AlgebraicCycle Z ℤ)
    (hf : relationsX ≤ Submodule.comap f relationsY)
    (hg : relationsY ≤ Submodule.comap g relationsZ)
    (hcomp : relationsX ≤ Submodule.comap (g.comp f) relationsZ) :
    integralCycleQuotientMap relationsX relationsZ (g.comp f) hcomp =
      (integralCycleQuotientMap relationsY relationsZ g hg).comp
        (integralCycleQuotientMap relationsX relationsY f hf) := by
  exact Submodule.mapQ_comp
    relationsX relationsY relationsZ f g hf hg hcomp

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

section RostSpecialization

universe v

variable {S T : Scheme.{u}}
variable {relationsS : Submodule ℤ (IntegralProductCycles S S)}
variable {relationsT : Submodule ℤ (IntegralProductCycles T T)}

/-- Rost nilpotence specialized to a base-change homomorphism between rings
whose underlying carriers are supplied quotients of actual integral cycles on
scheme squares.

The ring structures and base-change homomorphism remain explicit inputs: this
definition does not construct correspondence composition, rational
equivalence, or geometric scalar extension. -/
def IsIntegralProductCycleRostNilpotent
    [Ring (IntegralProductCycleClassModule S S relationsS)]
    [Ring (IntegralProductCycleClassModule T T relationsT)]
    (baseChange :
      IntegralProductCycleClassModule S S relationsS →+*
        IntegralProductCycleClassModule T T relationsT) : Prop :=
  IsRostNilpotent baseChange

/-- On supplied integral product-cycle quotient rings, Rost nilpotence lifts
every projector in the image of base change. -/
theorem lift_integralProductCycle_idempotent
    [Ring (IntegralProductCycleClassModule S S relationsS)]
    [Ring (IntegralProductCycleClassModule T T relationsT)]
    (baseChange :
      IntegralProductCycleClassModule S S relationsS →+*
        IntegralProductCycleClassModule T T relationsT)
    (h : IsIntegralProductCycleRostNilpotent baseChange)
    (e : IntegralProductCycleClassModule T T relationsT)
    (he_range : e ∈ baseChange.range)
    (he : IsIdempotentElem e) :
    ∃ e' : IntegralProductCycleClassModule S S relationsS,
      IsIdempotentElem e' ∧ baseChange e' = e :=
  lift_idempotent_of_isRostNilpotent baseChange h e he_range he

/-- A complete finite family of split projectors in the image of base change
lifts to the supplied integral product-cycle quotient ring. -/
theorem lift_complete_integralProductCycle_projectorFamily
    {ι : Type v} [Fintype ι]
    [Ring (IntegralProductCycleClassModule S S relationsS)]
    [Ring (IntegralProductCycleClassModule T T relationsT)]
    (baseChange :
      IntegralProductCycleClassModule S S relationsS →+*
        IntegralProductCycleClassModule T T relationsT)
    (h : IsIntegralProductCycleRostNilpotent baseChange)
    {e : ι → IntegralProductCycleClassModule T T relationsT}
    (he : CompleteOrthogonalIdempotents e)
    (he_range : ∀ i, e i ∈ baseChange.range) :
    ∃ e' : ι → IntegralProductCycleClassModule S S relationsS,
      CompleteOrthogonalIdempotents e' ∧ baseChange ∘ e' = e :=
  lift_completeOrthogonalIdempotents_of_isRostNilpotent
    baseChange h he he_range

end RostSpecialization

end RiemannResearch.Motives
