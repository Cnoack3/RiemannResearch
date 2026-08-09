/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import Mathlib.AlgebraicGeometry.Limits
import RiemannResearch.LinearAlgebra.QuotientMap

/-!
# Integral algebraic-cycle quotients

Quotients of Mathlib's integral algebraic cycles by a supplied linear relation,
with the functorial map API needed by later correspondence constructions.
-/

noncomputable section

namespace RiemannResearch.Motives

open AlgebraicGeometry
open CategoryTheory Limits

universe u

variable {X Y Z : Scheme.{u}}

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

end RiemannResearch.Motives
