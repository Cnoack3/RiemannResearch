/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.Motives.IntegralCorrespondenceComposition
import RiemannResearch.Motives.RostNilpotence

/-!
# Integral projector lifting

Rost-nilpotence consequences for projector families in supplied quotient rings
of integral product cycles.
-/

noncomputable section

namespace RiemannResearch.Motives

open AlgebraicGeometry
open CategoryTheory Limits

universe u

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
