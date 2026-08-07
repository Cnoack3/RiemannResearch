/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib

/-!
# Lifting through a split linear quotient

The theorem in this file is the module-theoretic kernel used in the generic
valuation-packet construction.  Taking the scalar semiring to be a group
algebra makes its linear maps equivariant module maps.
-/

namespace RiemannResearch.LinearAlgebra

/-- A specified right inverse of `q` lifts every linear map into the codomain
of `q`.  Over a group algebra this is the corresponding equivariant lifting
statement. -/
theorem exists_lift_of_rightInverse
    {R : Type*} [Semiring R]
    {V Q P : Type*}
    [AddCommMonoid V] [AddCommMonoid Q] [AddCommMonoid P]
    [Module R V] [Module R Q] [Module R P]
    (q : Q →ₗ[R] P) (s : P →ₗ[R] Q)
    (hs : q.comp s = LinearMap.id)
    (j : V →ₗ[R] P) :
    ∃ jTilde : V →ₗ[R] Q, q.comp jTilde = j := by
  refine ⟨s.comp j, ?_⟩
  rw [← LinearMap.comp_assoc, hs, LinearMap.id_comp]

end RiemannResearch.LinearAlgebra
