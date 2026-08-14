/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.QuadraticForm.Dual
import RiemannResearch.LinearAlgebra.RootSystem.D4SpinTriality

/-!
# The standard split D4 quadratic space

This file constructs the hyperbolic quadratic space `H⁴` and proves that it
satisfies the project's eight-dimensional regularity predicate. This supplies
an actual split quadratic form to the pointwise Clifford/Spin branch.

It does not construct the even-Clifford splitting into the two half-spin
endomorphism algebras or a triality action on spin points.
-/

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality

universe u

variable (K : Type u) [Field K] [Invertible (2 : K)]

/-- The standard split eight-dimensional quadratic space `H⁴`. -/
abbrev SplitD4Space :=
  Module.Dual K (Fin 4 → K) × (Fin 4 → K)

/-- The standard split quadratic form on `H⁴`. -/
def splitD4Form : QuadraticForm K (SplitD4Space K) :=
  QuadraticForm.dualProd K (Fin 4 → K)

/-- The polar form of the hyperbolic quadratic form is one half of the
standard dual-product pairing. -/
theorem associated_dualProd_eq
    {V : Type*} [AddCommGroup V] [Module K V] :
    QuadraticMap.associated (QuadraticForm.dualProd K V) =
      (⅟ (2 : K)) • LinearMap.dualProd K V := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rw [QuadraticMap.associated_apply]
  simp [QuadraticForm.dualProd_apply, LinearMap.dualProd_apply_apply,
    smul_eq_mul]
  all_goals ring_nf
  all_goals simp

/-- The polar form of a hyperbolic quadratic form is nondegenerate whenever
the underlying module is projective. -/
theorem associated_dualProd_nondegenerate
    {V : Type*} [AddCommGroup V] [Module K V] [Module.Projective K V] :
    (QuadraticMap.associated
      (QuadraticForm.dualProd K V)).Nondegenerate := by
  apply (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    (QuadraticForm.associated_isSymm K
      (QuadraticForm.dualProd K V)).isRefl).2
  rw [associated_dualProd_eq K]
  intro x hx
  apply ((LinearMap.separatingLeft_dualProd K V).2
    (Module.eval_apply_injective K)) x
  intro y
  have h := hx y
  change (⅟ (2 : K)) * (LinearMap.dualProd K V x y) = 0 at h
  rcases mul_eq_zero.mp h with h | h
  · have hi := invOf_mul_self (2 : K)
    rw [h, zero_mul] at hi
    exact (zero_ne_one hi).elim
  · exact h

/-- The standard split form `H⁴` has dimension eight and nondegenerate
polar form. -/
theorem splitD4Form_regular :
    IsRegularEightDimensional (splitD4Form K) := by
  constructor
  · rw [Module.finrank_prod, Subspace.dual_finrank_eq,
      Module.finrank_fin_fun]
  · exact associated_dualProd_nondegenerate K

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality
