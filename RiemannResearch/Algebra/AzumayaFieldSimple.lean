/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.Algebra.Azumaya.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.SimpleRing.Defs

/-!
# Azumaya algebras over fields are simple

Mathlib's present Azumaya API supplies centrality of a free Azumaya algebra,
but it does not yet expose the corresponding simplicity theorem over a field.
This file proves that missing implication directly from surjectivity of the
canonical left-right action

`A ⊗[k] Aᵐᵒᵖ →ₐ[k] Module.End k A`.

If a nonzero two-sided ideal contains `x`, choose a linear endomorphism sending
`x` to an arbitrary `y`.  Azumaya surjectivity expresses that endomorphism as
a sum of left-right multiplications, each of which preserves the ideal.  Thus
the ideal contains every `y`.
-/

open TensorProduct MulOpposite

namespace RiemannResearch.IsAzumaya

universe u v

/-- An Azumaya algebra over a field is a simple ring. -/
theorem isSimpleRing_of_field
    (k : Type u) (A : Type v) [Field k] [Ring A] [Algebra k A]
    [IsAzumaya k A] : IsSimpleRing A := by
  have : Nontrivial A := (FaithfulSMul.algebraMap_injective k A).nontrivial
  rw [isSimpleRing_iff]
  refine IsSimpleOrder.mk ?_
  intro I
  by_cases hI : I = ⊥
  · exact Or.inl hI
  · right
    apply top_unique
    intro y _
    have hex : ∃ x : A, x ∈ I ∧ x ≠ 0 := by
      by_contra h
      push Not at h
      apply hI
      ext x
      constructor
      · intro hx
        simp [h x hx]
      · intro hx
        have hx0 : x = 0 := by simpa using hx
        subst x
        exact I.zero_mem
    obtain ⟨x, hxI, hx0⟩ := hex
    let f : k →ₗ[k] A := LinearMap.toSpanSingleton k A x
    obtain ⟨g, hgf⟩ := LinearMap.exists_leftInverse_of_injective f
      (LinearMap.ker_toSpanSingleton k hx0)
    let e : Module.End k A := g.smulRight y
    obtain ⟨t, ht⟩ := IsAzumaya.bij.2 e
    have hmem : ∀ z : A ⊗[k] Aᵐᵒᵖ,
        AlgHom.mulLeftRight k A z x ∈ I := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
          rw [AlgHom.mulLeftRight_apply]
          exact I.mul_mem_right (a * x) b.unop
            (I.mul_mem_left a x hxI)
      | add z w hz hw =>
          simpa using I.add_mem hz hw
    have hgx : g x = 1 := by
      have h := congrArg (fun l : k →ₗ[k] k => l 1) hgf
      simpa [f, LinearMap.comp_apply] using h
    have htx := hmem t
    rw [ht] at htx
    simpa [e, hgx] using htx

end RiemannResearch.IsAzumaya
