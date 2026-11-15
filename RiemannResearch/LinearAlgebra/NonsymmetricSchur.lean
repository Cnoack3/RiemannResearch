/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.LinearAlgebra.ObliqueBlockElimination
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Abel

/-!
# Invertibility of a nonsymmetric finite Schur complement

Source: `CanonicalPrimePowerUpdatesResearch20261107.md`, Section 3.
Old-block invertibility and full-block injectivity imply Schur invertibility
in finite dimension. No transpose relation between the cross blocks is used.
-/

namespace LinearMap
variable {R U W : Type*} [CommRing R] [AddCommGroup U] [AddCommGroup W]
  [Module R U] [Module R W]

def blockSchur (A I : U →ₗ[R] U) (B : W →ₗ[R] U)
    (C : U →ₗ[R] W) (D : W →ₗ[R] W) : W →ₗ[R] W :=
  D - C.comp (I.comp B)

theorem blockSchur_injective
    (A I : U →ₗ[R] U) (B : W →ₗ[R] U) (C : U →ₗ[R] W) (D : W →ₗ[R] W)
    (hAI : ∀ u, A (I u) = u)
    (hblock : ∀ x y, A x + B y = 0 → C x + D y = 0 → x = 0 ∧ y = 0) :
    Function.Injective (blockSchur A I B C D) := by
  intro y z hyz
  have hs : blockSchur A I B C D (y - z) = 0 := by
    rw [map_sub, hyz, sub_self]
  have h₀ : A (-I (B (y - z))) + B (y - z) = 0 := by
    rw [map_neg, hAI, neg_add_cancel]
  have h₁ : C (-I (B (y - z))) + D (y - z) = 0 := by
    change D (y - z) - C (I (B (y - z))) = 0 at hs
    rw [map_neg]
    simpa only [sub_eq_add_neg, add_comm] using hs
  exact sub_eq_zero.mp (hblock _ _ h₀ h₁).2

end LinearMap

namespace LinearEquiv
variable {K U W : Type*} [Field K] [AddCommGroup U] [AddCommGroup W]
  [Module K U] [Module K W] [FiniteDimensional K W]

/-- The inverse used in exact Schur elimination exists from finite-dimensional
full-system injectivity. -/
noncomputable def blockSchurEquiv
    (A I : U →ₗ[K] U) (B : W →ₗ[K] U) (C : U →ₗ[K] W) (D : W →ₗ[K] W)
    (hAI : ∀ u, A (I u) = u)
    (hblock : ∀ x y, A x + B y = 0 → C x + D y = 0 → x = 0 ∧ y = 0) :
    W ≃ₗ[K] W :=
  ofInjectiveEndo (LinearMap.blockSchur A I B C D)
    (LinearMap.blockSchur_injective A I B C D hAI hblock)

@[simp] theorem blockSchurEquiv_apply
    (A I : U →ₗ[K] U) (B : W →ₗ[K] U) (C : U →ₗ[K] W) (D : W →ₗ[K] W)
    (hAI : ∀ u, A (I u) = u)
    (hblock : ∀ x y, A x + B y = 0 → C x + D y = 0 → x = 0 ∧ y = 0)
    (y : W) :
    blockSchurEquiv A I B C D hAI hblock y = D y - C (I (B y)) := rfl

/-- Exact inverse formula after elimination, including the signed Schur source.
The full-block hypothesis is injectivity, not a bound or positivity assertion. -/
theorem block_solution_eq_schur_inverse
    (A I : U →ₗ[K] U) (B : W →ₗ[K] U) (C : U →ₗ[K] W) (D : W →ₗ[K] W)
    (hAI : ∀ u, A (I u) = u) (hIA : ∀ u, I (A u) = u)
    (hblock : ∀ x y, A x + B y = 0 → C x + D y = 0 → x = 0 ∧ y = 0)
    (x s : U) (y t : W) (h₀ : A x + B y = s) (h₁ : C x + D y = t) :
    y = (blockSchurEquiv A I B C D hAI hblock).symm (t - C (I s)) ∧
      x = I s - I (B y) := by
  have he := RiemannResearch.LinearAlgebra.ObliqueBlockElimination.block_elimination
    A I B C D hIA x s y t h₀ h₁
  refine ⟨?_, he.1⟩
  apply (blockSchurEquiv A I B C D hAI hblock).injective
  rw [apply_symm_apply, blockSchurEquiv_apply]
  exact he.2

end LinearEquiv
