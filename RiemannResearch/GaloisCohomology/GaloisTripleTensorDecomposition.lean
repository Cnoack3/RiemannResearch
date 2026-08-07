/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.RingTheory.TensorProduct.Pi
import RiemannResearch.GaloisCohomology.GaloisTensorDecomposition

/-!
# Triple tensor decomposition of a finite Galois extension

For a finite Galois extension L/K, this file decomposes the right-associated
triple tensor product

    L ⊗[K] (L ⊗[K] L)

as the L-algebra of L-valued functions on two Galois automorphisms. The
L-algebra structure on the tensor product comes from its first factor.

Two coordinate systems are provided. The bar-coordinate equivalence sends

    x ⊗ (y ⊗ z)

at (τ, σ) to x * σ(y) * σ(τ(z)). Reindexing by
(σ, ρ) ↦ (σ⁻¹ρ, σ) gives independent coordinates, in which the formula is

    x * σ(y) * ρ(z).

The construction iterates the tensor-square decomposition and the finite-product
equivalence for tensor products.
-/

namespace RiemannResearch.GaloisCohomology

noncomputable section

universe u v

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]

private def galoisBarToIndependent :
    ((L ≃ₐ[K] L) → (L ≃ₐ[K] L) → L) ≃ₐ[L]
      ((L ≃ₐ[K] L) → (L ≃ₐ[K] L) → L) :=
  AlgEquiv.mk
    { toFun := fun f σ ρ => f (σ⁻¹ * ρ) σ
      invFun := fun f τ σ => f σ (σ * τ)
      left_inv := by
        intro f
        funext τ σ
        simp
      right_inv := by
        intro f
        funext σ ρ
        simp }
    (by intros; rfl)
    (by intros; rfl)
    (by intros; rfl)

/-- The triple tensor decomposition in bar coordinates.

At coordinates (τ, σ), a pure tensor x ⊗ (y ⊗ z) evaluates to
x * σ(y) * σ(τ(z)).
-/
def galoisTripleTensorBarEquiv
    [FiniteDimensional K L] [IsGalois K L] :
    TensorProduct K L (TensorProduct K L L) ≃ₐ[L]
      ((L ≃ₐ[K] L) → (L ≃ₐ[K] L) → L) := by
  classical
  exact
    (Algebra.TensorProduct.congr
        (AlgEquiv.refl)
        ((galoisTensorEquiv K L).restrictScalars K)).trans
      ((Algebra.TensorProduct.piRight K L L
        (fun _ : L ≃ₐ[K] L => L)).trans
      (AlgEquiv.piCongrRight
        (fun _ : L ≃ₐ[K] L => galoisTensorEquiv K L)))

/-- Explicit pure-tensor evaluation in bar coordinates. -/
@[simp]
theorem galoisTripleTensorBarEquiv_tmul_apply
    [FiniteDimensional K L] [IsGalois K L]
    (x y z : L) (τ σ : L ≃ₐ[K] L) :
    galoisTripleTensorBarEquiv K L
        (x ⊗ₜ[K] (y ⊗ₜ[K] z)) τ σ =
      x * σ y * σ (τ z) := by
  classical
  simp [galoisTripleTensorBarEquiv, Algebra.TensorProduct.congr_apply, mul_assoc]

/-- The triple tensor decomposition in independent Galois coordinates.

At coordinates (σ, ρ), a pure tensor x ⊗ (y ⊗ z) evaluates to
x * σ(y) * ρ(z).
-/
def galoisTripleTensorEquiv
    [FiniteDimensional K L] [IsGalois K L] :
    TensorProduct K L (TensorProduct K L L) ≃ₐ[L]
      ((L ≃ₐ[K] L) → (L ≃ₐ[K] L) → L) :=
  (galoisTripleTensorBarEquiv K L).trans
    (galoisBarToIndependent K L)

/-- Explicit pure-tensor evaluation in independent Galois coordinates. -/
@[simp]
theorem galoisTripleTensorEquiv_tmul_apply
    [FiniteDimensional K L] [IsGalois K L]
    (x y z : L) (σ ρ : L ≃ₐ[K] L) :
    galoisTripleTensorEquiv K L
        (x ⊗ₜ[K] (y ⊗ₜ[K] z)) σ ρ =
      x * σ y * ρ z := by
  change
    galoisTripleTensorBarEquiv K L
        (x ⊗ₜ[K] (y ⊗ₜ[K] z)) (σ⁻¹ * ρ) σ =
      x * σ y * ρ z
  rw [galoisTripleTensorBarEquiv_tmul_apply]
  simp

end

end RiemannResearch.GaloisCohomology
