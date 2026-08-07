/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.TensorProduct.Free

/-!
# Tensor-square decomposition of a finite Galois extension

For a finite Galois extension L/K, this file constructs the canonical
L-algebra equivalence

    L ⊗[K] L ≃ₐ[L] ((L ≃ₐ[K] L) → L).

Here the L-algebra structure on the tensor product comes from its first factor.
The equivalence sends a pure tensor x ⊗ y to the function σ ↦ x * σ y.

The proof uses a normal basis and Artin's linear independence of field
embeddings. In normal-basis coordinates, the matrix of the canonical map has
rows τ ↦ σ (b τ); these rows are linearly independent, hence the matrix is
invertible.
-/

namespace RiemannResearch.GaloisCohomology

noncomputable section

universe u v

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]

private def galoisTensorLeft :
    L →ₐ[L] ((L ≃ₐ[K] L) → L) :=
  AlgHom.pi (fun _ : L ≃ₐ[K] L => AlgHom.id L L)

private def galoisTensorRight :
    L →ₐ[K] ((L ≃ₐ[K] L) → L) :=
  AlgHom.pi (fun σ : L ≃ₐ[K] L => σ.toAlgHom)

/-- The canonical map from the tensor square to functions on the Galois group.

It is defined for every field extension. Finite Galois hypotheses are needed
only to prove that it is an equivalence.
-/
def galoisTensorToFunctions :
    TensorProduct K L L →ₐ[L] ((L ≃ₐ[K] L) → L) :=
  Algebra.TensorProduct.lift
    (galoisTensorLeft K L)
    (galoisTensorRight K L)
    (fun x y => by
      ext σ
      simp [galoisTensorLeft, galoisTensorRight, mul_comm])

/-- On a pure tensor, the canonical map is (x ⊗ y)(σ) = x * σ(y). -/
@[simp]
theorem galoisTensorToFunctions_tmul_apply
    (x y : L) (σ : L ≃ₐ[K] L) :
    galoisTensorToFunctions K L (x ⊗ₜ[K] y) σ = x * σ y := by
  simp [galoisTensorToFunctions, galoisTensorLeft, galoisTensorRight]

private theorem galoisConjugates_linearIndependent
    [FiniteDimensional K L] [IsGalois K L] :
    LinearIndependent L
      (fun σ : L ≃ₐ[K] L =>
        fun τ : L ≃ₐ[K] L => σ (IsGalois.normalBasis K L τ)) := by
  let b := IsGalois.normalBasis K L
  let c : ((L ≃ₐ[K] L) → L) ≃ₗ[L] (L →ₗ[K] L) := b.constr L
  have hinj :
      Function.Injective (fun σ : L ≃ₐ[K] L => σ.toAlgHom) := by
    intro σ τ h
    ext x
    exact DFunLike.congr_fun h x
  have hLI :
      LinearIndependent L
        (fun σ : L ≃ₐ[K] L => σ.toAlgHom.toLinearMap) := by
    simpa [Function.comp_def] using
      (linearIndependent_toLinearMap K L L).comp
        (fun σ : L ≃ₐ[K] L => σ.toAlgHom) hinj
  have hker : c.symm.toLinearMap.ker = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact c.symm.injective
  have hmapped := hLI.map' c.symm.toLinearMap hker
  have heval (f : L →ₗ[K] L) (i : L ≃ₐ[K] L) :
      c.symm f i = f (b i) := by
    change (b.constr L).symm f i = f (b i)
    rw [← b.constr_basis L ((b.constr L).symm f) i]
    simp
  have hfun :
      (c.symm.toLinearMap ∘
          fun σ : L ≃ₐ[K] L => σ.toAlgHom.toLinearMap) =
        (fun σ : L ≃ₐ[K] L =>
          fun τ : L ≃ₐ[K] L => σ (b τ)) := by
    funext σ τ
    exact heval σ.toAlgHom.toLinearMap τ
  rw [← hfun]
  exact hmapped

private theorem galoisTensorToFunctions_bijective
    [FiniteDimensional K L] [IsGalois K L] :
    Function.Bijective (galoisTensorToFunctions K L) := by
  classical
  let b := IsGalois.normalBasis K L
  let bTensor := Algebra.TensorProduct.basis L b
  let bFunctions := Pi.basisFun L (L ≃ₐ[K] L)
  let f := galoisTensorToFunctions K L
  let A := (LinearMap.toMatrix bTensor bFunctions) f.toLinearMap
  have hrow :
      A.row =
        (fun σ : L ≃ₐ[K] L =>
          fun τ : L ≃ₐ[K] L => σ (b τ)) := by
    funext σ τ
    simp [A, bTensor, bFunctions, f, b, LinearMap.toMatrix_apply]
  have hLI : LinearIndependent L A.row := by
    rw [hrow]
    exact galoisConjugates_linearIndependent K L
  have hAunit : IsUnit A :=
    Matrix.linearIndependent_rows_iff_isUnit.mp hLI
  have hdet : IsUnit A.det :=
    (Matrix.isUnit_iff_isUnit_det A).mp hAunit
  let e : TensorProduct K L L ≃ₗ[L] ((L ≃ₐ[K] L) → L) :=
    LinearEquiv.ofIsUnitDet hdet
  have heq :
      (e : TensorProduct K L L → ((L ≃ₐ[K] L) → L)) = f := by
    funext z
    exact LinearEquiv.ofIsUnitDet_apply hdet z
  rw [← heq]
  exact e.bijective

/-- The canonical finite-Galois decomposition
L ⊗[K] L ≃ₐ[L] ((L ≃ₐ[K] L) → L). -/
def galoisTensorEquiv
    [FiniteDimensional K L] [IsGalois K L] :
    TensorProduct K L L ≃ₐ[L] ((L ≃ₐ[K] L) → L) :=
  AlgEquiv.ofBijective
    (galoisTensorToFunctions K L)
    (galoisTensorToFunctions_bijective K L)

/-- The Galois tensor equivalence has the canonical map as its forward map. -/
@[simp]
theorem galoisTensorEquiv_apply
    [FiniteDimensional K L] [IsGalois K L]
    (z : TensorProduct K L L) :
    galoisTensorEquiv K L z = galoisTensorToFunctions K L z :=
  AlgEquiv.ofBijective_apply _ _ z

/-- Explicit evaluation of the Galois tensor equivalence on pure tensors. -/
@[simp]
theorem galoisTensorEquiv_tmul_apply
    [FiniteDimensional K L] [IsGalois K L]
    (x y : L) (σ : L ≃ₐ[K] L) :
    galoisTensorEquiv K L (x ⊗ₜ[K] y) σ = x * σ y := by
  rw [galoisTensorEquiv_apply]
  exact galoisTensorToFunctions_tmul_apply K L x y σ

end

end RiemannResearch.GaloisCohomology
