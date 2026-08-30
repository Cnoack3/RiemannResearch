/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.Algebra.Algebra.IsSimpleRing
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.TensorProduct.Opposite
import Mathlib.RingTheory.Flat.Basic

/-!
# Tensor products of Azumaya algebras over fields

Mathlib's current Azumaya API does not yet expose closure under tensor
products.  This file proves the field case by factoring the canonical
left-right action of `A ⊗ B` into three explicit linear equivalences:

* distribute the opposite algebra and shuffle the four tensor factors;
* apply the two Azumaya left-right equivalences separately; and
* identify the tensor product of the two endomorphism spaces with the
  endomorphisms of `A ⊗ B`.

The resulting composite is proved equal to
`AlgHom.mulLeftRight k (A ⊗[k] B)`, so its bijectivity supplies the Azumaya
structure without assuming centrality or simplicity of the tensor product.
-/

open scoped TensorProduct
open MulOpposite

namespace RiemannResearch.IsAzumaya

universe u v w

variable (k : Type u) (A : Type v) (B : Type w)
variable [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

/-- The canonical left-right action of an Azumaya algebra, regarded as a
linear equivalence. -/
noncomputable def mulLeftRightLinearEquiv [IsAzumaya k A] :
    (A ⊗[k] Aᵐᵒᵖ) ≃ₗ[k] Module.End k A :=
  LinearEquiv.ofBijective (AlgHom.mulLeftRight k A).toLinearMap
    IsAzumaya.bij

@[simp] theorem mulLeftRightLinearEquiv_tmul_apply
    [IsAzumaya k A] (a c x : A) :
    mulLeftRightLinearEquiv k A (a ⊗ₜ[k] op c) x = a * x * c := by
  change AlgHom.mulLeftRight k A (a ⊗ₜ[k] op c) x = a * x * c
  simp

/-- Distribute the opposite algebra of `A ⊗ B` and shuffle the middle two
tensor factors. -/
noncomputable def tensorAzumayaDomainEquiv :
    ((A ⊗[k] B) ⊗[k] (A ⊗[k] B)ᵐᵒᵖ) ≃ₗ[k]
      ((A ⊗[k] Aᵐᵒᵖ) ⊗[k] (B ⊗[k] Bᵐᵒᵖ)) :=
  TensorProduct.congr (LinearEquiv.refl k (A ⊗[k] B))
      (Algebra.TensorProduct.opAlgEquiv k k A B).symm.toLinearEquiv ≪≫ₗ
    TensorProduct.tensorTensorTensorComm k A B Aᵐᵒᵖ Bᵐᵒᵖ

@[simp] theorem tensorAzumayaDomainEquiv_tmul
    (a : A) (b : B) (c : A) (d : B) :
    tensorAzumayaDomainEquiv k A B
      ((a ⊗ₜ[k] b) ⊗ₜ[k] op (c ⊗ₜ[k] d)) =
      (a ⊗ₜ[k] op c) ⊗ₜ[k] (b ⊗ₜ[k] op d) := by
  simp [tensorAzumayaDomainEquiv]

@[simp] theorem tensorAzumayaDomainEquiv_symm_tmul
    (a : A) (b : B) (c : A) (d : B) :
    (tensorAzumayaDomainEquiv k A B).symm
      ((a ⊗ₜ[k] op c) ⊗ₜ[k] (b ⊗ₜ[k] op d)) =
      (a ⊗ₜ[k] b) ⊗ₜ[k] op (c ⊗ₜ[k] d) := by
  apply (tensorAzumayaDomainEquiv k A B).injective
  simp

/-- Apply the two Azumaya equivalences, then tensor the resulting
endomorphisms. -/
noncomputable def tensorAzumayaCodomainEquiv
    [IsAzumaya k A] [IsAzumaya k B] :
    ((A ⊗[k] Aᵐᵒᵖ) ⊗[k] (B ⊗[k] Bᵐᵒᵖ)) ≃ₗ[k]
      Module.End k (A ⊗[k] B) :=
  TensorProduct.congr (mulLeftRightLinearEquiv k A)
      (mulLeftRightLinearEquiv k B) ≪≫ₗ
    homTensorHomEquiv k A B A B

@[simp] theorem tensorAzumayaCodomainEquiv_tmul_apply
    [IsAzumaya k A] [IsAzumaya k B]
    (a c x : A) (b d y : B) :
    tensorAzumayaCodomainEquiv k A B
      ((a ⊗ₜ[k] op c) ⊗ₜ[k] (b ⊗ₜ[k] op d))
      (x ⊗ₜ[k] y) =
      (a * x * c) ⊗ₜ[k] (b * y * d) := by
  simp [tensorAzumayaCodomainEquiv, homTensorHomEquiv_apply]

private lemma tensorAzumaya_pure_comparison
    [IsAzumaya k A] [IsAzumaya k B]
    (a c x : A) (b d y : B) :
    tensorAzumayaCodomainEquiv k A B
      ((a ⊗ₜ[k] op c) ⊗ₜ[k] (b ⊗ₜ[k] op d)) (x ⊗ₜ[k] y) =
      (AlgHom.mulLeftRight k (A ⊗[k] B))
        ((tensorAzumayaDomainEquiv k A B).symm
          ((a ⊗ₜ[k] op c) ⊗ₜ[k] (b ⊗ₜ[k] op d)))
        (x ⊗ₜ[k] y) := by
  rw [tensorAzumayaDomainEquiv_symm_tmul]
  rw [tensorAzumayaCodomainEquiv_tmul_apply]
  simp [AlgHom.mulLeftRight_apply]

/-- After undoing the tensor-factor shuffle, the codomain equivalence is the
canonical left-right action. -/
theorem tensorAzumayaCodomainEquiv_toLinearMap
    [IsAzumaya k A] [IsAzumaya k B] :
    (tensorAzumayaCodomainEquiv k A B).toLinearMap =
      (AlgHom.mulLeftRight k (A ⊗[k] B)).toLinearMap.comp
        (tensorAzumayaDomainEquiv k A B).symm.toLinearMap := by
  apply TensorProduct.ext'
  intro ac bd
  induction ac using TensorProduct.induction_on with
  | zero => simp
  | add ac₁ ac₂ h₁ h₂ =>
      rw [TensorProduct.add_tmul, map_add, map_add]
      exact congrArg₂ (· + ·) h₁ h₂
  | tmul a c =>
      induction bd using TensorProduct.induction_on with
      | zero => simp
      | add bd₁ bd₂ h₁ h₂ =>
          rw [TensorProduct.tmul_add, map_add, map_add]
          exact congrArg₂ (· + ·) h₁ h₂
      | tmul b d =>
          rcases c with ⟨c⟩
          rcases d with ⟨d⟩
          apply LinearMap.ext
          intro xy
          induction xy using TensorProduct.induction_on with
          | zero => simp
          | add xy₁ xy₂ h₁ h₂ =>
              rw [map_add, map_add]
              exact congrArg₂ (· + ·) h₁ h₂
          | tmul x y =>
              exact tensorAzumaya_pure_comparison k A B a c x b d y

/-- The explicit factorization of the left-right action of `A ⊗ B`. -/
noncomputable def tensorAzumayaMulLeftRightEquiv
    [IsAzumaya k A] [IsAzumaya k B] :
    ((A ⊗[k] B) ⊗[k] (A ⊗[k] B)ᵐᵒᵖ) ≃ₗ[k]
      Module.End k (A ⊗[k] B) :=
  tensorAzumayaDomainEquiv k A B ≪≫ₗ
    tensorAzumayaCodomainEquiv k A B

/-- The explicit factorization is exactly Mathlib's canonical left-right
action. -/
theorem tensorAzumayaMulLeftRightEquiv_toLinearMap
    [IsAzumaya k A] [IsAzumaya k B] :
    (tensorAzumayaMulLeftRightEquiv k A B).toLinearMap =
      (AlgHom.mulLeftRight k (A ⊗[k] B)).toLinearMap := by
  apply LinearMap.ext
  intro z
  change (tensorAzumayaCodomainEquiv k A B).toLinearMap
      (tensorAzumayaDomainEquiv k A B z) = _
  rw [tensorAzumayaCodomainEquiv_toLinearMap]
  simp

/-- The tensor product of two Azumaya algebras over a field is Azumaya. -/
theorem tensorProduct_of_field
    [IsAzumaya k A] [IsAzumaya k B] :
    IsAzumaya k (A ⊗[k] B) := by
  haveI : Nontrivial A :=
    (FaithfulSMul.algebraMap_injective k A).nontrivial
  haveI : Nontrivial B :=
    (FaithfulSMul.algebraMap_injective k B).nontrivial
  haveI : Nontrivial (A ⊗[k] B) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left
      k A B (FaithfulSMul.algebraMap_injective k B)
  apply IsAzumaya.mk
  have hbij : Function.Bijective
      (tensorAzumayaMulLeftRightEquiv k A B).toLinearMap :=
    (tensorAzumayaMulLeftRightEquiv k A B).bijective
  rw [tensorAzumayaMulLeftRightEquiv_toLinearMap k A B] at hbij
  change Function.Bijective
    (AlgHom.mulLeftRight k (A ⊗[k] B)).toLinearMap
  exact hbij

end RiemannResearch.IsAzumaya
