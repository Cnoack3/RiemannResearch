/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.GaloisCohomology.GaloisSemilinearModuleCoaction

/-!
# Coassociativity of finite-Galois semilinear module coordinates

For a finite Galois extension `L/K`, the semilinear coordinate equivalence is
iterated to identify `L ⊗[K] (L ⊗[K] M)` with functions of two Galois
automorphisms.  These coordinates prove that the constant-coordinate
semilinear coaction is coassociative.

Source: user-provided argument.  The proof iterates the finite-Galois
semilinear tensor equivalence from `GaloisSemilinearModuleDescent`.
-/

namespace RiemannResearch.GaloisCohomology

noncomputable section

universe u

variable (K L M : Type u) [Field K] [Field L] [Algebra K L]
variable [AddCommGroup M] [Module K M] [Module L M] [IsScalarTower K L M]

/-- The semilinear action on Galois-indexed functions whose reindexing turns
bar coordinates into two independent Galois coordinates. -/
private def galoisSemilinearFunctionAction
    (a : GaloisSemilinearModuleAction K L M) :
    GaloisSemilinearModuleAction K L ((L ≃ₐ[K] L) → M) where
  action σ :=
    { toFun := fun f ρ => a.action σ (f (σ⁻¹ * ρ))
      map_zero' := by ext ρ; simp
      map_add' := by intro f g; ext ρ; simp }
  one_act := by
    ext f ρ
    simp [a.one_act]
  mul_act := by
    intro σ τ
    ext f ρ
    simp [a.mul_act, mul_assoc]
  semilinear := by
    intro σ l f
    ext ρ
    simp [a.semilinear]

/-- Independent two-Galois-coordinate decomposition of the right-associated
triple tensor product with a semilinear module in the last factor. -/
noncomputable def galoisSemilinearTripleTensorEquiv
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M) :
    TensorProduct K L (TensorProduct K L M) ≃ₗ[L]
      ((L ≃ₐ[K] L) → (L ≃ₐ[K] L) → M) :=
  (LinearEquiv.baseChange K L
      (TensorProduct K L M) ((L ≃ₐ[K] L) → M)
      ((galoisSemilinearTensorEquiv K L M a).restrictScalars K)).trans
    (galoisSemilinearTensorEquiv K L ((L ≃ₐ[K] L) → M)
      (galoisSemilinearFunctionAction K L M a))

/-- Pure-tensor evaluation in independent semilinear triple coordinates. -/
@[simp]
theorem galoisSemilinearTripleTensorEquiv_tmul_apply
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M)
    (x y : L) (m : M) (σ ρ : L ≃ₐ[K] L) :
    galoisSemilinearTripleTensorEquiv K L M a
        (x ⊗ₜ[K] (y ⊗ₜ[K] m)) σ ρ =
      (x * σ y) • a.action ρ m := by
  simp [galoisSemilinearTripleTensorEquiv,
    galoisSemilinearFunctionAction, a.semilinear, a.mul_act, smul_smul]

/-- Apply the semilinear coaction in the last factor of a tensor product. -/
def galoisSemilinearTensorMapCoaction
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M) :
    TensorProduct K L M →ₗ[L]
      TensorProduct K L (TensorProduct K L M) :=
  LinearMap.baseChange L
    ((galoisSemilinearCoaction K L M a).restrictScalars K)

/-- Pure-tensor formula for applying the coaction in the module factor. -/
@[simp]
theorem galoisSemilinearTensorMapCoaction_tmul
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M) (x : L) (m : M) :
    galoisSemilinearTensorMapCoaction K L M a (x ⊗ₜ[K] m) =
      x ⊗ₜ[K] galoisSemilinearCoaction K L M a m := by
  simp [galoisSemilinearTensorMapCoaction]

/-- Raw tensor form of the extension-restriction comonad comultiplication. -/
def galoisSemilinearTensorComultiplication :
    TensorProduct K L M →ₗ[L]
      TensorProduct K L (TensorProduct K L M) :=
  LinearMap.baseChange L ((TensorProduct.mk K L M) 1)

omit [Module L M] [IsScalarTower K L M] in
/-- Pure-tensor formula for the raw comultiplication. -/
@[simp]
theorem galoisSemilinearTensorComultiplication_tmul
    (x : L) (m : M) :
    galoisSemilinearTensorComultiplication K L M (x ⊗ₜ[K] m) =
      x ⊗ₜ[K] (1 ⊗ₜ[K] m) := by
  simp [galoisSemilinearTensorComultiplication]

/-- In triple coordinates, applying the coaction in the module factor retains
the first Galois coordinate. -/
theorem galoisSemilinearTripleTensorEquiv_tensorMapCoaction_apply
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M)
    (z : TensorProduct K L M) (σ ρ : L ≃ₐ[K] L) :
    galoisSemilinearTripleTensorEquiv K L M a
        (galoisSemilinearTensorMapCoaction K L M a z) σ ρ =
      galoisSemilinearTensorEquiv K L M a z σ := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x m =>
      simp [galoisSemilinearTripleTensorEquiv,
        galoisSemilinearFunctionAction]
      rw [← galoisSemilinearTensorEquiv_apply K L M a]
      simp
  | add p q hp hq => simp [hp, hq]

/-- In triple coordinates, comultiplication retains the second Galois
coordinate. -/
theorem galoisSemilinearTripleTensorEquiv_comultiplication_apply
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M)
    (z : TensorProduct K L M) (σ ρ : L ≃ₐ[K] L) :
    galoisSemilinearTripleTensorEquiv K L M a
        (galoisSemilinearTensorComultiplication K L M z) σ ρ =
      galoisSemilinearTensorEquiv K L M a z ρ := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x m => simp
  | add p q hp hq => simp [hp, hq]

/-- The constant-coordinate semilinear coaction is coassociative. -/
theorem galoisSemilinearCoaction_coassociative
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M) :
    (galoisSemilinearTensorMapCoaction K L M a).comp
        (galoisSemilinearCoaction K L M a) =
      (galoisSemilinearTensorComultiplication K L M).comp
        (galoisSemilinearCoaction K L M a) := by
  ext m
  apply (galoisSemilinearTripleTensorEquiv K L M a).injective
  funext σ ρ
  simp [galoisSemilinearTripleTensorEquiv_tensorMapCoaction_apply,
    galoisSemilinearTripleTensorEquiv_comultiplication_apply]

end

end RiemannResearch.GaloisCohomology
