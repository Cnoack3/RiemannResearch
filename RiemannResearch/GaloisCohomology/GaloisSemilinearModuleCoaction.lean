/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.GaloisCohomology.GaloisSemilinearModuleDescent

/-!
# The counital Galois semilinear coaction

For a finite Galois extension and a semilinear module action, the inverse
Galois-coordinate image of a constant function defines an `L`-linear map

    M → L ⊗[K] M.

Evaluation at the identity Galois automorphism is the tensor counit
`x ⊗ m ↦ x • m`, so the resulting map satisfies the counit law.

This is only the bounded counital layer.  No coassociativity or coalgebra
structure is asserted here.

Source: user-provided argument.  The proof uses the Galois-coordinate
equivalence from `GaloisSemilinearModuleDescent`.
-/

namespace RiemannResearch.GaloisCohomology

noncomputable section

universe u

variable (K L M : Type u) [Field K] [Field L] [Algebra K L]
variable [AddCommGroup M] [Module K M] [Module L M] [IsScalarTower K L M]

/-- The diagonal map sending a module element to the corresponding constant
Galois-indexed function. -/
def galoisConstantFunctions :
    M →ₗ[L] ((L ≃ₐ[K] L) → M) :=
  LinearMap.pi (fun _ : L ≃ₐ[K] L => LinearMap.id)

/-- The candidate semilinear descent coaction: the inverse Galois-coordinate
image of the constant function with value `m`. -/
noncomputable def galoisSemilinearCoaction
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M) :
    M →ₗ[L] TensorProduct K L M :=
  (galoisSemilinearTensorEquiv K L M a).symm.toLinearMap.comp
    (galoisConstantFunctions K L M)

/-- In Galois coordinates, the coaction of `m` is the constant function
with value `m`. -/
@[simp]
theorem galoisSemilinearTensorEquiv_coaction_apply
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M)
    (m : M) (σ : L ≃ₐ[K] L) :
    galoisSemilinearTensorEquiv K L M a
        (galoisSemilinearCoaction K L M a m) σ = m := by
  have h :=
    (galoisSemilinearTensorEquiv K L M a).apply_symm_apply
      (galoisConstantFunctions K L M m)
  exact congrFun h σ

/-- The tensor counit, sending `x ⊗ m` to `x • m`. -/
def galoisSemilinearTensorCounit :
    TensorProduct K L M →ₗ[L] M :=
  LinearMap.liftBaseChange L (LinearMap.id : M →ₗ[K] M)

/-- Pure-tensor formula for the tensor counit. -/
@[simp]
theorem galoisSemilinearTensorCounit_tmul
    (x : L) (m : M) :
    galoisSemilinearTensorCounit K L M (x ⊗ₜ[K] m) = x • m := by
  simp [galoisSemilinearTensorCounit]

/-- Evaluation of Galois coordinates at the identity automorphism is the
tensor counit. -/
theorem galoisSemilinearTensorEquiv_apply_one
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M)
    (z : TensorProduct K L M) :
    galoisSemilinearTensorEquiv K L M a z (1 : L ≃ₐ[K] L) =
      galoisSemilinearTensorCounit K L M z := by
  induction z using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul x m =>
      simp [a.one_act]
  | add p q hp hq =>
      rw [map_add, map_add, Pi.add_apply, hp, hq]

/-- Applying the tensor counit to the semilinear coaction recovers the
original module element. -/
@[simp]
theorem galoisSemilinearTensorCounit_coaction
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M)
    (m : M) :
    galoisSemilinearTensorCounit K L M
        (galoisSemilinearCoaction K L M a m) = m := by
  rw [← galoisSemilinearTensorEquiv_apply_one K L M a]
  exact galoisSemilinearTensorEquiv_coaction_apply K L M a m 1

/-- The coaction satisfies the counit law as an equality of `L`-linear
maps. -/
theorem galoisSemilinearCoaction_counit
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M) :
    (galoisSemilinearTensorCounit K L M).comp
        (galoisSemilinearCoaction K L M a) =
      LinearMap.id := by
  ext m
  exact galoisSemilinearTensorCounit_coaction K L M a m

end

end RiemannResearch.GaloisCohomology
