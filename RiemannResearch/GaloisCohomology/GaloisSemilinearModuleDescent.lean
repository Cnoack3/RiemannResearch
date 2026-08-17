/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.RingTheory.TensorProduct.Pi
import RiemannResearch.GaloisCohomology.GaloisTensorDecomposition

/-!
# Galois semilinear module tensor decomposition

For a finite Galois extension L/K, a semilinear action of the Galois group on
an L-module M identifies L tensor[K] M with the L-module of functions from the
Galois group to M.  The forward map sends x tensor m to the function taking
sigma to x times sigma(m).

The inverse is explicit.  If delta_sigma in L tensor[K] L corresponds under
galoisTensorEquiv to the characteristic function of sigma, then the inverse of
f is the sum of the contractions of delta_sigma against sigma inverse of
f(sigma).

Source: user-provided argument.  The delta-tensor construction and contraction
proof implement the standard finite-Galois coordinate argument.
-/

namespace RiemannResearch.GaloisCohomology

noncomputable section

universe u

/-- An additive action of the Galois group on an L-module, with its
semilinearity over L recorded explicitly. -/
structure GaloisSemilinearModuleAction
    (K L M : Type u) [Field K] [Field L] [Algebra K L]
    [AddCommGroup M] [Module L M] where
  action : (L ≃ₐ[K] L) → M →+ M
  one_act : action 1 = AddMonoidHom.id M
  mul_act : ∀ σ τ, action (σ * τ) = (action σ).comp (action τ)
  semilinear : ∀ σ l m, action σ (l • m) = σ l • action σ m

variable (K L M : Type u) [Field K] [Field L] [Algebra K L]
variable [AddCommGroup M] [Module L M]

namespace GaloisSemilinearModuleAction

/-- Acting first by sigma and then by its inverse is the identity. -/
@[simp]
theorem action_inv_apply_left
    (a : GaloisSemilinearModuleAction K L M)
    (σ : L ≃ₐ[K] L) (m : M) :
    a.action σ⁻¹ (a.action σ m) = m := by
  have h :=
    congrArg (fun f : M →+ M => f m) (a.mul_act σ⁻¹ σ)
  simpa [a.one_act] using h.symm

/-- Acting first by the inverse and then by sigma is the identity. -/
@[simp]
theorem action_inv_apply_right
    (a : GaloisSemilinearModuleAction K L M)
    (σ : L ≃ₐ[K] L) (m : M) :
    a.action σ (a.action σ⁻¹ m) = m := by
  have h :=
    congrArg (fun f : M →+ M => f m) (a.mul_act σ σ⁻¹)
  simpa [a.one_act] using h.symm

end GaloisSemilinearModuleAction

variable [Module K M] [IsScalarTower K L M]

/-- The orbit map of a semilinear action, regarded as a K-linear map. -/
private def galoisSemilinearOrbit
    (a : GaloisSemilinearModuleAction K L M) :
    M →ₗ[K] ((L ≃ₐ[K] L) → M) where
  toFun m σ := a.action σ m
  map_add' m n := by
    ext σ
    exact map_add (a.action σ) m n
  map_smul' k m := by
    ext σ
    rw [← IsScalarTower.algebraMap_smul L k m, a.semilinear]
    simp

/-- The canonical forward map for a semilinear module. -/
def galoisSemilinearTensorToFunctions
    (a : GaloisSemilinearModuleAction K L M) :
    TensorProduct K L M →ₗ[L] ((L ≃ₐ[K] L) → M) :=
  LinearMap.liftBaseChange L (galoisSemilinearOrbit K L M a)

/-- Pure-tensor formula for the semilinear forward map. -/
@[simp]
theorem galoisSemilinearTensorToFunctions_tmul_apply
    (a : GaloisSemilinearModuleAction K L M)
    (x : L) (m : M) (σ : L ≃ₐ[K] L) :
    galoisSemilinearTensorToFunctions K L M a (x ⊗ₜ[K] m) σ =
      x • a.action σ m := by
  simp [galoisSemilinearTensorToFunctions, galoisSemilinearOrbit]

/-- Bilinear map used to contract a tensor in L tensor[K] L against an
L-module element. -/
private def tensorModuleContractBilinear :
    L →ₗ[L] L →ₗ[K] (M →+ TensorProduct K L M) where
  toFun x :=
    { toFun := fun y =>
        { toFun := fun m => x ⊗ₜ[K] (y • m)
          map_zero' := by
            rw [smul_zero, TensorProduct.tmul_zero]
          map_add' := by
            intro m n
            rw [smul_add, TensorProduct.tmul_add] }
      map_add' := by
        intro y z
        ext m
        change
          x ⊗ₜ[K] ((y + z) • m) =
            x ⊗ₜ[K] (y • m) + x ⊗ₜ[K] (z • m)
        rw [add_smul, TensorProduct.tmul_add]
      map_smul' := by
        intro k y
        ext m
        change
          x ⊗ₜ[K] ((k • y) • m) =
            k • (x ⊗ₜ[K] (y • m))
        rw [IsScalarTower.smul_assoc, TensorProduct.tmul_smul] }
  map_add' := by
    intro x y
    ext z m
    change
      (x + y) ⊗ₜ[K] (z • m) =
        x ⊗ₜ[K] (z • m) + y ⊗ₜ[K] (z • m)
    rw [TensorProduct.add_tmul]
  map_smul' := by
    intro l x
    ext y m
    change
      (l • x) ⊗ₜ[K] (y • m) =
        l • (x ⊗ₜ[K] (y • m))
    exact (TensorProduct.smul_tmul' l x (y • m)).symm

/-- Contract a tensor in L tensor[K] L against an element of M. -/
def tensorModuleContract :
    TensorProduct K L L →ₗ[L] (M →+ TensorProduct K L M) :=
  TensorProduct.AlgebraTensorModule.lift
    (tensorModuleContractBilinear K L M)

/-- Contraction on a pure tensor. -/
@[simp]
theorem tensorModuleContract_tmul
    (x y : L) (m : M) :
    tensorModuleContract K L M (x ⊗ₜ[K] y) m =
      x ⊗ₜ[K] (y • m) := by
  simp [tensorModuleContract, tensorModuleContractBilinear]

/-- Multiplication on the right tensor factor can be moved into the module
argument of contraction. -/
theorem tensorModuleContract_mul_tmul_right
    (z : TensorProduct K L L) (y : L) (m : M) :
    tensorModuleContract K L M (z * (1 ⊗ₜ[K] y)) m =
      tensorModuleContract K L M z (y • m) := by
  induction z using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul x z =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul,
        tensorModuleContract_tmul, mul_smul]
      rw [mul_one]
  | add p q hp hq =>
      rw [add_mul, map_add, map_add]
      change
        tensorModuleContract K L M (p * (1 ⊗ₜ[K] y)) m +
            tensorModuleContract K L M (q * (1 ⊗ₜ[K] y)) m =
          tensorModuleContract K L M p (y • m) +
            tensorModuleContract K L M q (y • m)
      rw [hp, hq]

/-- In Galois coordinates, contraction multiplies the tensor coordinate by the
corresponding semilinear translate of the module element. -/
theorem galoisSemilinearTensorToFunctions_contract_apply
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M)
    (z : TensorProduct K L L) (m : M) (σ : L ≃ₐ[K] L) :
    galoisSemilinearTensorToFunctions K L M a
        (tensorModuleContract K L M z m) σ =
      galoisTensorEquiv K L z σ • a.action σ m := by
  induction z using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul x y =>
      rw [tensorModuleContract_tmul,
        galoisSemilinearTensorToFunctions_tmul_apply,
        a.semilinear, galoisTensorEquiv_tmul_apply, smul_smul]
  | add p q hp hq =>
      rw [map_add, map_add, Pi.add_apply, add_smul]
      change
        galoisSemilinearTensorToFunctions K L M a
            (tensorModuleContract K L M p m +
              tensorModuleContract K L M q m) σ =
          galoisTensorEquiv K L p σ • a.action σ m +
            galoisTensorEquiv K L q σ • a.action σ m
      rw [map_add, Pi.add_apply, hp, hq]

/-- The delta tensor at a Galois automorphism. -/
noncomputable def deltaTensor
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) : TensorProduct K L L := by
  classical
  exact (galoisTensorEquiv K L).symm (Pi.single σ 1)

/-- The delta tensor has coordinate one at its indexing automorphism. -/
@[simp]
theorem deltaTensor_same
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) :
    galoisTensorEquiv K L (deltaTensor K L σ) σ = 1 := by
  classical
  simp [deltaTensor]

/-- The delta tensor has coordinate zero away from its indexing automorphism. -/
theorem deltaTensor_ne
    [FiniteDimensional K L] [IsGalois K L]
    (σ τ : L ≃ₐ[K] L) (h : σ ≠ τ) :
    galoisTensorEquiv K L (deltaTensor K L σ) τ = 0 := by
  classical
  simp [deltaTensor, Ne.symm h]

/-- Delta-tensor reconstruction of a scalar in the first tensor factor. -/
theorem deltaTensor_sum_twist
    [FiniteDimensional K L] [IsGalois K L]
    (x : L) :
    (∑ σ : L ≃ₐ[K] L,
        deltaTensor K L σ * (1 ⊗ₜ[K] σ.symm x)) =
      x ⊗ₜ[K] 1 := by
  classical
  apply (galoisTensorEquiv K L).injective
  ext τ
  simp only [map_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single τ]
  · rw [map_mul]
    change
      galoisTensorEquiv K L (deltaTensor K L τ) τ *
          galoisTensorEquiv K L (1 ⊗ₜ[K] τ.symm x) τ =
        galoisTensorEquiv K L (x ⊗ₜ[K] 1) τ
    rw [deltaTensor_same]
    simp
  · intro σ _ h
    rw [map_mul]
    change
      galoisTensorEquiv K L (deltaTensor K L σ) τ *
          galoisTensorEquiv K L (1 ⊗ₜ[K] σ.symm x) τ =
        0
    rw [deltaTensor_ne K L σ τ h]
    simp
  · simp

/-- The explicit delta-tensor inverse of the semilinear forward map. -/
noncomputable def galoisSemilinearTensorInverse
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M) :
    ((L ≃ₐ[K] L) → M) →+ TensorProduct K L M where
  toFun f :=
    ∑ σ : L ≃ₐ[K] L,
      tensorModuleContract K L M (deltaTensor K L σ)
        (a.action σ⁻¹ (f σ))
  map_zero' := by
    classical
    simp
  map_add' f g := by
    classical
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]

/-- The forward map is a right inverse of the explicit delta-tensor inverse. -/
theorem galoisSemilinearTensor_forward_inverse
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M)
    (f : (L ≃ₐ[K] L) → M) :
    galoisSemilinearTensorToFunctions K L M a
        (galoisSemilinearTensorInverse K L M a f) =
      f := by
  classical
  ext τ
  change
    galoisSemilinearTensorToFunctions K L M a
        (∑ σ : L ≃ₐ[K] L,
          tensorModuleContract K L M (deltaTensor K L σ)
            (a.action σ⁻¹ (f σ))) τ =
      f τ
  rw [map_sum]
  simp only [Finset.sum_apply,
    galoisSemilinearTensorToFunctions_contract_apply]
  rw [Finset.sum_eq_single τ]
  · rw [deltaTensor_same]
    simp
  · intro σ _ h
    rw [deltaTensor_ne K L σ τ h]
    simp
  · simp

/-- The explicit inverse recovers a pure tensor after applying the forward
map. -/
theorem galoisSemilinearTensor_inverse_forward_tmul
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M)
    (x : L) (m : M) :
    galoisSemilinearTensorInverse K L M a
        (galoisSemilinearTensorToFunctions K L M a (x ⊗ₜ[K] m)) =
      x ⊗ₜ[K] m := by
  classical
  change
    (∑ σ : L ≃ₐ[K] L,
      tensorModuleContract K L M (deltaTensor K L σ)
        (a.action σ⁻¹ (x • a.action σ m))) =
      x ⊗ₜ[K] m
  have hact (σ : L ≃ₐ[K] L) :
      a.action σ⁻¹ (x • a.action σ m) = σ.symm x • m := by
    rw [a.semilinear, a.action_inv_apply_left]
    rfl
  simp_rw [hact]
  have hcontract (σ : L ≃ₐ[K] L) :
      tensorModuleContract K L M (deltaTensor K L σ)
          (σ.symm x • m) =
        tensorModuleContract K L M
          (deltaTensor K L σ * (1 ⊗ₜ[K] σ.symm x)) m :=
    (tensorModuleContract_mul_tmul_right K L M
      (deltaTensor K L σ) (σ.symm x) m).symm
  simp_rw [hcontract]
  have hsum :=
    congrArg
      (fun z : TensorProduct K L L => tensorModuleContract K L M z m)
      (deltaTensor_sum_twist K L x)
  rw [map_sum] at hsum
  rw [AddMonoidHom.coe_finsetSum, Finset.sum_apply] at hsum
  change
    (∑ σ : L ≃ₐ[K] L,
      tensorModuleContract K L M
        (deltaTensor K L σ * (1 ⊗ₜ[K] σ.symm x)) m) =
      tensorModuleContract K L M (x ⊗ₜ[K] 1) m at hsum
  rw [hsum]
  simp

/-- The explicit inverse is a left inverse of the semilinear forward map. -/
theorem galoisSemilinearTensor_inverse_forward
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M)
    (z : TensorProduct K L M) :
    galoisSemilinearTensorInverse K L M a
        (galoisSemilinearTensorToFunctions K L M a z) =
      z := by
  induction z using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul x m =>
      exact galoisSemilinearTensor_inverse_forward_tmul K L M a x m
  | add p q hp hq =>
      rw [map_add, map_add, hp, hq]

/-- Bijectivity of the canonical semilinear tensor map. -/
theorem galoisSemilinearTensorToFunctions_bijective
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M) :
    Function.Bijective
      (galoisSemilinearTensorToFunctions K L M a) :=
  ⟨Function.LeftInverse.injective
      (galoisSemilinearTensor_inverse_forward K L M a),
    Function.RightInverse.surjective
      (galoisSemilinearTensor_forward_inverse K L M a)⟩

/-- The finite-Galois semilinear module tensor equivalence. -/
noncomputable def galoisSemilinearTensorEquiv
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M) :
    TensorProduct K L M ≃ₗ[L] ((L ≃ₐ[K] L) → M) :=
  LinearEquiv.ofBijective
    (galoisSemilinearTensorToFunctions K L M a)
    (galoisSemilinearTensorToFunctions_bijective K L M a)

/-- The semilinear tensor equivalence is the canonical forward map. -/
@[simp]
theorem galoisSemilinearTensorEquiv_apply
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M)
    (z : TensorProduct K L M) :
    galoisSemilinearTensorEquiv K L M a z =
      galoisSemilinearTensorToFunctions K L M a z := by
  rw [galoisSemilinearTensorEquiv, LinearEquiv.ofBijective_apply]

/-- Pure-tensor formula for the finite-Galois semilinear equivalence. -/
@[simp]
theorem galoisSemilinearTensorEquiv_tmul_apply
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M)
    (x : L) (m : M) (σ : L ≃ₐ[K] L) :
    galoisSemilinearTensorEquiv K L M a (x ⊗ₜ[K] m) σ =
      x • a.action σ m := by
  rw [galoisSemilinearTensorEquiv_apply]
  exact galoisSemilinearTensorToFunctions_tmul_apply K L M a x m σ

/-- The inverse of the equivalence is the explicit delta-tensor formula. -/
@[simp]
theorem galoisSemilinearTensorEquiv_symm_apply
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M)
    (f : (L ≃ₐ[K] L) → M) :
    (galoisSemilinearTensorEquiv K L M a).symm f =
      galoisSemilinearTensorInverse K L M a f := by
  apply (galoisSemilinearTensorEquiv K L M a).injective
  rw [LinearEquiv.apply_symm_apply, galoisSemilinearTensorEquiv_apply,
    galoisSemilinearTensor_forward_inverse]

end

end RiemannResearch.GaloisCohomology
