/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.GaloisCohomology.GaloisSemilinearModuleCoaction

/-!
# Galois semilinear algebra coordinates and coaction

For a finite Galois extension L/K, an action on an L-algebra by
K-algebra equivalences which is semilinear over L upgrades the existing
module-valued Galois tensor equivalence to an L-algebra equivalence

    L ⊗[K] A ≃ₐ[L] ((L ≃ₐ[K] L) → A).

The inverse image of constant functions is consequently an L-algebra
homomorphism.  Its underlying linear map is definitionally the previously
constructed module coaction, so the established counit and coassociativity
theorems remain directly reusable.

Source: user-provided finite-Galois algebra-descent argument.  The tensor
coordinate calculation is the algebra-valued refinement of
GaloisSemilinearModuleDescent.
-/

namespace RiemannResearch.GaloisCohomology

noncomputable section

universe u

/-- An action on an L-algebra by K-algebra equivalences, together with
its semilinearity over L. -/
structure GaloisSemilinearAlgebraAction
    (K L A : Type u) [Field K] [Field L] [Algebra K L]
    [CommRing A] [Algebra K A] [Algebra L A] [IsScalarTower K L A] where
  action : (L ≃ₐ[K] L) →* AlgEquiv K A A
  semilinear : ∀ σ l a, action σ (l • a) = σ l • action σ a

variable (K L A : Type u) [Field K] [Field L] [Algebra K L]
variable [CommRing A] [Algebra K A] [Algebra L A] [IsScalarTower K L A]

namespace GaloisSemilinearAlgebraAction

/-- Forget multiplication and the unit in a semilinear algebra action. -/
def toModuleAction (a : GaloisSemilinearAlgebraAction K L A) :
    GaloisSemilinearModuleAction K L A where
  action σ := (a.action σ).toAddEquiv.toAddMonoidHom
  one_act := by
    ext x
    exact congrArg (fun e : A ≃ₐ[K] A => e x) a.action.map_one
  mul_act σ τ := by
    ext x
    exact congrArg (fun e : A ≃ₐ[K] A => e x) (a.action.map_mul σ τ)
  semilinear := a.semilinear

/-- The forgotten additive action evaluates as the original algebra action. -/
@[simp] theorem toModuleAction_apply
    (a : GaloisSemilinearAlgebraAction K L A)
    (σ : L ≃ₐ[K] L) (x : A) :
    (a.toModuleAction K L A).action σ x = a.action σ x :=
  rfl

end GaloisSemilinearAlgebraAction

/-- The module-valued Galois tensor equivalence preserves the unit when the
semilinear action is algebra-valued. -/
theorem galoisSemilinearTensorEquiv_map_one
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearAlgebraAction K L A) :
    galoisSemilinearTensorEquiv K L A (a.toModuleAction K L A)
        (1 : TensorProduct K L A) =
      (1 : (L ≃ₐ[K] L) → A) := by
  ext σ
  simp [Algebra.TensorProduct.one_def]

/-- The module-valued Galois tensor equivalence preserves multiplication when
the semilinear action is algebra-valued. -/
theorem galoisSemilinearTensorEquiv_map_mul
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearAlgebraAction K L A)
    (x y : TensorProduct K L A) :
    galoisSemilinearTensorEquiv K L A (a.toModuleAction K L A) (x * y) =
      galoisSemilinearTensorEquiv K L A (a.toModuleAction K L A) x *
        galoisSemilinearTensorEquiv K L A (a.toModuleAction K L A) y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l b =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul m c =>
          ext σ
          simp [Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def]
          ac_rfl
      | add y z hy hz =>
          simp only [mul_add, map_add, hy, hz]
  | add x y hx hy =>
      simp only [add_mul, map_add, hx, hy]

/-- The finite-Galois semilinear tensor coordinates as an algebra
equivalence.  This reuses the existing linear equivalence rather than
constructing a second tensor isomorphism. -/
noncomputable def galoisSemilinearTensorAlgEquiv
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearAlgebraAction K L A) :
    TensorProduct K L A ≃ₐ[L] ((L ≃ₐ[K] L) → A) :=
  AlgEquiv.ofLinearEquiv
    (galoisSemilinearTensorEquiv K L A (a.toModuleAction K L A))
    (galoisSemilinearTensorEquiv_map_one K L A a)
    (galoisSemilinearTensorEquiv_map_mul K L A a)

/-- The algebra coordinate equivalence has exactly the previously verified
underlying linear equivalence. -/
@[simp] theorem galoisSemilinearTensorAlgEquiv_toLinearEquiv
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearAlgebraAction K L A) :
    (galoisSemilinearTensorAlgEquiv K L A a).toLinearEquiv =
      galoisSemilinearTensorEquiv K L A (a.toModuleAction K L A) := by
  rfl

/-- The diagonal algebra homomorphism to constant Galois-indexed functions. -/
def galoisConstantFunctionsAlgHom :
    A →ₐ[L] ((L ≃ₐ[K] L) → A) :=
  AlgHom.pi (fun _ : L ≃ₐ[K] L => AlgHom.id L A)

/-- The algebra-valued semilinear descent coaction: the inverse tensor
coordinate image of constant functions. -/
noncomputable def galoisSemilinearAlgebraCoaction
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearAlgebraAction K L A) :
    A →ₐ[L] TensorProduct K L A :=
  (galoisSemilinearTensorAlgEquiv K L A a).symm.toAlgHom.comp
    (galoisConstantFunctionsAlgHom K L A)

/-- The algebra-valued coaction is exactly the existing module coaction after
forgetting multiplication. -/
theorem galoisSemilinearAlgebraCoaction_toLinearMap
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearAlgebraAction K L A) :
    (galoisSemilinearAlgebraCoaction K L A a).toLinearMap =
      galoisSemilinearCoaction K L A (a.toModuleAction K L A) := by
  rfl

/-- The existing semilinear module coaction preserves the algebra unit. -/
@[simp] theorem galoisSemilinearCoaction_one
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearAlgebraAction K L A) :
    galoisSemilinearCoaction K L A (a.toModuleAction K L A) 1 = 1 := by
  rw [← galoisSemilinearAlgebraCoaction_toLinearMap K L A a]
  exact map_one (galoisSemilinearAlgebraCoaction K L A a)

/-- The existing semilinear module coaction preserves multiplication. -/
theorem galoisSemilinearCoaction_mul
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearAlgebraAction K L A) (x y : A) :
    galoisSemilinearCoaction K L A (a.toModuleAction K L A) (x * y) =
      galoisSemilinearCoaction K L A (a.toModuleAction K L A) x *
        galoisSemilinearCoaction K L A (a.toModuleAction K L A) y := by
  rw [← galoisSemilinearAlgebraCoaction_toLinearMap K L A a]
  exact map_mul (galoisSemilinearAlgebraCoaction K L A a) x y

end

end RiemannResearch.GaloisCohomology
