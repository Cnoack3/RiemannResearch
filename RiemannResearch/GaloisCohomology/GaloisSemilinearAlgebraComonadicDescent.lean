/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.GaloisCohomology.GaloisSemilinearAlgebraCoaction
import RiemannResearch.GaloisCohomology.GaloisSemilinearModuleComonadicDescent

/-!
# Algebra structure maps in finite-Galois comonadic descent

For a finite Galois extension L/K and a semilinear action on a commutative
L-algebra A, this module constructs the diagonal action on A tensor[L] A and
packages the algebra unit and multiplication as morphisms of the existing
extension--restriction coalgebras.

This is the first effective-algebra-descent compatibility layer. It does not
yet transport the maps to the selected descended K-module or assert a
descended algebra, Hopf algebra, affine group scheme, or torsor classifier.

Source: user-provided finite-Galois algebra-descent argument. The categorical
step uses the naturality bridge in GaloisSemilinearModuleComonadicDescent and
the multiplication law from GaloisSemilinearAlgebraCoaction.
-/

namespace RiemannResearch.GaloisCohomology

noncomputable section

universe u

variable (K L A : Type u) [Field K] [Field L] [Algebra K L]
variable [CommRing A] [Algebra K A] [Algebra L A] [IsScalarTower K L A]

/-- An algebra-valued semilinear action, regarded as a semilinear map for one
fixed Galois automorphism. -/
def galoisSemilinearAlgebraActionSemilinearMap
    (a : GaloisSemilinearAlgebraAction K L A)
    (σ : L ≃ₐ[K] L) : A →ₛₗ[σ.toRingHom] A where
  toFun := a.action σ
  map_add' := map_add (a.action σ)
  map_smul' := a.semilinear σ

@[simp] theorem galoisSemilinearAlgebraActionSemilinearMap_apply
    (a : GaloisSemilinearAlgebraAction K L A)
    (σ : L ≃ₐ[K] L) (x : A) :
    galoisSemilinearAlgebraActionSemilinearMap K L A a σ x =
      a.action σ x :=
  rfl

/-- The tautological semilinear algebra action of Gal(L/K) on L. -/
def galoisScalarSemilinearAlgebraAction :
    GaloisSemilinearAlgebraAction K L L where
  action := MonoidHom.id _
  semilinear σ l x := σ.map_mul l x

@[simp] theorem galoisScalarSemilinearAlgebraAction_apply
    (σ : L ≃ₐ[K] L) (x : L) :
    (galoisScalarSemilinearAlgebraAction K L).action σ x = σ x :=
  rfl

/-- The diagonal semilinear action on A tensor[L] A. -/
def galoisSemilinearTensorSquareAction
    (a : GaloisSemilinearAlgebraAction K L A) :
    GaloisSemilinearModuleAction K L (TensorProduct L A A) where
  action σ :=
    (TensorProduct.map
      (galoisSemilinearAlgebraActionSemilinearMap K L A a σ)
      (galoisSemilinearAlgebraActionSemilinearMap K L A a σ)).toAddHom
  one_act := by
    ext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
        simp [galoisSemilinearAlgebraActionSemilinearMap]
    | add x y hx hy => simp only [map_add, hx, hy]
  mul_act σ τ := by
    ext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
        simp [galoisSemilinearAlgebraActionSemilinearMap]
        rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  semilinear σ l z :=
    (TensorProduct.map
      (galoisSemilinearAlgebraActionSemilinearMap K L A a σ)
      (galoisSemilinearAlgebraActionSemilinearMap K L A a σ)).map_smul' l z

@[simp] theorem galoisSemilinearTensorSquareAction_tmul
    (a : GaloisSemilinearAlgebraAction K L A)
    (σ : L ≃ₐ[K] L) (x y : A) :
    (galoisSemilinearTensorSquareAction K L A a).action σ
        (x ⊗ₜ[L] y) =
      a.action σ x ⊗ₜ[L] a.action σ y := by
  simp [galoisSemilinearTensorSquareAction,
    galoisSemilinearAlgebraActionSemilinearMap]
  rfl

/-- Multiplication of A as an L-linear map out of A tensor[L] A. -/
def galoisAlgebraMultiplicationLinearMap :
    TensorProduct L A A →ₗ[L] A :=
  TensorProduct.lift (LinearMap.mul L A)

@[simp] theorem galoisAlgebraMultiplicationLinearMap_tmul
    (x y : A) :
    galoisAlgebraMultiplicationLinearMap L A (x ⊗ₜ[L] y) = x * y := by
  simp [galoisAlgebraMultiplicationLinearMap]

/-- The algebra unit is equivariant for the scalar and algebra actions. -/
theorem galoisSemilinearAlgebraUnit_equivariant
    (a : GaloisSemilinearAlgebraAction K L A)
    (σ : L ≃ₐ[K] L) (l : L) :
    a.action σ (Algebra.linearMap L A l) =
      Algebra.linearMap L A
        ((galoisScalarSemilinearAlgebraAction K L).action σ l) := by
  have h := a.semilinear σ l (1 : A)
  simpa [Algebra.smul_def] using h

/-- Algebra multiplication is equivariant for the diagonal tensor-square
action. -/
theorem galoisSemilinearAlgebraMul_equivariant
    (a : GaloisSemilinearAlgebraAction K L A)
    (σ : L ≃ₐ[K] L) (z : TensorProduct L A A) :
    a.action σ (galoisAlgebraMultiplicationLinearMap L A z) =
      galoisAlgebraMultiplicationLinearMap L A
        ((galoisSemilinearTensorSquareAction K L A a).action σ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      simp only [galoisAlgebraMultiplicationLinearMap_tmul,
        galoisSemilinearTensorSquareAction_tmul]
      exact (a.action σ).map_mul x y
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The raw coaction commutes with the algebra unit. -/
theorem galoisSemilinearAlgebraUnit_coaction
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearAlgebraAction K L A) (l : L) :
    LinearMap.baseChange L ((Algebra.linearMap L A).restrictScalars K)
        (galoisSemilinearCoaction K L L
          ((galoisScalarSemilinearAlgebraAction K L).toModuleAction K L L) l) =
      galoisSemilinearCoaction K L A (a.toModuleAction K L A)
        (Algebra.linearMap L A l) :=
  galoisSemilinearCoaction_natural K L L A
    ((galoisScalarSemilinearAlgebraAction K L).toModuleAction K L L)
    (a.toModuleAction K L A) (Algebra.linearMap L A)
    (galoisSemilinearAlgebraUnit_equivariant K L A a) l

/-- The raw coaction commutes with algebra multiplication. -/
theorem galoisSemilinearAlgebraMul_coaction
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearAlgebraAction K L A)
    (z : TensorProduct L A A) :
    LinearMap.baseChange L
        ((galoisAlgebraMultiplicationLinearMap L A).restrictScalars K)
        (galoisSemilinearCoaction K L (TensorProduct L A A)
          (galoisSemilinearTensorSquareAction K L A a) z) =
      galoisSemilinearCoaction K L A (a.toModuleAction K L A)
        (galoisAlgebraMultiplicationLinearMap L A z) :=
  galoisSemilinearCoaction_natural K L (TensorProduct L A A) A
    (galoisSemilinearTensorSquareAction K L A a)
    (a.toModuleAction K L A) (galoisAlgebraMultiplicationLinearMap L A)
    (galoisSemilinearAlgebraMul_equivariant K L A a) z

/-- On a pure tensor, multiplication naturality is exactly multiplicativity
of the established algebra-valued coaction. -/
theorem galoisSemilinearAlgebraMul_coaction_tmul
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearAlgebraAction K L A) (x y : A) :
    LinearMap.baseChange L
        ((galoisAlgebraMultiplicationLinearMap L A).restrictScalars K)
        (galoisSemilinearCoaction K L (TensorProduct L A A)
          (galoisSemilinearTensorSquareAction K L A a) (x ⊗ₜ[L] y)) =
      galoisSemilinearCoaction K L A (a.toModuleAction K L A) x *
        galoisSemilinearCoaction K L A (a.toModuleAction K L A) y := by
  rw [galoisSemilinearAlgebraMul_coaction K L A a,
    galoisAlgebraMultiplicationLinearMap_tmul,
    galoisSemilinearCoaction_mul K L A a]

/-- The algebra unit as a morphism of extension--restriction coalgebras. -/
noncomputable def galoisSemilinearAlgebraUnitDescentMap
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearAlgebraAction K L A) :
    galoisSemilinearComonadicDescentData K L L
        ((galoisScalarSemilinearAlgebraAction K L).toModuleAction K L L) ⟶
      galoisSemilinearComonadicDescentData K L A
        (a.toModuleAction K L A) :=
  galoisSemilinearComonadicDescentMap K L L A
    ((galoisScalarSemilinearAlgebraAction K L).toModuleAction K L L)
    (a.toModuleAction K L A) (Algebra.linearMap L A)
    (galoisSemilinearAlgebraUnit_equivariant K L A a)

/-- Algebra multiplication as a morphism of extension--restriction
coalgebras. -/
noncomputable def galoisSemilinearAlgebraMulDescentMap
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearAlgebraAction K L A) :
    galoisSemilinearComonadicDescentData K L (TensorProduct L A A)
        (galoisSemilinearTensorSquareAction K L A a) ⟶
      galoisSemilinearComonadicDescentData K L A
        (a.toModuleAction K L A) :=
  galoisSemilinearComonadicDescentMap K L (TensorProduct L A A) A
    (galoisSemilinearTensorSquareAction K L A a)
    (a.toModuleAction K L A)
    (galoisAlgebraMultiplicationLinearMap L A)
    (galoisSemilinearAlgebraMul_equivariant K L A a)

@[simp] theorem galoisSemilinearAlgebraUnitDescentMap_f
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearAlgebraAction K L A) :
    (galoisSemilinearAlgebraUnitDescentMap K L A a).f =
      ModuleCat.ofHom (Algebra.linearMap L A) :=
  rfl

@[simp] theorem galoisSemilinearAlgebraMulDescentMap_f
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearAlgebraAction K L A) :
    (galoisSemilinearAlgebraMulDescentMap K L A a).f =
      ModuleCat.ofHom (galoisAlgebraMultiplicationLinearMap L A) :=
  rfl

end

end RiemannResearch.GaloisCohomology
