/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.GaloisCohomology.GaloisSemilinearAlgebraComonadicDescent

/-!
# Effective transport of finite-Galois semilinear algebra maps

This module applies the inverse faithfully-flat comonadic equivalence to
finite-Galois semilinear module maps and compares that inverse choice with the
selected Cech-descended module. It transports the algebra unit and
multiplication to maps between the selected descended modules.

It also constructs the scalar-extension tensor comparison. The remaining
boundary is descent compatibility of that comparison; no multiplication on the
tensor square of the descended module, descended algebra, or Hopf algebra is
asserted.

Source: user-provided finite-Galois algebra-descent program. The tensor
comparison uses Mathlib's distributivity of base change over tensor products.
-/

namespace RiemannResearch.GaloisCohomology

noncomputable section

universe u

open CategoryTheory
open RiemannResearch.AlgebraicGeometry

variable (K L M : Type u) [Field K] [Field L] [Algebra K L]
variable [AddCommGroup M] [Module K M] [Module L M] [IsScalarTower K L M]

noncomputable def galoisSemilinearComonadicInverseModule
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M) : ModuleCat K :=
  (comonadicModuleDescentEquivalence
    (galoisFieldAlgebraMap_faithfullyFlat K L)).inverse.obj
      (galoisSemilinearComonadicDescentData K L M a)

noncomputable def galoisSemilinearComonadicInverseBaseChangeIso
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M) :
    (ModuleCat.extendScalars (algebraMap K L)).obj
        (galoisSemilinearComonadicInverseModule K L M a) ≅
      ModuleCat.of L M :=
  (comonadicModuleDescentComparisonForgetIso (algebraMap K L)).symm.app
      (galoisSemilinearComonadicInverseModule K L M a) ≪≫
    (ComonadicModuleDescentData.forget (algebraMap K L)).mapIso
      ((comonadicModuleDescentEquivalence
        (galoisFieldAlgebraMap_faithfullyFlat K L)).counitIso.app
          (galoisSemilinearComonadicDescentData K L M a))

noncomputable def galoisSemilinearDescendedModuleComonadicInverseIso
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M) :
    galoisSemilinearDescendedModule K L M a ≅
      galoisSemilinearComonadicInverseModule K L M a := by
  let f := CommRingCat.ofHom (algebraMap K L)
  let hf := galoisFieldAlgebraMap_faithfullyFlat K L
  let B := affineCechComonadicBridge f
  let E := comonadicModuleDescentEquivalence hf
  let Q := galoisSemilinearComonadicDescentData K L M a
  let D := galoisSemilinearCechModuleDescentData K L M a
  let N := galoisSemilinearDescendedModule K L M a
  let iC : (affineCechModuleDescentComparison f).obj N ≅ D :=
    affineCechDescendedModuleIso f hf D
  let iQ : E.functor.obj N ≅ Q :=
    (B.comparisonIso.app N).symm ≪≫
      B.equivalence.functor.mapIso iC ≪≫
      B.equivalence.counitIso.app Q
  exact E.unitIso.app N ≪≫ E.inverse.mapIso iQ

section Maps

variable (N : Type u)
variable [AddCommGroup N] [Module K N] [Module L N] [IsScalarTower K L N]

noncomputable def galoisSemilinearComonadicInverseMap
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M)
    (b : GaloisSemilinearModuleAction K L N)
    (f : M →ₗ[L] N)
    (hf : ∀ σ m, b.action σ (f m) = f (a.action σ m)) :
    galoisSemilinearComonadicInverseModule K L M a ⟶
      galoisSemilinearComonadicInverseModule K L N b :=
  (comonadicModuleDescentEquivalence
    (galoisFieldAlgebraMap_faithfullyFlat K L)).inverse.map
      (galoisSemilinearComonadicDescentMap K L M N a b f hf)

theorem galoisSemilinearComonadicInverseMap_recover
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M)
    (b : GaloisSemilinearModuleAction K L N)
    (f : M →ₗ[L] N)
    (hf : ∀ σ m, b.action σ (f m) = f (a.action σ m)) :
    let E := comonadicModuleDescentEquivalence
      (galoisFieldAlgebraMap_faithfullyFlat K L)
    let Q := galoisSemilinearComonadicDescentData K L M a
    let Q' := galoisSemilinearComonadicDescentData K L N b
    E.functor.map (galoisSemilinearComonadicInverseMap
        K L M N a b f hf) ≫
        E.counitIso.hom.app Q' =
      E.counitIso.hom.app Q ≫
        galoisSemilinearComonadicDescentMap K L M N a b f hf := by
  dsimp only
  exact (comonadicModuleDescentEquivalence
    (galoisFieldAlgebraMap_faithfullyFlat K L)).counitIso.hom.naturality
      (galoisSemilinearComonadicDescentMap K L M N a b f hf)

noncomputable def galoisSemilinearDescendedMap
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M)
    (b : GaloisSemilinearModuleAction K L N)
    (f : M →ₗ[L] N)
    (hf : ∀ σ m, b.action σ (f m) = f (a.action σ m)) :
    galoisSemilinearDescendedModule K L M a ⟶
      galoisSemilinearDescendedModule K L N b :=
  (galoisSemilinearDescendedModuleComonadicInverseIso K L M a).hom ≫
    galoisSemilinearComonadicInverseMap K L M N a b f hf ≫
    (galoisSemilinearDescendedModuleComonadicInverseIso K L N b).inv

end Maps

variable (A : Type u)
variable [CommRing A] [Algebra K A] [Algebra L A] [IsScalarTower K L A]

noncomputable def galoisSemilinearAlgebraUnitDescendedMap
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearAlgebraAction K L A) :
    galoisSemilinearDescendedModule K L L
        ((galoisScalarSemilinearAlgebraAction K L).toModuleAction K L L) ⟶
      galoisSemilinearDescendedModule K L A
        (a.toModuleAction K L A) :=
  galoisSemilinearDescendedMap K L L A
    ((galoisScalarSemilinearAlgebraAction K L).toModuleAction K L L)
    (a.toModuleAction K L A)
    (Algebra.linearMap L A)
    (galoisSemilinearAlgebraUnit_equivariant K L A a)

noncomputable def galoisSemilinearAlgebraMulDescendedMap
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearAlgebraAction K L A) :
    galoisSemilinearDescendedModule K L (TensorProduct L A A)
        (galoisSemilinearTensorSquareAction K L A a) ⟶
      galoisSemilinearDescendedModule K L A
        (a.toModuleAction K L A) :=
  galoisSemilinearDescendedMap K L (TensorProduct L A A) A
    (galoisSemilinearTensorSquareAction K L A a)
    (a.toModuleAction K L A)
    (galoisAlgebraMultiplicationLinearMap L A)
    (galoisSemilinearAlgebraMul_equivariant K L A a)

private noncomputable def galoisEffectiveScalarRestrictLinearEquiv :
    L ≃ₗ[L]
      ((ModuleCat.restrictScalars (algebraMap K L)).obj
        (ModuleCat.of L L)) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def galoisSemilinearDescendedTensorBaseChangeIso
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearAlgebraAction K L A) :
    (ModuleCat.extendScalars (algebraMap K L)).obj
        (ModuleCat.of K
          (TensorProduct K
            (galoisSemilinearDescendedModule K L A
              (a.toModuleAction K L A))
            (galoisSemilinearDescendedModule K L A
              (a.toModuleAction K L A)))) ≅
      ModuleCat.of L (TensorProduct L A A) := by
  let D := galoisSemilinearDescendedModule K L A
    (a.toModuleAction K L A)
  let e := galoisSemilinearDescendedModuleBaseChangeIso K L A
    (a.toModuleAction K L A)
  let LK := (ModuleCat.restrictScalars (algebraMap K L)).obj
    (ModuleCat.of L L)
  letI : Module K LK := LK.isModule
  letI : IsScalarTower K L LK :=
    IsScalarTower.of_algebraMap_smul (by intro k x; rfl)
  let eRaw : TensorProduct K L D ≃ₗ[L] A :=
    (TensorProduct.AlgebraTensorModule.congr
      (galoisEffectiveScalarRestrictLinearEquiv K L)
      (LinearEquiv.refl K D)).trans e.toLinearEquiv
  change ModuleCat.of L (TensorProduct K LK (TensorProduct K D D)) ≅
    ModuleCat.of L (TensorProduct L A A)
  exact ((TensorProduct.AlgebraTensorModule.congr
      (galoisEffectiveScalarRestrictLinearEquiv K L).symm
      (LinearEquiv.refl K (TensorProduct K D D))).trans
    ((TensorProduct.AlgebraTensorModule.distribBaseChange K L D D).trans
      (TensorProduct.congr eRaw eRaw))).toModuleIso

noncomputable def galoisSemilinearDescendedTensorComparisonBaseChangeIso
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearAlgebraAction K L A) :
    (ModuleCat.extendScalars (algebraMap K L)).obj
        (ModuleCat.of K
          (TensorProduct K
            (galoisSemilinearDescendedModule K L A
              (a.toModuleAction K L A))
            (galoisSemilinearDescendedModule K L A
              (a.toModuleAction K L A)))) ≅
      (ModuleCat.extendScalars (algebraMap K L)).obj
        (galoisSemilinearDescendedModule K L (TensorProduct L A A)
          (galoisSemilinearTensorSquareAction K L A a)) :=
  galoisSemilinearDescendedTensorBaseChangeIso K L A a ≪≫
    (galoisSemilinearDescendedModuleBaseChangeIso K L
      (TensorProduct L A A)
      (galoisSemilinearTensorSquareAction K L A a)).symm

end

end RiemannResearch.GaloisCohomology
