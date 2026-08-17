/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.AffineModuleComonadicBridge
import RiemannResearch.GaloisCohomology.GaloisSemilinearModuleCoassociativity

/-!
# Comonadic descent data from a finite-Galois semilinear action

This module transports the raw tensor coaction for a finite-Galois semilinear
module into Mathlib's extension--restriction comonad. The transport is explicit
because the raw tensor product and the categorical comonad carrier use
propositionally equal, but not definitionally identical, restricted-scalar
module structures.

The transported coaction satisfies the comonad counit and coassociativity laws,
and hence defines an extension--restriction coalgebra.

This is an underlying-module result. No multiplication, Hopf structure,
affine group scheme, or torsor descent is asserted here.

Source: user-provided argument. The proof uses the raw coassociativity theorem
from GaloisSemilinearModuleCoassociativity and the extension--restriction
comonad from Mathlib.
-/

namespace RiemannResearch.GaloisCohomology

noncomputable section

universe u

open CategoryTheory
open RiemannResearch.AlgebraicGeometry

variable (K L M : Type u) [Field K] [Field L] [Algebra K L]
variable [AddCommGroup M] [Module K M] [Module L M] [IsScalarTower K L M]

/-- Identity on the module, viewed as an equivalence to categorical
restriction of scalars. -/
private noncomputable def galoisModuleRestrictLinearEquiv :
    M ≃ₗ[K]
      ((ModuleCat.restrictScalars (algebraMap K L)).obj
        (ModuleCat.of L M)) where
  toFun m := m
  invFun m := m
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' k m := by
    change k • m = (algebraMap K L k) • m
    exact (IsScalarTower.algebraMap_smul L k m).symm

/-- Identity on L, viewed as an L-linear equivalence to the carrier of its
categorical restriction of scalars. -/
private noncomputable def galoisScalarRestrictLinearEquiv :
    L ≃ₗ[L]
      ((ModuleCat.restrictScalars (algebraMap K L)).obj
        (ModuleCat.of L L)) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Canonical normalization from the raw tensor module to the carrier of the
extension--restriction comonad. -/
noncomputable def galoisSemilinearComonadicTensorEquiv :
    TensorProduct K L M ≃ₗ[L]
      ((ModuleCat.extendRestrictScalarsAdj (algebraMap K L)).toComonad).obj
        (ModuleCat.of L M) := by
  let LK := (ModuleCat.restrictScalars (algebraMap K L)).obj
    (ModuleCat.of L L)
  letI : Module K LK := LK.isModule
  letI : IsScalarTower K L LK :=
    IsScalarTower.of_algebraMap_smul (by intro k x; rfl)
  change
    TensorProduct K L M ≃ₗ[L]
      TensorProduct K LK
        ((ModuleCat.restrictScalars (algebraMap K L)).obj
          (ModuleCat.of L M))
  exact TensorProduct.AlgebraTensorModule.congr
    (galoisScalarRestrictLinearEquiv K L)
    (galoisModuleRestrictLinearEquiv K L M)

/-- Canonical normalization one tensor level higher, from raw right-associated
triple tensors to the twice-applied comonad carrier. -/
noncomputable def galoisSemilinearComonadicDoubleTensorEquiv :
    TensorProduct K L (TensorProduct K L M) ≃ₗ[L]
      ((ModuleCat.extendRestrictScalarsAdj
        (algebraMap K L)).toComonad).obj
        (((ModuleCat.extendRestrictScalarsAdj
          (algebraMap K L)).toComonad).obj (ModuleCat.of L M)) := by
  let f := algebraMap K L
  let G := (ModuleCat.extendRestrictScalarsAdj f).toComonad
  let A := ModuleCat.of L M
  let GA := G.obj A
  let N := ↑GA
  letI : Module L N := GA.isModule
  letI : Module K N := Module.compHom N f
  letI : IsScalarTower K L N :=
    IsScalarTower.of_algebraMap_smul (by intro k n; rfl)
  let inner :
      TensorProduct K L M ≃ₗ[K]
        ((ModuleCat.restrictScalars f).obj GA) :=
    ((galoisSemilinearComonadicTensorEquiv K L M).restrictScalars K).trans
      (galoisModuleRestrictLinearEquiv K L N)
  let LK := (ModuleCat.restrictScalars f).obj (ModuleCat.of L L)
  letI : Module K LK := LK.isModule
  letI : IsScalarTower K L LK :=
    IsScalarTower.of_algebraMap_smul (by intro k x; rfl)
  change
    TensorProduct K L (TensorProduct K L M) ≃ₗ[L]
      TensorProduct K LK ((ModuleCat.restrictScalars f).obj GA)
  exact TensorProduct.AlgebraTensorModule.congr
    (galoisScalarRestrictLinearEquiv K L) inner

/-- The raw coaction transported to the categorical comonad carrier. -/
noncomputable def galoisSemilinearComonadicCoaction
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M) :
    ModuleCat.of L M ⟶
      ((ModuleCat.extendRestrictScalarsAdj (algebraMap K L)).toComonad).obj
        (ModuleCat.of L M) := by
  refine ConcreteCategory.ofHom ?_
  exact
    (galoisSemilinearComonadicTensorEquiv K L M).toLinearMap.comp
      (galoisSemilinearCoaction K L M a)

/-- The categorical counit is the raw tensor counit after normalization. -/
theorem galoisSemilinearComonadicTensorCounit
    (z : TensorProduct K L M) :
    ConcreteCategory.hom
        ((ModuleCat.extendRestrictScalarsAdj
          (algebraMap K L)).toComonad.ε.app (ModuleCat.of L M))
        (galoisSemilinearComonadicTensorEquiv K L M z) =
      galoisSemilinearTensorCounit K L M z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x m =>
      change x • m = x • m
      rfl
  | add p q hp hq =>
      simpa only [map_add] using congrArg₂ (· + ·) hp hq

/-- Categorical comultiplication corresponds to raw tensor
comultiplication under normalization. -/
theorem galoisSemilinearComonadicTensorComultiplication
    (z : TensorProduct K L M) :
    ConcreteCategory.hom
        ((ModuleCat.extendRestrictScalarsAdj
          (algebraMap K L)).toComonad.δ.app (ModuleCat.of L M))
        (galoisSemilinearComonadicTensorEquiv K L M z) =
      galoisSemilinearComonadicDoubleTensorEquiv K L M
        (galoisSemilinearTensorComultiplication K L M z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x m => rfl
  | add p q hp hq =>
      simpa only [map_add] using congrArg₂ (· + ·) hp hq

/-- Mapping the transported coaction through the comonad corresponds to
applying the raw coaction in the module tensor factor. -/
theorem galoisSemilinearComonadicTensorMapCoaction
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M)
    (z : TensorProduct K L M) :
    ConcreteCategory.hom
        (((ModuleCat.extendRestrictScalarsAdj
          (algebraMap K L)).toComonad).map
            (galoisSemilinearComonadicCoaction K L M a))
        (galoisSemilinearComonadicTensorEquiv K L M z) =
      galoisSemilinearComonadicDoubleTensorEquiv K L M
        (galoisSemilinearTensorMapCoaction K L M a z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x m => rfl
  | add p q hp hq =>
      simpa only [map_add] using congrArg₂ (· + ·) hp hq

/-- The transported coaction satisfies the comonad counit law. -/
theorem galoisSemilinearComonadicCoaction_counit
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M) :
    galoisSemilinearComonadicCoaction K L M a ≫
        ((ModuleCat.extendRestrictScalarsAdj
          (algebraMap K L)).toComonad).ε.app (ModuleCat.of L M) =
      𝟙 (ModuleCat.of L M) := by
  apply ModuleCat.hom_ext
  ext m
  change
    ConcreteCategory.hom
        ((ModuleCat.extendRestrictScalarsAdj
          (algebraMap K L)).toComonad.ε.app (ModuleCat.of L M))
        (galoisSemilinearComonadicTensorEquiv K L M
          (galoisSemilinearCoaction K L M a m)) = m
  rw [galoisSemilinearComonadicTensorCounit,
    galoisSemilinearTensorCounit_coaction]

/-- The transported coaction satisfies the comonad coassociativity law. -/
theorem galoisSemilinearComonadicCoaction_coassociative
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M) :
    galoisSemilinearComonadicCoaction K L M a ≫
        ((ModuleCat.extendRestrictScalarsAdj
          (algebraMap K L)).toComonad).δ.app (ModuleCat.of L M) =
      galoisSemilinearComonadicCoaction K L M a ≫
        ((ModuleCat.extendRestrictScalarsAdj
          (algebraMap K L)).toComonad).map
            (galoisSemilinearComonadicCoaction K L M a) := by
  apply ModuleCat.hom_ext
  ext m
  change
    ConcreteCategory.hom
        ((ModuleCat.extendRestrictScalarsAdj
          (algebraMap K L)).toComonad.δ.app (ModuleCat.of L M))
        (galoisSemilinearComonadicTensorEquiv K L M
          (galoisSemilinearCoaction K L M a m)) =
      ConcreteCategory.hom
        (((ModuleCat.extendRestrictScalarsAdj
          (algebraMap K L)).toComonad).map
            (galoisSemilinearComonadicCoaction K L M a))
        (galoisSemilinearComonadicTensorEquiv K L M
          (galoisSemilinearCoaction K L M a m))
  rw [galoisSemilinearComonadicTensorComultiplication,
    galoisSemilinearComonadicTensorMapCoaction]
  apply congrArg (galoisSemilinearComonadicDoubleTensorEquiv K L M)
  have h := congrArg (fun f => f m)
    (galoisSemilinearCoaction_coassociative K L M a)
  exact h.symm

/-- A semilinear action determines an extension--restriction coalgebra. -/
noncomputable def galoisSemilinearComonadicDescentData
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M) :
    ComonadicModuleDescentData (algebraMap K L) :=
  Comonad.Coalgebra.mk (ModuleCat.of L M)
    (galoisSemilinearComonadicCoaction K L M a)
    (galoisSemilinearComonadicCoaction_counit K L M a)
    (galoisSemilinearComonadicCoaction_coassociative K L M a)

section Naturality

variable (N : Type u)
variable [AddCommGroup N] [Module K N] [Module L N] [IsScalarTower K L N]

/-- Galois tensor coordinates commute with scalar extension of an equivariant
L-linear map. -/
theorem galoisSemilinearTensorEquiv_baseChange
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M)
    (b : GaloisSemilinearModuleAction K L N)
    (f : M →ₗ[L] N)
    (hf : ∀ σ m, b.action σ (f m) = f (a.action σ m))
    (z : TensorProduct K L M) (σ : L ≃ₐ[K] L) :
    galoisSemilinearTensorEquiv K L N b
        (LinearMap.baseChange L (f.restrictScalars K) z) σ =
      f (galoisSemilinearTensorEquiv K L M a z σ) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x m =>
      simp only [LinearMap.baseChange_tmul,
        galoisSemilinearTensorEquiv_apply,
        galoisSemilinearTensorToFunctions_tmul_apply]
      change x • b.action σ (f m) = f (x • a.action σ m)
      rw [hf, map_smul]
  | add x y hx hy =>
      simp only [map_add, Pi.add_apply, hx, hy]

/-- The raw Galois coaction is natural in equivariant L-linear maps. -/
theorem galoisSemilinearCoaction_natural
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M)
    (b : GaloisSemilinearModuleAction K L N)
    (f : M →ₗ[L] N)
    (hf : ∀ σ m, b.action σ (f m) = f (a.action σ m))
    (m : M) :
    LinearMap.baseChange L (f.restrictScalars K)
        (galoisSemilinearCoaction K L M a m) =
      galoisSemilinearCoaction K L N b (f m) := by
  apply (galoisSemilinearTensorEquiv K L N b).injective
  ext σ
  rw [galoisSemilinearTensorEquiv_baseChange K L M N a b f hf]
  simp

/-- The categorical comonad maps a normalized raw tensor by scalar extension
of the underlying linear map. -/
theorem galoisSemilinearComonadicTensorMap
    (f : M →ₗ[L] N) (z : TensorProduct K L M) :
    ConcreteCategory.hom
        (((ModuleCat.extendRestrictScalarsAdj
          (algebraMap K L)).toComonad).map (ModuleCat.ofHom f))
        (galoisSemilinearComonadicTensorEquiv K L M z) =
      galoisSemilinearComonadicTensorEquiv K L N
        (LinearMap.baseChange L (f.restrictScalars K) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x m => rfl
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- Transport to the extension--restriction comonad preserves naturality of
equivariant semilinear maps. -/
theorem galoisSemilinearComonadicCoaction_natural
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M)
    (b : GaloisSemilinearModuleAction K L N)
    (f : M →ₗ[L] N)
    (hf : ∀ σ m, b.action σ (f m) = f (a.action σ m)) :
    galoisSemilinearComonadicCoaction K L M a ≫
        ((ModuleCat.extendRestrictScalarsAdj
          (algebraMap K L)).toComonad).map (ModuleCat.ofHom f) =
      ModuleCat.ofHom f ≫
        galoisSemilinearComonadicCoaction K L N b := by
  apply ModuleCat.hom_ext
  ext m
  change
    ConcreteCategory.hom
        (((ModuleCat.extendRestrictScalarsAdj
          (algebraMap K L)).toComonad).map (ModuleCat.ofHom f))
        (galoisSemilinearComonadicTensorEquiv K L M
          (galoisSemilinearCoaction K L M a m)) =
      galoisSemilinearComonadicTensorEquiv K L N
        (galoisSemilinearCoaction K L N b (f m))
  rw [galoisSemilinearComonadicTensorMap K L M N f,
    galoisSemilinearCoaction_natural K L M N a b f hf]

/-- An equivariant L-linear map between semilinear Galois modules is a
morphism of their extension--restriction coalgebras. -/
noncomputable def galoisSemilinearComonadicDescentMap
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M)
    (b : GaloisSemilinearModuleAction K L N)
    (f : M →ₗ[L] N)
    (hf : ∀ σ m, b.action σ (f m) = f (a.action σ m)) :
    galoisSemilinearComonadicDescentData K L M a ⟶
      galoisSemilinearComonadicDescentData K L N b :=
  Comonad.Coalgebra.Hom.mk (ModuleCat.ofHom f)
    (galoisSemilinearComonadicCoaction_natural K L M N a b f hf)

end Naturality

/-- The affine Čech module datum canonically selected from the semilinear
extension--restriction coalgebra. -/
noncomputable def galoisSemilinearCechModuleDescentData
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M) :
    AffineCechModuleDescentData
      (CommRingCat.ofHom (algebraMap K L)) :=
  (affineCechComonadicBridge
    (CommRingCat.ofHom (algebraMap K L))).equivalence.inverse.obj
      (galoisSemilinearComonadicDescentData K L M a)

/-- The unique cover module of the selected Čech datum is the original
semilinear L-module. -/
noncomputable def galoisSemilinearCechModuleDescentData_coverIso
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M) :
    (galoisSemilinearCechModuleDescentData K L M a).obj PUnit.unit ≅
      ModuleCat.of L M := by
  exact Iso.refl _

/-- A field extension is faithfully flat, in the form required by the affine
Čech descent bridge. -/
theorem galoisFieldAlgebraMap_faithfullyFlat :
    (algebraMap K L).FaithfullyFlat := by
  unfold RingHom.FaithfullyFlat
  infer_instance

/-- The selected base-field module descended from a finite-Galois semilinear
L-module. -/
noncomputable def galoisSemilinearDescendedModule
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M) : ModuleCat K :=
  affineCechDescendedModule
    (CommRingCat.ofHom (algebraMap K L))
    (galoisFieldAlgebraMap_faithfullyFlat K L)
    (galoisSemilinearCechModuleDescentData K L M a)

/-- Scalar extension of the selected descended module recovers the original
semilinear L-module. -/
noncomputable def galoisSemilinearDescendedModuleBaseChangeIso
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearModuleAction K L M) :
    (ModuleCat.extendScalars (algebraMap K L)).obj
        (galoisSemilinearDescendedModule K L M a) ≅
      ModuleCat.of L M :=
  affineCechDescendedModuleBaseChangeIso
      (CommRingCat.ofHom (algebraMap K L))
      (galoisFieldAlgebraMap_faithfullyFlat K L)
      (galoisSemilinearCechModuleDescentData K L M a) ≪≫
    galoisSemilinearCechModuleDescentData_coverIso K L M a

end

end RiemannResearch.GaloisCohomology
