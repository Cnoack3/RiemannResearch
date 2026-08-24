/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.D4ZornCoordinateGaloisSelectedHopfLaws
import RiemannResearch.AlgebraicGeometry.D4ZornCoordinateGroupSchemeDescent

/-!
# Effective finite-Galois descent of the D4 coordinate Hopf algebra

The selected affine Čech Hopf object is bundled here as an ordinary
commutative Hopf algebra over the base field.  Its canonical scalar-extension
comparison is promoted from a linear equivalence to a bialgebra equivalence,
and hence to an isomorphism in commutative Hopf algebras.  This supplies the
effective Hopf datum required by the D4 group-scheme and fpqc H¹ bridge.
-/

namespace RiemannResearch.AlgebraicGeometry

open CategoryTheory
open RiemannResearch.GaloisCohomology
open RiemannResearch.LinearAlgebra.RootSystem.D4Triality
open RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn
open scoped TensorProduct

noncomputable section

universe u v

private abbrev AIntegral := RelatedTripleCoordinateRing.{0}

local instance : CommRing AIntegral := inferInstance

local instance : HopfAlgebra ℤ AIntegral :=
  relatedTripleCoordinateHopfAlgebra

/-- The ordinary coordinate ring selected by effective affine Čech descent
from the diagram-twisted split D4 coordinate Hopf algebra. -/
noncomputable abbrev relatedTripleCoordinateGaloisDescendedCoordinateRing
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) : Type u :=
  affineCechDescendedModule
    (CommRingCat.ofHom (algebraMap K L))
    (galoisFieldAlgebraMap_faithfullyFlat K L)
    (relatedTripleCoordinateGaloisSelectedCommHopfAlgebraObject
      K L diagram).obj

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L] [IsGalois K L]
variable (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry)

private abbrev B :=
  relatedTripleCoordinateGaloisDescendedCoordinateRing K L diagram

@[instance_reducible]
noncomputable instance relatedTripleCoordinateGaloisDescendedModuleInstance :
    Module K (B K L diagram) :=
  (relatedTripleCoordinateGaloisDescendedModule K L diagram).isModule

@[instance_reducible]
noncomputable instance relatedTripleCoordinateGaloisDescendedCommRing :
    CommRing (B K L diagram) :=
  (relatedTripleCoordinateGaloisSelectedCommHopfAlgebraObject
    K L diagram).descendedCommRing

@[instance_reducible]
noncomputable instance relatedTripleCoordinateGaloisDescendedAlgebra :
    Algebra K (B K L diagram) :=
  (relatedTripleCoordinateGaloisSelectedCommHopfAlgebraObject
    K L diagram).descendedAlgebra

@[instance_reducible]
noncomputable instance relatedTripleCoordinateGaloisDescendedCoalgebraStruct :
    CoalgebraStruct K (B K L diagram) :=
  (relatedTripleCoordinateGaloisSelectedCommHopfAlgebraObject
    K L diagram).descendedCoalgebraStruct

@[instance_reducible]
noncomputable instance relatedTripleCoordinateGaloisDescendedCoalgebra :
    Coalgebra K (B K L diagram) :=
  (relatedTripleCoordinateGaloisSelectedCommHopfAlgebraObject
    K L diagram).descendedCoalgebra

@[instance_reducible]
noncomputable instance relatedTripleCoordinateGaloisDescendedBialgebra :
    Bialgebra K (B K L diagram) :=
  (relatedTripleCoordinateGaloisSelectedCommHopfAlgebraObject
    K L diagram).descendedBialgebra

@[instance_reducible]
noncomputable instance relatedTripleCoordinateGaloisDescendedHopfAlgebraStruct :
    HopfAlgebraStruct K (B K L diagram) :=
  (relatedTripleCoordinateGaloisSelectedCommHopfAlgebraObject
    K L diagram).descendedHopfAlgebraStruct

@[instance_reducible]
noncomputable instance relatedTripleCoordinateGaloisDescendedHopfAlgebra :
    HopfAlgebra K (B K L diagram) :=
  (relatedTripleCoordinateGaloisSelectedCommHopfAlgebraObject
    K L diagram).descendedHopfAlgebra

/-- The canonical scalar-extension comparison on literal tensor-product
carriers.  The first factor comparison only reconciles Mathlib's categorical
restriction-of-scalars carrier with the ordinary type (L). -/
noncomputable def relatedTripleCoordinateGaloisHopfBaseChangeLinearEquiv :
    TensorProduct K L (B K L diagram) ≃ₗ[L]
      RelatedTripleCoordinateScalarExtension L := by
  let LK := (ModuleCat.restrictScalars (algebraMap K L)).obj
    (ModuleCat.of L L)
  letI : Module K LK := LK.isModule
  letI : IsScalarTower K L LK :=
    IsScalarTower.of_algebraMap_smul (by intro k x; rfl)
  let c :
      TensorProduct K L (B K L diagram) ≃ₗ[L]
        TensorProduct K LK (B K L diagram) :=
    TensorProduct.AlgebraTensorModule.congr
      (relatedTripleCoordinateGaloisScalarRestrictLinearEquiv K L)
      (LinearEquiv.refl K (B K L diagram))
  let d :=
    relatedTripleCoordinateGaloisDescendedModuleBaseChangeIso K L diagram
  change
    ModuleCat.of L (TensorProduct K LK (B K L diagram)) ≅
      ModuleCat.of L (RelatedTripleCoordinateScalarExtension L) at d
  exact c.trans d.toLinearEquiv

@[simp] theorem relatedTripleCoordinateGaloisHopfBaseChangeLinearEquiv_tmul
    (l : L) (b : B K L diagram) :
    relatedTripleCoordinateGaloisHopfBaseChangeLinearEquiv K L diagram
        (l ⊗ₜ[K] b) =
      (relatedTripleCoordinateGaloisDescendedModuleBaseChangeIso
        K L diagram).hom
        ((relatedTripleCoordinateGaloisScalarRestrictLinearEquiv K L l) ⊗ₜ[K]
          b) := by
  rfl

set_option maxRecDepth 8000 in
set_option linter.style.haveILetI false in
private theorem relatedTripleCoordinateGaloisHopfBaseChange_one_tmul_mul
    (b c : B K L diagram) :
    relatedTripleCoordinateGaloisHopfBaseChangeLinearEquiv K L diagram
        ((1 : L) ⊗ₜ[K] (b * c)) =
      relatedTripleCoordinateGaloisHopfBaseChangeLinearEquiv K L diagram
          ((1 : L) ⊗ₜ[K] b) *
        relatedTripleCoordinateGaloisHopfBaseChangeLinearEquiv K L diagram
          ((1 : L) ⊗ₜ[K] c) := by
  let f := CommRingCat.ofHom (algebraMap K L)
  let hf := galoisFieldAlgebraMap_faithfullyFlat K L
  let eD :=
    relatedTripleCoordinateGaloisDescendedModuleBaseChangeIso K L diagram
  let eT := affineCechDescendedTensorBaseChangeIso f hf
    (relatedTripleCoordinateGaloisCechModuleDescentData K L diagram)
    (relatedTripleCoordinateGaloisCechModuleDescentData K L diagram)
  let LK := (ModuleCat.restrictScalars (algebraMap K L)).obj
    (ModuleCat.of L L)
  letI : Module K LK := LK.isModule
  letI : IsScalarTower K L LK :=
    IsScalarTower.of_algebraMap_smul (by intro k x; rfl)
  let oneLK :=
    relatedTripleCoordinateGaloisScalarRestrictLinearEquiv K L (1 : L)
  have h := congrArg
    (fun q => ModuleCat.Hom.hom q (oneLK ⊗ₜ[K] (b ⊗ₜ[K] c)))
    (relatedTripleCoordinateGaloisSelectedCommHopfAlgebraObject
      K L diagram).toAffineCechSelectedAlgebraObject.descendedMul_baseChange
  change
    ModuleCat.Hom.hom eD.hom (oneLK ⊗ₜ[K] (b * c)) =
      ModuleCat.Hom.hom
        (relatedTripleCoordinateGaloisSelectedCommHopfAlgebraObject
          K L diagram).coverMul
        (ModuleCat.Hom.hom eT.hom
          (oneLK ⊗ₜ[K] (b ⊗ₜ[K] c))) at h
  let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
  have ht :=
    affineCechDescendedTensorBaseChangeIso_hom_tmul
      f hf D D oneLK b c
  change
    ModuleCat.Hom.hom eT.hom (oneLK ⊗ₜ[K] (b ⊗ₜ[K] c)) =
      ModuleCat.Hom.hom eD.hom (oneLK ⊗ₜ[K] b) ⊗ₜ[L]
        ModuleCat.Hom.hom eD.hom
          ((relatedTripleCoordinateGaloisScalarRestrictLinearEquiv
            K L (1 : L)) ⊗ₜ[K] c) at ht
  rw [ht] at h
  have hc :=
    relatedTripleCoordinateGaloisSelectedMulDescentMap_cover K L diagram
  change
    (relatedTripleCoordinateGaloisSelectedCommHopfAlgebraObject
        K L diagram).coverMul =
      ModuleCat.ofHom
        (galoisAlgebraMultiplicationLinearMap L
          (RelatedTripleCoordinateScalarExtension L)) at hc
  rw [hc] at h
  change
    relatedTripleCoordinateGaloisHopfBaseChangeLinearEquiv K L diagram
        ((1 : L) ⊗ₜ[K] (b * c)) =
      relatedTripleCoordinateGaloisHopfBaseChangeLinearEquiv K L diagram
          ((1 : L) ⊗ₜ[K] b) *
        relatedTripleCoordinateGaloisHopfBaseChangeLinearEquiv K L diagram
          ((1 : L) ⊗ₜ[K] c) at h
  exact h

private theorem relatedTripleCoordinateGaloisHopfBaseChange_tmul_scalar
    (l : L) (b : B K L diagram) :
    relatedTripleCoordinateGaloisHopfBaseChangeLinearEquiv K L diagram
        (l ⊗ₜ[K] b) =
      l • relatedTripleCoordinateGaloisHopfBaseChangeLinearEquiv K L diagram
        ((1 : L) ⊗ₜ[K] b) := by
  rw [← map_smul]
  congr 1
  rw [TensorProduct.smul_tmul']
  simp only [smul_eq_mul, mul_one]

private theorem relatedTripleCoordinateGaloisHopfBaseChange_map_mul
    (x y : TensorProduct K L (B K L diagram)) :
    relatedTripleCoordinateGaloisHopfBaseChangeLinearEquiv K L diagram
        (x * y) =
      relatedTripleCoordinateGaloisHopfBaseChangeLinearEquiv K L diagram x *
        relatedTripleCoordinateGaloisHopfBaseChangeLinearEquiv K L diagram y := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [zero_mul, map_zero]
  | tmul l b =>
      induction y using TensorProduct.induction_on with
      | zero => simp only [mul_zero, map_zero]
      | tmul m c =>
          rw [Algebra.TensorProduct.tmul_mul_tmul]
          rw [relatedTripleCoordinateGaloisHopfBaseChange_tmul_scalar
            K L diagram (l * m) (b * c)]
          rw [relatedTripleCoordinateGaloisHopfBaseChange_one_tmul_mul]
          rw [relatedTripleCoordinateGaloisHopfBaseChange_tmul_scalar
            K L diagram l b]
          rw [relatedTripleCoordinateGaloisHopfBaseChange_tmul_scalar
            K L diagram m c]
          rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
      | add p q hp hq =>
          simp only [mul_add, map_add, hp, hq]
  | add p q hp hq =>
      simp only [add_mul, map_add, hp, hq]

private theorem relatedTripleCoordinateGaloisScalar_comul (l : L) :
    CoalgebraStruct.comul l = (l ⊗ₜ[L] (1 : L)) := by
  calc
    CoalgebraStruct.comul l =
        CoalgebraStruct.comul (l • (1 : L)) := by
      rw [Algebra.smul_def, Algebra.algebraMap_self_apply, mul_one]
    _ = l • CoalgebraStruct.comul (1 : L) := by rw [map_smul]
    _ = l • (1 : TensorProduct L L L) := by rw [Bialgebra.comul_one]
    _ = l ⊗ₜ[L] (1 : L) := by
      rw [show
        (1 : TensorProduct L L L) = (1 : L) ⊗ₜ[L] (1 : L) from rfl,
        TensorProduct.smul_tmul']
      simp only [smul_eq_mul, mul_one]

set_option maxRecDepth 8000 in
set_option synthInstance.maxHeartbeats 200000 in
-- The middle-four tensor comparison requires an enlarged instance-search budget.
set_option linter.style.haveILetI false in
private theorem relatedTripleCoordinateGaloisHopfBaseChange_tensor_comul
    (l : L) (b : B K L diagram) :
    TensorProduct.map
        (relatedTripleCoordinateGaloisHopfBaseChangeLinearEquiv
          K L diagram).toLinearMap
        (relatedTripleCoordinateGaloisHopfBaseChangeLinearEquiv
          K L diagram).toLinearMap
        (CoalgebraStruct.comul (l ⊗ₜ[K] b)) =
      ModuleCat.Hom.hom
        (affineCechDescendedTensorBaseChangeIso
          (CommRingCat.ofHom (algebraMap K L))
          (galoisFieldAlgebraMap_faithfullyFlat K L)
          (relatedTripleCoordinateGaloisCechModuleDescentData K L diagram)
          (relatedTripleCoordinateGaloisCechModuleDescentData
            K L diagram)).hom
        ((relatedTripleCoordinateGaloisScalarRestrictLinearEquiv K L l) ⊗ₜ[K]
          ModuleCat.Hom.hom
            (relatedTripleCoordinateGaloisSelectedCommHopfAlgebraObject
              K L diagram).toAffineCechSelectedCoalgebraObject.descendedComul
            b) := by
  let f := CommRingCat.ofHom (algebraMap K L)
  let hf := galoisFieldAlgebraMap_faithfullyFlat K L
  let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
  let eT := affineCechDescendedTensorBaseChangeIso f hf D D
  let LK := (ModuleCat.restrictScalars (algebraMap K L)).obj
    (ModuleCat.of L L)
  letI : Module K LK := LK.isModule
  letI : IsScalarTower K L LK :=
    IsScalarTower.of_algebraMap_smul (by intro k x; rfl)
  let lLK := relatedTripleCoordinateGaloisScalarRestrictLinearEquiv K L l
  let z : TensorProduct K (B K L diagram) (B K L diagram) :=
    ModuleCat.Hom.hom
      (relatedTripleCoordinateGaloisSelectedCommHopfAlgebraObject
        K L diagram).toAffineCechSelectedCoalgebraObject.descendedComul b
  change
    TensorProduct.map
        (relatedTripleCoordinateGaloisHopfBaseChangeLinearEquiv
          K L diagram).toLinearMap
        (relatedTripleCoordinateGaloisHopfBaseChangeLinearEquiv
          K L diagram).toLinearMap
        ((TensorProduct.AlgebraTensorModule.tensorTensorTensorComm
          K L K L L L (B K L diagram) (B K L diagram))
          (CoalgebraStruct.comul l ⊗ₜ[K] z)) =
      ModuleCat.Hom.hom eT.hom (lLK ⊗ₜ[K] z)
  rw [relatedTripleCoordinateGaloisScalar_comul]
  induction z using TensorProduct.induction_on with
  | zero =>
      change
        TensorProduct.map
            (relatedTripleCoordinateGaloisHopfBaseChangeLinearEquiv
              K L diagram).toLinearMap
            (relatedTripleCoordinateGaloisHopfBaseChangeLinearEquiv
              K L diagram).toLinearMap
            ((TensorProduct.AlgebraTensorModule.tensorTensorTensorComm
              K L K L L L (B K L diagram) (B K L diagram)) 0) =
          ModuleCat.Hom.hom eT.hom 0
      rfl
  | tmul m n =>
      rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
        TensorProduct.map_tmul]
      have ht :=
        affineCechDescendedTensorBaseChangeIso_hom_tmul
          f hf D D lLK m n
      change
        ModuleCat.Hom.hom eT.hom (lLK ⊗ₜ[K] (m ⊗ₜ[K] n)) =
          relatedTripleCoordinateGaloisHopfBaseChangeLinearEquiv K L diagram
              (l ⊗ₜ[K] m) ⊗ₜ[L]
            relatedTripleCoordinateGaloisHopfBaseChangeLinearEquiv K L diagram
              ((1 : L) ⊗ₜ[K] n) at ht
      exact ht.symm
  | add x y hx hy =>
      simp only [TensorProduct.tmul_add, map_add, hx, hy]
      calc
        ModuleCat.Hom.hom eT.hom (lLK ⊗ₜ[K] x) +
            ModuleCat.Hom.hom eT.hom (lLK ⊗ₜ[K] y) =
          ModuleCat.Hom.hom eT.hom
            ((lLK ⊗ₜ[K] x) + (lLK ⊗ₜ[K] y)) :=
          ((ModuleCat.Hom.hom eT.hom).map_add _ _).symm
        _ = ModuleCat.Hom.hom eT.hom (lLK ⊗ₜ[K] (x + y)) :=
          congrArg (ModuleCat.Hom.hom eT.hom)
            (TensorProduct.tmul_add lLK x y).symm


private theorem relatedTripleCoordinateGaloisScalar_counit (l : L) :
    CoalgebraStruct.counit l = l := by
  calc
    CoalgebraStruct.counit l =
        CoalgebraStruct.counit (l • (1 : L)) := by
      rw [Algebra.smul_def, Algebra.algebraMap_self_apply, mul_one]
    _ = l • CoalgebraStruct.counit (1 : L) := by rw [map_smul]
    _ = l • (1 : L) := by rw [Bialgebra.counit_one]
    _ = l := by simp only [smul_eq_mul, mul_one]

private theorem relatedTripleCoordinateGaloisTensor_counit
    (l : L) (b : B K L diagram) :
    CoalgebraStruct.counit (l ⊗ₜ[K] b) =
      l * algebraMap K L (CoalgebraStruct.counit b) := by
  change
    (TensorProduct.AlgebraTensorModule.rid K L L)
        (CoalgebraStruct.counit l ⊗ₜ[K] CoalgebraStruct.counit b) =
      l * algebraMap K L (CoalgebraStruct.counit b)
  rw [relatedTripleCoordinateGaloisScalar_counit,
    TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def]
  exact mul_comm _ _

set_option maxRecDepth 8000 in
set_option linter.style.haveILetI false in
private theorem relatedTripleCoordinateGaloisHopfBaseChange_map_comul
    (x : TensorProduct K L (B K L diagram)) :
    TensorProduct.map
        (relatedTripleCoordinateGaloisHopfBaseChangeLinearEquiv
          K L diagram).toLinearMap
        (relatedTripleCoordinateGaloisHopfBaseChangeLinearEquiv
          K L diagram).toLinearMap
        ((CoalgebraStruct.comul :
          TensorProduct K L (B K L diagram) →ₗ[L]
            TensorProduct L
              (TensorProduct K L (B K L diagram))
              (TensorProduct K L (B K L diagram))) x) =
      (CoalgebraStruct.comul :
        RelatedTripleCoordinateScalarExtension L →ₗ[L]
          TensorProduct L
            (RelatedTripleCoordinateScalarExtension L)
            (RelatedTripleCoordinateScalarExtension L))
        (relatedTripleCoordinateGaloisHopfBaseChangeLinearEquiv
          K L diagram x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul l b =>
      let f := CommRingCat.ofHom (algebraMap K L)
      let hf := galoisFieldAlgebraMap_faithfullyFlat K L
      let eD :=
        relatedTripleCoordinateGaloisDescendedModuleBaseChangeIso K L diagram
      let eT := affineCechDescendedTensorBaseChangeIso f hf
        (relatedTripleCoordinateGaloisCechModuleDescentData K L diagram)
        (relatedTripleCoordinateGaloisCechModuleDescentData K L diagram)
      let LK := (ModuleCat.restrictScalars (algebraMap K L)).obj
        (ModuleCat.of L L)
      letI : Module K LK := LK.isModule
      letI : IsScalarTower K L LK :=
        IsScalarTower.of_algebraMap_smul (by intro k x; rfl)
      let lLK :=
        relatedTripleCoordinateGaloisScalarRestrictLinearEquiv K L l
      have h := congrArg
        (fun q => ModuleCat.Hom.hom q (lLK ⊗ₜ[K] b))
        (relatedTripleCoordinateGaloisSelectedCommHopfAlgebraObject
          K L diagram).toAffineCechSelectedCoalgebraObject.descendedComul_baseChange
      change
        ModuleCat.Hom.hom
            (relatedTripleCoordinateGaloisSelectedCommHopfAlgebraObject
              K L diagram).toAffineCechSelectedCoalgebraObject.coverComul
            (ModuleCat.Hom.hom eD.hom (lLK ⊗ₜ[K] b)) =
          ModuleCat.Hom.hom eT.hom
            (lLK ⊗ₜ[K]
              ModuleCat.Hom.hom
                (relatedTripleCoordinateGaloisSelectedCommHopfAlgebraObject
                  K L diagram).toAffineCechSelectedCoalgebraObject.descendedComul
                b) at h
      have hc :=
        relatedTripleCoordinateGaloisSelectedComulDescentMap_cover K L diagram
      change
        (relatedTripleCoordinateGaloisSelectedCommHopfAlgebraObject
          K L diagram).toAffineCechSelectedCoalgebraObject.coverComul =
            ModuleCat.ofHom
              (CoalgebraStruct.comul :
                RelatedTripleCoordinateScalarExtension L →ₗ[L]
                  TensorProduct L
                    (RelatedTripleCoordinateScalarExtension L)
                    (RelatedTripleCoordinateScalarExtension L)) at hc
      rw [hc] at h
      have ht :=
        relatedTripleCoordinateGaloisHopfBaseChange_tensor_comul
          K L diagram l b
      have he :
          ModuleCat.Hom.hom eD.hom (lLK ⊗ₜ[K] b) =
            relatedTripleCoordinateGaloisHopfBaseChangeLinearEquiv
              K L diagram (l ⊗ₜ[K] b) := rfl
      rw [he] at h
      exact ht.trans h.symm
  | add x y hx hy =>
      simp only [map_add, hx, hy]

set_option maxRecDepth 8000 in
set_option linter.style.haveILetI false in
private theorem relatedTripleCoordinateGaloisHopfBaseChange_map_counit
    (x : TensorProduct K L (B K L diagram)) :
    (CoalgebraStruct.counit :
        RelatedTripleCoordinateScalarExtension L →ₗ[L] L)
        (relatedTripleCoordinateGaloisHopfBaseChangeLinearEquiv
          K L diagram x) =
      (CoalgebraStruct.counit :
        TensorProduct K L (B K L diagram) →ₗ[L] L) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul l b =>
      let f := CommRingCat.ofHom (algebraMap K L)
      let eD :=
        relatedTripleCoordinateGaloisDescendedModuleBaseChangeIso K L diagram
      let LK := (ModuleCat.restrictScalars (algebraMap K L)).obj
        (ModuleCat.of L L)
      letI : Module K LK := LK.isModule
      letI : IsScalarTower K L LK :=
        IsScalarTower.of_algebraMap_smul (by intro k x; rfl)
      let lLK :=
        relatedTripleCoordinateGaloisScalarRestrictLinearEquiv K L l
      have h := congrArg
        (fun q => ModuleCat.Hom.hom q (lLK ⊗ₜ[K] b))
        (relatedTripleCoordinateGaloisSelectedCommHopfAlgebraObject
          K L diagram).toAffineCechSelectedCoalgebraObject.descendedCounit_baseChange
      change
        ModuleCat.Hom.hom
            (relatedTripleCoordinateGaloisSelectedCommHopfAlgebraObject
              K L diagram).toAffineCechSelectedCoalgebraObject.coverCounit
            (ModuleCat.Hom.hom eD.hom (lLK ⊗ₜ[K] b)) =
          algebraMap K L
              (ModuleCat.Hom.hom
                (relatedTripleCoordinateGaloisSelectedCommHopfAlgebraObject
                  K L diagram).toAffineCechSelectedCoalgebraObject.descendedCounit
                b) * l at h
      have hc :=
        relatedTripleCoordinateGaloisSelectedCounitDescentMap_cover K L diagram
      change
        (relatedTripleCoordinateGaloisSelectedCommHopfAlgebraObject
          K L diagram).toAffineCechSelectedCoalgebraObject.coverCounit =
            ModuleCat.ofHom
              (CoalgebraStruct.counit :
                RelatedTripleCoordinateScalarExtension L →ₗ[L] L) at hc
      rw [hc] at h
      change
        ModuleCat.Hom.hom
            (ModuleCat.ofHom
              (CoalgebraStruct.counit :
                RelatedTripleCoordinateScalarExtension L →ₗ[L] L))
            (ModuleCat.Hom.hom eD.hom (lLK ⊗ₜ[K] b)) =
          algebraMap K L
              (ModuleCat.Hom.hom
                (relatedTripleCoordinateGaloisSelectedCommHopfAlgebraObject
                  K L diagram).toAffineCechSelectedCoalgebraObject.descendedCounit
                b) * l at h
      have he :
          ModuleCat.Hom.hom eD.hom (lLK ⊗ₜ[K] b) =
            relatedTripleCoordinateGaloisHopfBaseChangeLinearEquiv
              K L diagram (l ⊗ₜ[K] b) := rfl
      rw [he] at h
      have heps :
          ModuleCat.Hom.hom
              (relatedTripleCoordinateGaloisSelectedCommHopfAlgebraObject
                K L diagram).toAffineCechSelectedCoalgebraObject.descendedCounit
              b =
            CoalgebraStruct.counit b := rfl
      rw [heps] at h
      exact h.trans <|
        (mul_comm _ _).trans
          (relatedTripleCoordinateGaloisTensor_counit K L diagram l b).symm
  | add x y hx hy =>
      simp only [map_add, hx, hy]

/-- The scalar-extension comparison is an equivalence of bialgebras. -/
noncomputable def relatedTripleCoordinateGaloisHopfBaseChangeBialgEquiv :
    TensorProduct K L (B K L diagram) ≃ₐc[L]
      RelatedTripleCoordinateScalarExtension L := by
  let e :=
    relatedTripleCoordinateGaloisHopfBaseChangeLinearEquiv K L diagram
  let c :
      TensorProduct K L (B K L diagram) →ₗc[L]
        RelatedTripleCoordinateScalarExtension L :=
    CoalgHom.mk e.toLinearMap
      (by
        apply LinearMap.ext
        intro x
        exact relatedTripleCoordinateGaloisHopfBaseChange_map_counit
          K L diagram x)
      (by
        apply LinearMap.ext
        intro x
        exact relatedTripleCoordinateGaloisHopfBaseChange_map_comul
          K L diagram x)
  let ce :
      TensorProduct K L (B K L diagram) ≃ₗc[L]
        RelatedTripleCoordinateScalarExtension L :=
    CoalgEquiv.mk c e.symm
      (fun x => e.symm_apply_apply x)
      (fun x => e.apply_symm_apply x)
  exact BialgEquiv.mk ce
    (fun x y =>
      relatedTripleCoordinateGaloisHopfBaseChange_map_mul K L diagram x y)

/-- Scalar extension of the descended coordinate Hopf algebra is split. -/
noncomputable def relatedTripleCoordinateGaloisHopfBaseChangeIso :
    CommHopfAlgCat.of L (TensorProduct K L (B K L diagram)) ≅
      CommHopfAlgCat.of L (RelatedTripleCoordinateScalarExtension L) :=
  commHopfAlgIsoOfBialgEquiv
    (relatedTripleCoordinateGaloisHopfBaseChangeBialgEquiv K L diagram)

/-- The selected D4 Hopf object supplies the effective Hopf descent datum. -/
noncomputable def relatedTripleCoordinateGaloisHopfDescentData :
    RelatedTripleCoordinateGaloisHopfDescentData
      K L (B K L diagram) diagram where
  moduleIso := Iso.refl _
  baseChangeHopfIso :=
    relatedTripleCoordinateGaloisHopfBaseChangeIso K L diagram

/-- Effective D4 Hopf descent reaches the affine group-scheme and fpqc H¹
bridge. -/
theorem relatedTripleCoordinateGalois_groupScheme_fpqc :
    Nonempty
      (affineGroupSchemePullbackGroup K L (B K L diagram) ≅
        affineGroupSchemeGroup L
          (RelatedTripleCoordinateScalarExtension L)) ∧
      ∃ res :
          FpqcH1.{u, v} (CommRingCat.of K)
              (CommRingCat.of (B K L diagram)) →
            FpqcH1.{u, v} (CommRingCat.of L)
              (CommRingCat.of
                (RelatedTripleCoordinateScalarExtension L)),
        res
            (FpqcH1.neutral (CommRingCat.of K)
              (CommRingCat.of (B K L diagram))) =
          FpqcH1.neutral (CommRingCat.of L)
            (CommRingCat.of
              (RelatedTripleCoordinateScalarExtension L)) := by
  exact
    RelatedTripleCoordinateGaloisHopfDescentData.groupScheme_fpqc
      (relatedTripleCoordinateGaloisHopfDescentData K L diagram)

end

end RiemannResearch.AlgebraicGeometry
