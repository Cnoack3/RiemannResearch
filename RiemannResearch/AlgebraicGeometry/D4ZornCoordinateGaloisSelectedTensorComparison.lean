/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.D4ZornCoordinateGaloisSelectedHopfDescent
import RiemannResearch.LinearAlgebra.RootSystem.D4ZornCoordinateGaloisSemilinearAlgebraEffectiveDescent

/-!
# Selected tensor comparisons for finite-Galois D4 coordinate descent

This module begins the comparison of the tensor unit and tensor square selected
by effective affine Čech module descent with the canonical finite-Galois
semilinear Čech data used for the D4 related-triple coordinate Hopf maps.  It
records the scalar pure-generator coaction normalization, proves the
comparison-coalgebra tensor-unit coaction square, and constructs the selected
tensor-unit Čech isomorphism. It then proves the tensor-square comparison
coaction square and constructs the selected tensor-square Čech isomorphism.

Source: user-provided D4 Hopf-descent program.
-/

namespace RiemannResearch.AlgebraicGeometry

noncomputable section

open CategoryTheory
open RiemannResearch.GaloisCohomology
open RiemannResearch.LinearAlgebra.RootSystem.D4Triality
open RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn
open scoped TensorProduct

universe u

private abbrev ASelected := RelatedTripleCoordinateRing.{0}

local instance coordinateGaloisSelectedTensorComparisonCommRing :
    CommRing ASelected :=
  inferInstance

private noncomputable abbrev coordinateAlgebraAction
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :=
  relatedTripleCoordinateGaloisSemilinearAlgebraAction K L diagram

private noncomputable abbrev coordinateModuleAction
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :=
  (coordinateAlgebraAction K L diagram).toModuleAction
    K L (RelatedTripleCoordinateScalarExtension L)

/-- For the scalar semilinear Galois action, the coaction of a scalar times a
base-field scalar is the corresponding pure tensor. This is the generator
normalization needed to compare the selected Čech tensor unit with canonical
finite-Galois scalar descent. -/
theorem galoisScalarSemilinearCoaction_mul_algebraMap
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (l : L) (k : K) :
    galoisSemilinearCoaction K L L
        ((galoisScalarSemilinearAlgebraAction K L).toModuleAction K L L)
        (l * algebraMap K L k) =
      l ⊗ₜ[K] algebraMap K L k := by
  apply (galoisSemilinearTensorEquiv K L L
    ((galoisScalarSemilinearAlgebraAction K L).toModuleAction K L L)).injective
  ext σ
  rw [galoisSemilinearTensorEquiv_coaction_apply,
    galoisSemilinearTensorEquiv_tmul_apply]
  simp

/-- Identity on the scalar extension ring, regarded as an equivalence to its
categorical restriction-of-scalars carrier. -/
noncomputable def relatedTripleCoordinateGaloisScalarRestrictLinearEquiv
    (K L : Type u) [Field K] [Field L] [Algebra K L] :
    L ≃ₗ[L] ((ModuleCat.restrictScalars (algebraMap K L)).obj
      (ModuleCat.of L L)) := {
  toFun := fun x => x
  invFun := fun x => x
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  map_add' := by intro x y; rfl
  map_smul' := by intro x y; rfl
}

/-- The comparison carrier of the selected tensor unit, normalized to the
cover field. -/
noncomputable def relatedTripleCoordinateGaloisComparisonTensorUnitLinearEquiv
    (K L : Type u) [Field K] [Field L] [Algebra K L] :
    let LK := (ModuleCat.restrictScalars (algebraMap K L)).obj (ModuleCat.of L L)
    letI : Module K LK := LK.isModule
    letI : IsScalarTower K L LK :=
      IsScalarTower.of_algebraMap_smul (by intro k x; rfl)
    TensorProduct K LK K ≃ₗ[L] L := by
  dsimp only
  let LK := (ModuleCat.restrictScalars (algebraMap K L)).obj (ModuleCat.of L L)
  letI : Module K LK := LK.isModule
  letI : IsScalarTower K L LK :=
    IsScalarTower.of_algebraMap_smul (by intro k x; rfl)
  exact
    (TensorProduct.AlgebraTensorModule.congr
        (relatedTripleCoordinateGaloisScalarRestrictLinearEquiv K L)
        (LinearEquiv.refl K K)).symm.trans
      (TensorProduct.AlgebraTensorModule.rid K L L)

/-- The canonical comparison-coalgebra tensor-unit carrier isomorphism. -/
noncomputable def relatedTripleCoordinateGaloisComparisonTensorUnitIso
    (K L : Type u) [Field K] [Field L] [Algebra K L] :
    ((comonadicModuleDescentComparison (algebraMap K L)).obj
      (ModuleCat.of K K)).A ≅ ModuleCat.of L L := by
  let LK := (ModuleCat.restrictScalars (algebraMap K L)).obj (ModuleCat.of L L)
  letI : Module K LK := LK.isModule
  letI : IsScalarTower K L LK :=
    IsScalarTower.of_algebraMap_smul (by intro k x; rfl)
  change ModuleCat.of L (TensorProduct K LK K) ≅ ModuleCat.of L L
  exact
    (relatedTripleCoordinateGaloisComparisonTensorUnitLinearEquiv K L).toModuleIso

set_option linter.style.haveILetI false in
/-- The comparison tensor-unit carrier isomorphism sends a pure tensor to
ordinary scalar multiplication. -/
theorem relatedTripleCoordinateGaloisComparisonTensorUnitLinearEquiv_tmul
    (K L : Type u) [Field K] [Field L] [Algebra K L] (l : L) (k : K) :
    let LK := (ModuleCat.restrictScalars (algebraMap K L)).obj (ModuleCat.of L L)
    letI : Module K LK := LK.isModule
    letI : IsScalarTower K L LK :=
      IsScalarTower.of_algebraMap_smul (by intro k x; rfl)
    relatedTripleCoordinateGaloisComparisonTensorUnitLinearEquiv K L
        ((relatedTripleCoordinateGaloisScalarRestrictLinearEquiv K L l) ⊗ₜ[K] k) =
      l * algebraMap K L k := by
  dsimp only
  let LK := (ModuleCat.restrictScalars (algebraMap K L)).obj (ModuleCat.of L L)
  letI : Module K LK := LK.isModule
  letI : IsScalarTower K L LK :=
    IsScalarTower.of_algebraMap_smul (by intro k x; rfl)
  let eT := TensorProduct.AlgebraTensorModule.congr
    (relatedTripleCoordinateGaloisScalarRestrictLinearEquiv K L)
    (LinearEquiv.refl K K)
  have hc :
      eT.symm
          ((relatedTripleCoordinateGaloisScalarRestrictLinearEquiv K L l) ⊗ₜ[K] k) =
        l ⊗ₜ[K] k := by
    apply eT.injective
    rw [eT.apply_symm_apply, TensorProduct.AlgebraTensorModule.congr_tmul]
    simp only [LinearEquiv.refl_apply]
  change
    (eT.symm.trans (TensorProduct.AlgebraTensorModule.rid K L L))
        ((relatedTripleCoordinateGaloisScalarRestrictLinearEquiv K L l) ⊗ₜ[K] k) =
      l * algebraMap K L k
  rw [LinearEquiv.trans_apply, hc,
    TensorProduct.AlgebraTensorModule.rid_tmul]
  simp only [Algebra.smul_def]
  exact mul_comm _ _

set_option linter.style.haveILetI false in
/-- The comparison-coalgebra tensor unit is compatible with the canonical
scalar Galois coaction. -/
theorem relatedTripleCoordinateGaloisComparisonTensorUnit_coaction
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    let N := ModuleCat.of K K
    let Q := galoisSemilinearComonadicDescentData K L L
      ((galoisScalarSemilinearAlgebraAction K L).toModuleAction K L L)
    let G := (ModuleCat.extendRestrictScalarsAdj (algebraMap K L)).toComonad
    let e := relatedTripleCoordinateGaloisComparisonTensorUnitIso K L
    ((comonadicModuleDescentComparison (algebraMap K L)).obj N).a ≫
        G.map e.hom = e.hom ≫ Q.a := by
  dsimp only
  let N : ModuleCat K := ModuleCat.of K K
  let Q := galoisSemilinearComonadicDescentData K L L
    ((galoisScalarSemilinearAlgebraAction K L).toModuleAction K L L)
  let G := (ModuleCat.extendRestrictScalarsAdj (algebraMap K L)).toComonad
  let e := relatedTripleCoordinateGaloisComparisonTensorUnitIso K L
  let LK := (ModuleCat.restrictScalars (algebraMap K L)).obj (ModuleCat.of L L)
  letI : Module K LK := LK.isModule
  letI : IsScalarTower K L LK :=
    IsScalarTower.of_algebraMap_smul (by intro k x; rfl)
  let T := TensorProduct K LK K
  let Y : ModuleCat L := G.obj Q.A
  let lhs : T →ₗ[L] Y := ModuleCat.Hom.hom
    (((comonadicModuleDescentComparison (algebraMap K L)).obj N).a ≫ G.map e.hom)
  let rhs : T →ₗ[L] Y := ModuleCat.Hom.hom (e.hom ≫ Q.a)
  apply ModuleCat.hom_ext
  change lhs = rhs
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul l k =>
      dsimp [lhs, rhs]
      change L at l
      have he : e.hom = ModuleCat.ofHom
          (relatedTripleCoordinateGaloisComparisonTensorUnitLinearEquiv
            K L).toLinearMap := by
        rfl
      rw [he]
      change
        ConcreteCategory.hom
            (G.map (ModuleCat.ofHom
              (relatedTripleCoordinateGaloisComparisonTensorUnitLinearEquiv
                K L).toLinearMap))
            (galoisSemilinearComonadicTensorEquiv K L T
              (l ⊗ₜ[K]
                ((relatedTripleCoordinateGaloisScalarRestrictLinearEquiv
                  K L (1 : L)) ⊗ₜ[K] k))) =
          galoisSemilinearComonadicTensorEquiv K L L
            (galoisSemilinearCoaction K L L
              ((galoisScalarSemilinearAlgebraAction K L).toModuleAction K L L)
              (relatedTripleCoordinateGaloisComparisonTensorUnitLinearEquiv
                K L
                ((relatedTripleCoordinateGaloisScalarRestrictLinearEquiv
                  K L l) ⊗ₜ[K] k)))
      rw [galoisSemilinearComonadicTensorMap, LinearMap.baseChange_tmul,
        relatedTripleCoordinateGaloisComparisonTensorUnitLinearEquiv_tmul]
      have hinner :
          ((relatedTripleCoordinateGaloisComparisonTensorUnitLinearEquiv
            K L).toLinearMap.restrictScalars K)
              ((relatedTripleCoordinateGaloisScalarRestrictLinearEquiv
                K L (1 : L)) ⊗ₜ[K] k) = algebraMap K L k := by
        change
          relatedTripleCoordinateGaloisComparisonTensorUnitLinearEquiv K L
              ((relatedTripleCoordinateGaloisScalarRestrictLinearEquiv
                K L (1 : L)) ⊗ₜ[K] k) = algebraMap K L k
        simpa only [one_mul] using
          relatedTripleCoordinateGaloisComparisonTensorUnitLinearEquiv_tmul
            K L 1 k
      rw [hinner]
      exact congrArg (galoisSemilinearComonadicTensorEquiv K L L)
        (galoisScalarSemilinearCoaction_mul_algebraMap K L l k).symm
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- The selected tensor-unit datum, transported through the canonical bridge,
is isomorphic to canonical scalar finite-Galois descent. -/
noncomputable def relatedTripleCoordinateGaloisSelectedTensorUnitComonadicIso
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    let f := CommRingCat.ofHom (algebraMap K L)
    let U := affineCechSelectedTensorUnitDescentData f
    let Q := galoisSemilinearComonadicDescentData K L L
      ((galoisScalarSemilinearAlgebraAction K L).toModuleAction K L L)
    let E := (affineCechComonadicBridge f).equivalence
    E.functor.obj U ≅ Q := by
  dsimp only
  let f := CommRingCat.ofHom (algebraMap K L)
  let N : ModuleCat K := ModuleCat.of K K
  let Q := galoisSemilinearComonadicDescentData K L L
    ((galoisScalarSemilinearAlgebraAction K L).toModuleAction K L L)
  let c := (affineCechComonadicBridge f).comparisonIso.app N
  let e := relatedTripleCoordinateGaloisComparisonTensorUnitIso K L
  let q : (comonadicModuleDescentComparison (algebraMap K L)).obj N ≅ Q :=
    Comonad.Coalgebra.isoMk e
      (relatedTripleCoordinateGaloisComparisonTensorUnit_coaction K L)
  exact c ≪≫ q

/-- The selected affine Čech tensor unit is isomorphic to the inverse-bridge
datum of canonical scalar finite-Galois descent. -/
noncomputable def relatedTripleCoordinateGaloisSelectedTensorUnitCechIso
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    let f := CommRingCat.ofHom (algebraMap K L)
    let U := affineCechSelectedTensorUnitDescentData f
    let Q := galoisSemilinearComonadicDescentData K L L
      ((galoisScalarSemilinearAlgebraAction K L).toModuleAction K L L)
    let E := (affineCechComonadicBridge f).equivalence
    U ≅ E.inverse.obj Q := by
  dsimp only
  let f := CommRingCat.ofHom (algebraMap K L)
  let U := affineCechSelectedTensorUnitDescentData f
  let Q := galoisSemilinearComonadicDescentData K L L
    ((galoisScalarSemilinearAlgebraAction K L).toModuleAction K L L)
  exact affineCechIsoOfComonadicIso f U Q
    (relatedTripleCoordinateGaloisSelectedTensorUnitComonadicIso K L)

/-- The comparison coalgebra of the selected descended coordinate module is
canonically isomorphic to the finite-Galois coordinate coalgebra. Its carrier
is exactly the selected coordinate base-change isomorphism. -/
noncomputable def relatedTripleCoordinateGaloisCoordinateComparisonComonadicIso
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    let a := coordinateModuleAction K L diagram
    let Q := galoisSemilinearComonadicDescentData K L
      (RelatedTripleCoordinateScalarExtension L) a
    let M := galoisSemilinearDescendedModule K L
      (RelatedTripleCoordinateScalarExtension L) a
    (comonadicModuleDescentComparison (algebraMap K L)).obj M ≅ Q := by
  dsimp only
  let f := CommRingCat.ofHom (algebraMap K L)
  let hf := galoisFieldAlgebraMap_faithfullyFlat K L
  let a := coordinateModuleAction K L diagram
  let Q := galoisSemilinearComonadicDescentData K L
    (RelatedTripleCoordinateScalarExtension L) a
  let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
  let M := galoisSemilinearDescendedModule K L
    (RelatedTripleCoordinateScalarExtension L) a
  let E := (affineCechComonadicBridge f).equivalence
  let c := (affineCechComonadicBridge f).comparisonIso.app M
  let i := affineCechDescendedModuleIso f hf D
  exact c.symm ≪≫ E.functor.mapIso i ≪≫ E.counitIso.app Q

set_option linter.style.haveILetI false in
/-- Literal linear-equivalence presentation of the selected coordinate
base-change isomorphism. -/
noncomputable def relatedTripleCoordinateGaloisCoordinateBaseChangeLinearEquiv
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    let a := coordinateModuleAction K L diagram
    let M := galoisSemilinearDescendedModule K L
      (RelatedTripleCoordinateScalarExtension L) a
    let LK := (ModuleCat.restrictScalars (algebraMap K L)).obj
      (ModuleCat.of L L)
    letI : Module K LK := LK.isModule
    letI : IsScalarTower K L LK :=
      IsScalarTower.of_algebraMap_smul (by intro k x; rfl)
    TensorProduct K LK M ≃ₗ[L]
      RelatedTripleCoordinateScalarExtension L := by
  dsimp only
  let a := coordinateModuleAction K L diagram
  let M := galoisSemilinearDescendedModule K L
    (RelatedTripleCoordinateScalarExtension L) a
  let LK := (ModuleCat.restrictScalars (algebraMap K L)).obj
    (ModuleCat.of L L)
  letI : Module K LK := LK.isModule
  letI : IsScalarTower K L LK :=
    IsScalarTower.of_algebraMap_smul (by intro k x; rfl)
  let e := galoisSemilinearDescendedModuleBaseChangeIso K L
    (RelatedTripleCoordinateScalarExtension L) a
  change ModuleCat.of L (TensorProduct K LK M) ≅
    ModuleCat.of L (RelatedTripleCoordinateScalarExtension L) at e
  exact e.toLinearEquiv

set_option maxHeartbeats 1000000 in
-- Normalizing the selected base-change coalgebra square is elaboration-intensive.
set_option linter.style.haveILetI false in
/-- Elements of the selected descended coordinate module become
finite-Galois fixed after base change. The scalar form recorded here is the
normalization used in the tensor-square comparison. -/
theorem relatedTripleCoordinateGaloisCoordinateBaseChange_coaction
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry)
    (l : L)
    (m : galoisSemilinearDescendedModule K L
      (RelatedTripleCoordinateScalarExtension L)
      (coordinateModuleAction K L diagram)) :
    let a := coordinateModuleAction K L diagram
    let eD := galoisSemilinearDescendedModuleBaseChangeIso K L
      (RelatedTripleCoordinateScalarExtension L) a
    galoisSemilinearCoaction K L
        (RelatedTripleCoordinateScalarExtension L) a
        (eD.hom (l ⊗ₜ[K] m)) =
      l ⊗ₜ[K] eD.hom ((1 : L) ⊗ₜ[K] m) := by
  dsimp only
  let a := coordinateModuleAction K L diagram
  let Q := galoisSemilinearComonadicDescentData K L
    (RelatedTripleCoordinateScalarExtension L) a
  let M := galoisSemilinearDescendedModule K L
    (RelatedTripleCoordinateScalarExtension L) a
  let G := (ModuleCat.extendRestrictScalarsAdj
    (algebraMap K L)).toComonad
  let eD := galoisSemilinearDescendedModuleBaseChangeIso K L
    (RelatedTripleCoordinateScalarExtension L) a
  let q := relatedTripleCoordinateGaloisCoordinateComparisonComonadicIso
    K L diagram
  let LK := (ModuleCat.restrictScalars (algebraMap K L)).obj
    (ModuleCat.of L L)
  letI : Module K LK := LK.isModule
  letI : IsScalarTower K L LK :=
    IsScalarTower.of_algebraMap_smul (by intro k x; rfl)
  let T := TensorProduct K LK M
  let eDRaw :=
    relatedTripleCoordinateGaloisCoordinateBaseChangeLinearEquiv K L diagram
  have he : q.hom.f = eD.hom := by rfl
  have heD : eD.hom = ModuleCat.ofHom eDRaw.toLinearMap := by rfl
  have h := congrArg
    (fun z : ((comonadicModuleDescentComparison
        (algebraMap K L)).obj M).A ⟶ G.obj Q.A =>
      ModuleCat.Hom.hom z (l ⊗ₜ[K] m)) q.hom.h
  rw [he, heD] at h
  change
    ConcreteCategory.hom (G.map (ModuleCat.ofHom eDRaw.toLinearMap))
        (galoisSemilinearComonadicTensorEquiv K L T
          (l ⊗ₜ[K]
            ((relatedTripleCoordinateGaloisScalarRestrictLinearEquiv
              K L (1 : L)) ⊗ₜ[K] m))) =
      galoisSemilinearComonadicTensorEquiv K L
        (RelatedTripleCoordinateScalarExtension L)
        (galoisSemilinearCoaction K L
          (RelatedTripleCoordinateScalarExtension L) a
          (eDRaw
            ((relatedTripleCoordinateGaloisScalarRestrictLinearEquiv
              K L l) ⊗ₜ[K] m))) at h
  rw [galoisSemilinearComonadicTensorMap,
    LinearMap.baseChange_tmul] at h
  apply (galoisSemilinearComonadicTensorEquiv K L
    (RelatedTripleCoordinateScalarExtension L)).injective
  exact h.symm

set_option linter.style.haveILetI false in
/-- The selected tensor-square comparison carrier, normalized to the
canonical tensor square of the finite-Galois coordinate algebra. -/
noncomputable def relatedTripleCoordinateGaloisComparisonTensorSquareLinearEquiv
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    let a := coordinateModuleAction K L diagram
    let M := galoisSemilinearDescendedModule K L
      (RelatedTripleCoordinateScalarExtension L) a
    let LK := (ModuleCat.restrictScalars (algebraMap K L)).obj
      (ModuleCat.of L L)
    letI : Module K LK := LK.isModule
    letI : IsScalarTower K L LK :=
      IsScalarTower.of_algebraMap_smul (by intro k x; rfl)
    TensorProduct K LK (TensorProduct K M M) ≃ₗ[L]
      TensorProduct L (RelatedTripleCoordinateScalarExtension L)
        (RelatedTripleCoordinateScalarExtension L) := by
  dsimp only
  let aA := coordinateAlgebraAction K L diagram
  let a := coordinateModuleAction K L diagram
  let M := galoisSemilinearDescendedModule K L
    (RelatedTripleCoordinateScalarExtension L) a
  let LK := (ModuleCat.restrictScalars (algebraMap K L)).obj
    (ModuleCat.of L L)
  letI : Module K LK := LK.isModule
  letI : IsScalarTower K L LK :=
    IsScalarTower.of_algebraMap_smul (by intro k x; rfl)
  let e := galoisSemilinearDescendedTensorBaseChangeIso K L
    (RelatedTripleCoordinateScalarExtension L) aA
  change ModuleCat.of L (TensorProduct K LK (TensorProduct K M M)) ≅
    ModuleCat.of L
      (TensorProduct L (RelatedTripleCoordinateScalarExtension L)
        (RelatedTripleCoordinateScalarExtension L)) at e
  exact e.toLinearEquiv

/-- The canonical comparison-coalgebra tensor-square carrier isomorphism. -/
noncomputable def relatedTripleCoordinateGaloisComparisonTensorSquareIso
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    let a := coordinateModuleAction K L diagram
    let M := galoisSemilinearDescendedModule K L
      (RelatedTripleCoordinateScalarExtension L) a
    let N := ModuleCat.of K (TensorProduct K M M)
    ((comonadicModuleDescentComparison (algebraMap K L)).obj N).A ≅
      ModuleCat.of L
        (TensorProduct L (RelatedTripleCoordinateScalarExtension L)
          (RelatedTripleCoordinateScalarExtension L)) := by
  dsimp only
  let a := coordinateModuleAction K L diagram
  let M := galoisSemilinearDescendedModule K L
    (RelatedTripleCoordinateScalarExtension L) a
  let LK := (ModuleCat.restrictScalars (algebraMap K L)).obj
    (ModuleCat.of L L)
  letI : Module K LK := LK.isModule
  letI : IsScalarTower K L LK :=
    IsScalarTower.of_algebraMap_smul (by intro k x; rfl)
  change ModuleCat.of L (TensorProduct K LK (TensorProduct K M M)) ≅
    ModuleCat.of L
      (TensorProduct L (RelatedTripleCoordinateScalarExtension L)
        (RelatedTripleCoordinateScalarExtension L))
  exact
    (relatedTripleCoordinateGaloisComparisonTensorSquareLinearEquiv
      K L diagram).toModuleIso

set_option maxHeartbeats 1000000 in
-- Unfolding the tensor-square base-change equivalence on a generator is costly.
set_option linter.style.haveILetI false in
/-- The selected tensor-square comparison on a pure generator is the tensor
product of the two selected coordinate base-change comparisons. -/
@[simp] theorem
    relatedTripleCoordinateGaloisComparisonTensorSquareLinearEquiv_tmul
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry)
    (l : L)
    (m n : galoisSemilinearDescendedModule K L
      (RelatedTripleCoordinateScalarExtension L)
      (coordinateModuleAction K L diagram)) :
    let a := coordinateModuleAction K L diagram
    let LK := (ModuleCat.restrictScalars (algebraMap K L)).obj
      (ModuleCat.of L L)
    letI : Module K LK := LK.isModule
    letI : IsScalarTower K L LK :=
      IsScalarTower.of_algebraMap_smul (by intro k x; rfl)
    let eD := galoisSemilinearDescendedModuleBaseChangeIso K L
      (RelatedTripleCoordinateScalarExtension L) a
    relatedTripleCoordinateGaloisComparisonTensorSquareLinearEquiv K L diagram
        ((relatedTripleCoordinateGaloisScalarRestrictLinearEquiv K L l) ⊗ₜ[K]
          (m ⊗ₜ[K] n)) =
      eD.hom
          ((relatedTripleCoordinateGaloisScalarRestrictLinearEquiv
            K L l) ⊗ₜ[K] m) ⊗ₜ[L]
        eD.hom
          ((relatedTripleCoordinateGaloisScalarRestrictLinearEquiv
            K L (1 : L)) ⊗ₜ[K] n) := by
  dsimp only
  rfl

/-- A scalar-pure coordinate coaction in each tensor factor gives the
corresponding scalar-pure diagonal tensor-square coaction. -/
theorem galoisSemilinearTensorSquareCoaction_of_pure_factors
    (K L A : Type u) [Field K] [Field L] [Algebra K L]
    [CommRing A] [Algebra K A] [Algebra L A] [IsScalarTower K L A]
    [FiniteDimensional K L] [IsGalois K L]
    (a : GaloisSemilinearAlgebraAction K L A)
    (l : L) (xl x0 y0 : A)
    (hx : galoisSemilinearCoaction K L A
        (a.toModuleAction K L A) xl = l ⊗ₜ[K] x0)
    (hy : galoisSemilinearCoaction K L A
        (a.toModuleAction K L A) y0 = (1 : L) ⊗ₜ[K] y0) :
    galoisSemilinearCoaction K L (TensorProduct L A A)
        (galoisSemilinearTensorSquareAction K L A a)
        (xl ⊗ₜ[L] y0) =
      l ⊗ₜ[K] (x0 ⊗ₜ[L] y0) := by
  apply (galoisSemilinearTensorEquiv K L (TensorProduct L A A)
    (galoisSemilinearTensorSquareAction K L A a)).injective
  ext σ
  rw [galoisSemilinearTensorEquiv_coaction_apply,
    galoisSemilinearTensorEquiv_tmul_apply,
    galoisSemilinearTensorSquareAction_tmul]
  have hxσ := congrArg
    (fun z => galoisSemilinearTensorEquiv K L A
      (a.toModuleAction K L A) z σ) hx
  have hyσ := congrArg
    (fun z => galoisSemilinearTensorEquiv K L A
      (a.toModuleAction K L A) z σ) hy
  rw [galoisSemilinearTensorEquiv_coaction_apply,
    galoisSemilinearTensorEquiv_tmul_apply] at hxσ hyσ
  simp only [one_smul] at hyσ
  change xl ⊗ₜ[L] y0 =
    l • (a.action σ x0 ⊗ₜ[L] a.action σ y0)
  have hxσ' : xl = l • a.action σ x0 := hxσ
  have hyσ' : y0 = a.action σ y0 := hyσ
  calc
    xl ⊗ₜ[L] y0 =
        (l • a.action σ x0) ⊗ₜ[L] y0 :=
      congrArg (fun z => z ⊗ₜ[L] y0) hxσ'
    _ = (l • a.action σ x0) ⊗ₜ[L] a.action σ y0 :=
      congrArg (fun z => (l • a.action σ x0) ⊗ₜ[L] z) hyσ'
    _ = l • (a.action σ x0 ⊗ₜ[L] a.action σ y0) :=
      (TensorProduct.smul_tmul' l (a.action σ x0)
        (a.action σ y0)).symm

set_option maxHeartbeats 1200000 in
-- The proof performs nested tensor inductions and normalizes two bridge layers.
set_option linter.style.haveILetI false in
/-- The selected tensor-square comparison is compatible with the canonical
diagonal finite-Galois coaction. -/
theorem relatedTripleCoordinateGaloisComparisonTensorSquare_coaction
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    let aA := coordinateAlgebraAction K L diagram
    let a := coordinateModuleAction K L diagram
    let M := galoisSemilinearDescendedModule K L
      (RelatedTripleCoordinateScalarExtension L) a
    let N := ModuleCat.of K (TensorProduct K M M)
    let Q := galoisSemilinearComonadicDescentData K L
      (TensorProduct L (RelatedTripleCoordinateScalarExtension L)
        (RelatedTripleCoordinateScalarExtension L))
      (galoisSemilinearTensorSquareAction K L
        (RelatedTripleCoordinateScalarExtension L) aA)
    let G := (ModuleCat.extendRestrictScalarsAdj
      (algebraMap K L)).toComonad
    let e := relatedTripleCoordinateGaloisComparisonTensorSquareIso
      K L diagram
    ((comonadicModuleDescentComparison (algebraMap K L)).obj N).a ≫
        G.map e.hom =
      e.hom ≫ Q.a := by
  dsimp only
  let aA := coordinateAlgebraAction K L diagram
  let a := coordinateModuleAction K L diagram
  let M := galoisSemilinearDescendedModule K L
    (RelatedTripleCoordinateScalarExtension L) a
  let N := ModuleCat.of K (TensorProduct K M M)
  let Q := galoisSemilinearComonadicDescentData K L
    (TensorProduct L (RelatedTripleCoordinateScalarExtension L)
      (RelatedTripleCoordinateScalarExtension L))
    (galoisSemilinearTensorSquareAction K L
      (RelatedTripleCoordinateScalarExtension L) aA)
  let G := (ModuleCat.extendRestrictScalarsAdj
    (algebraMap K L)).toComonad
  let e := relatedTripleCoordinateGaloisComparisonTensorSquareIso
    K L diagram
  let LK := (ModuleCat.restrictScalars (algebraMap K L)).obj
    (ModuleCat.of L L)
  letI : Module K LK := LK.isModule
  letI : IsScalarTower K L LK :=
    IsScalarTower.of_algebraMap_smul (by intro k x; rfl)
  let T := TensorProduct K LK (TensorProduct K M M)
  let Y : ModuleCat L := G.obj Q.A
  let lhs : T →ₗ[L] Y := ModuleCat.Hom.hom
    (((comonadicModuleDescentComparison (algebraMap K L)).obj N).a ≫
      G.map e.hom)
  let rhs : T →ₗ[L] Y := ModuleCat.Hom.hom (e.hom ≫ Q.a)
  apply ModuleCat.hom_ext
  change lhs = rhs
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul l z =>
      induction z using TensorProduct.induction_on with
      | zero => simp only [TensorProduct.tmul_zero, map_zero]
      | tmul m n =>
          dsimp [lhs, rhs]
          change L at l
          let eRaw :=
            relatedTripleCoordinateGaloisComparisonTensorSquareLinearEquiv
              K L diagram
          let eD := galoisSemilinearDescendedModuleBaseChangeIso K L
            (RelatedTripleCoordinateScalarExtension L) a
          have he : e.hom = ModuleCat.ofHom eRaw.toLinearMap := by rfl
          rw [he]
          change
            ConcreteCategory.hom
                (G.map (ModuleCat.ofHom eRaw.toLinearMap))
                (galoisSemilinearComonadicTensorEquiv K L T
                  (l ⊗ₜ[K]
                    ((relatedTripleCoordinateGaloisScalarRestrictLinearEquiv
                      K L (1 : L)) ⊗ₜ[K] (m ⊗ₜ[K] n)))) =
              galoisSemilinearComonadicTensorEquiv K L
                (TensorProduct L
                  (RelatedTripleCoordinateScalarExtension L)
                  (RelatedTripleCoordinateScalarExtension L))
                (galoisSemilinearCoaction K L
                  (TensorProduct L
                    (RelatedTripleCoordinateScalarExtension L)
                    (RelatedTripleCoordinateScalarExtension L))
                  (galoisSemilinearTensorSquareAction K L
                    (RelatedTripleCoordinateScalarExtension L) aA)
                  (eRaw
                    ((relatedTripleCoordinateGaloisScalarRestrictLinearEquiv
                      K L l) ⊗ₜ[K] (m ⊗ₜ[K] n))))
          rw [galoisSemilinearComonadicTensorMap,
            LinearMap.baseChange_tmul]
          have hinner :
              (eRaw.toLinearMap.restrictScalars K)
                  ((relatedTripleCoordinateGaloisScalarRestrictLinearEquiv
                    K L (1 : L)) ⊗ₜ[K] (m ⊗ₜ[K] n)) =
                eD.hom
                    ((relatedTripleCoordinateGaloisScalarRestrictLinearEquiv
                      K L (1 : L)) ⊗ₜ[K] m) ⊗ₜ[L]
                  eD.hom
                    ((relatedTripleCoordinateGaloisScalarRestrictLinearEquiv
                      K L (1 : L)) ⊗ₜ[K] n) := by
            change eRaw
                ((relatedTripleCoordinateGaloisScalarRestrictLinearEquiv
                  K L (1 : L)) ⊗ₜ[K] (m ⊗ₜ[K] n)) = _
            exact
              relatedTripleCoordinateGaloisComparisonTensorSquareLinearEquiv_tmul
                K L diagram 1 m n
          rw [hinner,
            relatedTripleCoordinateGaloisComparisonTensorSquareLinearEquiv_tmul]
          let xl := eD.hom
            ((relatedTripleCoordinateGaloisScalarRestrictLinearEquiv
              K L l) ⊗ₜ[K] m)
          let x0 := eD.hom
            ((relatedTripleCoordinateGaloisScalarRestrictLinearEquiv
              K L (1 : L)) ⊗ₜ[K] m)
          let y0 := eD.hom
            ((relatedTripleCoordinateGaloisScalarRestrictLinearEquiv
              K L (1 : L)) ⊗ₜ[K] n)
          have hx :
              galoisSemilinearCoaction K L
                  (RelatedTripleCoordinateScalarExtension L) a xl =
                l ⊗ₜ[K] x0 := by
            exact relatedTripleCoordinateGaloisCoordinateBaseChange_coaction
              K L diagram l m
          have hy :
              galoisSemilinearCoaction K L
                  (RelatedTripleCoordinateScalarExtension L) a y0 =
                (1 : L) ⊗ₜ[K] y0 := by
            exact relatedTripleCoordinateGaloisCoordinateBaseChange_coaction
              K L diagram 1 n
          have hraw :=
            galoisSemilinearTensorSquareCoaction_of_pure_factors
              K L (RelatedTripleCoordinateScalarExtension L)
              aA l xl x0 y0 hx hy
          exact congrArg
            (galoisSemilinearComonadicTensorEquiv K L
              (TensorProduct L
                (RelatedTripleCoordinateScalarExtension L)
                (RelatedTripleCoordinateScalarExtension L)))
            hraw.symm
      | add x y hx hy =>
          simpa only [TensorProduct.tmul_add, map_add] using
            congrArg₂ (· + ·) hx hy
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- The selected tensor-square datum, transported through the canonical
bridge, is isomorphic to canonical diagonal finite-Galois descent. -/
noncomputable def relatedTripleCoordinateGaloisSelectedTensorSquareComonadicIso
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    let f := CommRingCat.ofHom (algebraMap K L)
    let hf := galoisFieldAlgebraMap_faithfullyFlat K L
    let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
    let T := affineCechSelectedTensorDescentData f hf D D
    let aA := coordinateAlgebraAction K L diagram
    let Q := galoisSemilinearComonadicDescentData K L
      (TensorProduct L (RelatedTripleCoordinateScalarExtension L)
        (RelatedTripleCoordinateScalarExtension L))
      (galoisSemilinearTensorSquareAction K L
        (RelatedTripleCoordinateScalarExtension L) aA)
    let E := (affineCechComonadicBridge f).equivalence
    E.functor.obj T ≅ Q := by
  dsimp only
  let f := CommRingCat.ofHom (algebraMap K L)
  let hf := galoisFieldAlgebraMap_faithfullyFlat K L
  let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
  let M := affineCechDescendedModule f hf D
  let N := ModuleCat.of K (TensorProduct K M M)
  let aA := coordinateAlgebraAction K L diagram
  let Q := galoisSemilinearComonadicDescentData K L
    (TensorProduct L (RelatedTripleCoordinateScalarExtension L)
      (RelatedTripleCoordinateScalarExtension L))
    (galoisSemilinearTensorSquareAction K L
      (RelatedTripleCoordinateScalarExtension L) aA)
  let c := (affineCechComonadicBridge f).comparisonIso.app N
  let e := relatedTripleCoordinateGaloisComparisonTensorSquareIso
    K L diagram
  let q : (comonadicModuleDescentComparison (algebraMap K L)).obj N ≅ Q :=
    Comonad.Coalgebra.isoMk e
      (relatedTripleCoordinateGaloisComparisonTensorSquare_coaction
        K L diagram)
  exact c ≪≫ q

/-- The selected affine Čech tensor square is isomorphic to the canonical
finite-Galois diagonal tensor-square datum. -/
noncomputable def relatedTripleCoordinateGaloisSelectedTensorSquareCechIso
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    let f := CommRingCat.ofHom (algebraMap K L)
    let hf := galoisFieldAlgebraMap_faithfullyFlat K L
    let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
    let T := affineCechSelectedTensorDescentData f hf D D
    T ≅ relatedTripleCoordinateGaloisTensorSquareCechModuleDescentData
      K L diagram := by
  dsimp only
  let f := CommRingCat.ofHom (algebraMap K L)
  let hf := galoisFieldAlgebraMap_faithfullyFlat K L
  let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
  let T := affineCechSelectedTensorDescentData f hf D D
  let aA := coordinateAlgebraAction K L diagram
  let Q := galoisSemilinearComonadicDescentData K L
    (TensorProduct L (RelatedTripleCoordinateScalarExtension L)
      (RelatedTripleCoordinateScalarExtension L))
    (galoisSemilinearTensorSquareAction K L
      (RelatedTripleCoordinateScalarExtension L) aA)
  exact affineCechIsoOfComonadicIso f T Q
    (relatedTripleCoordinateGaloisSelectedTensorSquareComonadicIso
      K L diagram)

end

end RiemannResearch.AlgebraicGeometry
