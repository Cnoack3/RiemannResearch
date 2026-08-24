/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.D4ZornCoordinateGaloisSelectedBialgebraLaws

/-!
# Selected D4 antipode laws in affine Čech descent

This module proves the two selected convolution-inverse identities for the
finite-Galois D4 coordinate antipode and packages the resulting commutative
Hopf algebra object.

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

private abbrev ASelectedHopf := RelatedTripleCoordinateRing.{0}

local instance coordinateGaloisSelectedHopfCommRing :
    CommRing ASelectedHopf :=
  inferInstance

set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 200000 in
-- The cover proof normalizes a selected tensor map against the antipode.
set_option maxHeartbeats 3000000 in
set_option linter.style.haveILetI false in
/-- The selected coordinate antipode is a left convolution inverse to the
identity. -/
theorem relatedTripleCoordinateGaloisSelectedAntipode_mul_left
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    let f := CommRingCat.ofHom (algebraMap K L)
    let hf := galoisFieldAlgebraMap_faithfullyFlat K L
    let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
    let comul :=
      relatedTripleCoordinateGaloisSelectedComulDescentMap K L diagram
    let antipode :=
      relatedTripleCoordinateGaloisSelectedAntipodeDescentMap K L diagram
    let mul := relatedTripleCoordinateGaloisSelectedMulDescentMap K L diagram
    let counit :=
      relatedTripleCoordinateGaloisSelectedCounitDescentMap K L diagram
    let unit := relatedTripleCoordinateGaloisSelectedUnitDescentMap K L diagram
    comul ≫ affineCechSelectedTensorMap f hf antipode (𝟙 D) ≫ mul =
      counit ≫ unit := by
  dsimp only
  let f := CommRingCat.ofHom (algebraMap K L)
  let hf := galoisFieldAlgebraMap_faithfullyFlat K L
  let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
  let U := affineCechSelectedTensorUnitDescentData f
  let T := affineCechSelectedTensorDescentData f hf D D
  let B := RelatedTripleCoordinateScalarExtension L
  let comul :=
    relatedTripleCoordinateGaloisSelectedComulDescentMap K L diagram
  let antipode :=
    relatedTripleCoordinateGaloisSelectedAntipodeDescentMap K L diagram
  let mul := relatedTripleCoordinateGaloisSelectedMulDescentMap K L diagram
  let counit :=
    relatedTripleCoordinateGaloisSelectedCounitDescentMap K L diagram
  let unit := relatedTripleCoordinateGaloisSelectedUnitDescentMap K L diagram
  let DA : ModuleCat L := ModuleCat.of L B
  let UA : ModuleCat L := (AffineCechModuleDescentData.evaluation f).obj U
  let TA : ModuleCat L := (AffineCechModuleDescentData.evaluation f).obj T
  let eU : UA ≅ ModuleCat.of L L :=
    affineCechSelectedTensorUnitCoverIso f
  let eT : TA ≅ ModuleCat.of L (TensorProduct L DA DA) :=
    affineCechSelectedTensorDescentDataCoverIso f hf D D
  let comulA : DA ⟶ TA := comul.hom PUnit.unit
  let antipodeA : DA ⟶ DA := antipode.hom PUnit.unit
  let mulA : TA ⟶ DA := mul.hom PUnit.unit
  let counitA : DA ⟶ UA := counit.hom PUnit.unit
  let unitA : UA ⟶ DA := unit.hom PUnit.unit
  let deltaA : DA ⟶ ModuleCat.of L (TensorProduct L DA DA) :=
    ModuleCat.ofHom
      (CoalgebraStruct.comul : B →ₗ[L] TensorProduct L B B)
  let sigmaA : DA ⟶ DA :=
    ModuleCat.ofHom
      (HopfAlgebraStruct.antipode L : B →ₗ[L] B)
  let muA : ModuleCat.of L (TensorProduct L DA DA) ⟶ DA :=
    ModuleCat.ofHom (galoisAlgebraMultiplicationLinearMap L B)
  let epsA : DA ⟶ ModuleCat.of L L :=
    ModuleCat.ofHom (CoalgebraStruct.counit : B →ₗ[L] L)
  let etaA : ModuleCat.of L L ⟶ DA :=
    ModuleCat.ofHom (Algebra.linearMap L B)
  let tm : TA ⟶ TA :=
    (affineCechSelectedTensorMap f hf antipode (𝟙 D)).hom PUnit.unit
  let mapm : ModuleCat.of L (TensorProduct L DA DA) ⟶
      ModuleCat.of L (TensorProduct L DA DA) :=
    ModuleCat.ofHom
      (TensorProduct.map
        (ModuleCat.Hom.hom
          ((AffineCechModuleDescentData.evaluation f).map antipode))
        (ModuleCat.Hom.hom
          ((AffineCechModuleDescentData.evaluation f).map (𝟙 D))))
  have hc : comulA ≫ eT.hom = deltaA :=
    relatedTripleCoordinateGaloisSelectedComulDescentMap_cover K L diagram
  have hs : antipodeA = sigmaA :=
    relatedTripleCoordinateGaloisSelectedAntipodeDescentMap_cover K L diagram
  have hm : eT.inv ≫ mulA = muA :=
    relatedTripleCoordinateGaloisSelectedMulDescentMap_cover K L diagram
  have he : counitA ≫ eU.hom = epsA :=
    relatedTripleCoordinateGaloisSelectedCounitDescentMap_cover K L diagram
  have hu : eU.inv ≫ unitA = etaA :=
    relatedTripleCoordinateGaloisSelectedUnitDescentMap_cover K L diagram
  have hn : tm ≫ eT.hom = eT.hom ≫ mapm :=
    affineCechSelectedTensorDescentDataCoverIso_natural
      f hf antipode (𝟙 D)
  have htm : eT.inv ≫ tm ≫ eT.hom = mapm := by
    have h := congrArg (fun z => eT.inv ≫ z) hn
    simpa only [Category.assoc, eT.inv_hom_id_assoc] using h
  have hmap :
      mapm = ModuleCat.ofHom
        (LinearMap.rTensor B
          (HopfAlgebraStruct.antipode L : B →ₗ[L] B)) := by
    apply ModuleCat.hom_ext
    change
      TensorProduct.map (ModuleCat.Hom.hom antipodeA)
          (ModuleCat.Hom.hom (𝟙 DA)) =
        LinearMap.rTensor B (HopfAlgebraStruct.antipode L)
    rw [hs]
    simp only [ModuleCat.hom_id]
    exact (LinearMap.rTensor_def B _).symm
  have hstd : deltaA ≫ mapm ≫ muA = epsA ≫ etaA := by
    rw [hmap]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    change
      galoisAlgebraMultiplicationLinearMap L B
          ((LinearMap.rTensor B (HopfAlgebraStruct.antipode L))
            (CoalgebraStruct.comul x)) =
        Algebra.linearMap L B (CoalgebraStruct.counit x)
    exact LinearMap.congr_fun
      (HopfAlgebra.mul_antipode_rTensor_comul (R := L) (A := B)) x
  have hcover :
      comulA ≫ tm ≫ mulA = counitA ≫ unitA := by
    calc
      comulA ≫ tm ≫ mulA =
          (comulA ≫ eT.hom) ≫
            (eT.inv ≫ tm ≫ eT.hom) ≫ (eT.inv ≫ mulA) := by
              simp only [Category.assoc, eT.hom_inv_id_assoc]
      _ = deltaA ≫ mapm ≫ muA := by rw [hc, htm, hm]
      _ = epsA ≫ etaA := hstd
      _ = (counitA ≫ eU.hom) ≫ (eU.inv ≫ unitA) := by rw [he, hu]
      _ = counitA ≫ unitA := by
            simp only [Category.assoc, eU.hom_inv_id_assoc]
  ext i
  cases i
  change comulA ≫ tm ≫ mulA = counitA ≫ unitA
  exact hcover

set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 200000 in
-- The cover proof normalizes a selected tensor map against the antipode.
set_option maxHeartbeats 3000000 in
set_option linter.style.haveILetI false in
/-- The selected coordinate antipode is a right convolution inverse to the
identity. -/
theorem relatedTripleCoordinateGaloisSelectedAntipode_mul_right
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    let f := CommRingCat.ofHom (algebraMap K L)
    let hf := galoisFieldAlgebraMap_faithfullyFlat K L
    let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
    let comul :=
      relatedTripleCoordinateGaloisSelectedComulDescentMap K L diagram
    let antipode :=
      relatedTripleCoordinateGaloisSelectedAntipodeDescentMap K L diagram
    let mul := relatedTripleCoordinateGaloisSelectedMulDescentMap K L diagram
    let counit :=
      relatedTripleCoordinateGaloisSelectedCounitDescentMap K L diagram
    let unit := relatedTripleCoordinateGaloisSelectedUnitDescentMap K L diagram
    comul ≫ affineCechSelectedTensorMap f hf (𝟙 D) antipode ≫ mul =
      counit ≫ unit := by
  dsimp only
  let f := CommRingCat.ofHom (algebraMap K L)
  let hf := galoisFieldAlgebraMap_faithfullyFlat K L
  let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
  let U := affineCechSelectedTensorUnitDescentData f
  let T := affineCechSelectedTensorDescentData f hf D D
  let B := RelatedTripleCoordinateScalarExtension L
  let comul :=
    relatedTripleCoordinateGaloisSelectedComulDescentMap K L diagram
  let antipode :=
    relatedTripleCoordinateGaloisSelectedAntipodeDescentMap K L diagram
  let mul := relatedTripleCoordinateGaloisSelectedMulDescentMap K L diagram
  let counit :=
    relatedTripleCoordinateGaloisSelectedCounitDescentMap K L diagram
  let unit := relatedTripleCoordinateGaloisSelectedUnitDescentMap K L diagram
  let DA : ModuleCat L := ModuleCat.of L B
  let UA : ModuleCat L := (AffineCechModuleDescentData.evaluation f).obj U
  let TA : ModuleCat L := (AffineCechModuleDescentData.evaluation f).obj T
  let eU : UA ≅ ModuleCat.of L L :=
    affineCechSelectedTensorUnitCoverIso f
  let eT : TA ≅ ModuleCat.of L (TensorProduct L DA DA) :=
    affineCechSelectedTensorDescentDataCoverIso f hf D D
  let comulA : DA ⟶ TA := comul.hom PUnit.unit
  let antipodeA : DA ⟶ DA := antipode.hom PUnit.unit
  let mulA : TA ⟶ DA := mul.hom PUnit.unit
  let counitA : DA ⟶ UA := counit.hom PUnit.unit
  let unitA : UA ⟶ DA := unit.hom PUnit.unit
  let deltaA : DA ⟶ ModuleCat.of L (TensorProduct L DA DA) :=
    ModuleCat.ofHom
      (CoalgebraStruct.comul : B →ₗ[L] TensorProduct L B B)
  let sigmaA : DA ⟶ DA :=
    ModuleCat.ofHom
      (HopfAlgebraStruct.antipode L : B →ₗ[L] B)
  let muA : ModuleCat.of L (TensorProduct L DA DA) ⟶ DA :=
    ModuleCat.ofHom (galoisAlgebraMultiplicationLinearMap L B)
  let epsA : DA ⟶ ModuleCat.of L L :=
    ModuleCat.ofHom (CoalgebraStruct.counit : B →ₗ[L] L)
  let etaA : ModuleCat.of L L ⟶ DA :=
    ModuleCat.ofHom (Algebra.linearMap L B)
  let tm : TA ⟶ TA :=
    (affineCechSelectedTensorMap f hf (𝟙 D) antipode).hom PUnit.unit
  let mapm : ModuleCat.of L (TensorProduct L DA DA) ⟶
      ModuleCat.of L (TensorProduct L DA DA) :=
    ModuleCat.ofHom
      (TensorProduct.map
        (ModuleCat.Hom.hom
          ((AffineCechModuleDescentData.evaluation f).map (𝟙 D)))
        (ModuleCat.Hom.hom
          ((AffineCechModuleDescentData.evaluation f).map antipode)))
  have hc : comulA ≫ eT.hom = deltaA :=
    relatedTripleCoordinateGaloisSelectedComulDescentMap_cover K L diagram
  have hs : antipodeA = sigmaA :=
    relatedTripleCoordinateGaloisSelectedAntipodeDescentMap_cover K L diagram
  have hm : eT.inv ≫ mulA = muA :=
    relatedTripleCoordinateGaloisSelectedMulDescentMap_cover K L diagram
  have he : counitA ≫ eU.hom = epsA :=
    relatedTripleCoordinateGaloisSelectedCounitDescentMap_cover K L diagram
  have hu : eU.inv ≫ unitA = etaA :=
    relatedTripleCoordinateGaloisSelectedUnitDescentMap_cover K L diagram
  have hn : tm ≫ eT.hom = eT.hom ≫ mapm :=
    affineCechSelectedTensorDescentDataCoverIso_natural
      f hf (𝟙 D) antipode
  have htm : eT.inv ≫ tm ≫ eT.hom = mapm := by
    have h := congrArg (fun z => eT.inv ≫ z) hn
    simpa only [Category.assoc, eT.inv_hom_id_assoc] using h
  have hmap :
      mapm = ModuleCat.ofHom
        (LinearMap.lTensor B
          (HopfAlgebraStruct.antipode L : B →ₗ[L] B)) := by
    apply ModuleCat.hom_ext
    change
      TensorProduct.map (ModuleCat.Hom.hom (𝟙 DA))
          (ModuleCat.Hom.hom antipodeA) =
        LinearMap.lTensor B (HopfAlgebraStruct.antipode L)
    rw [hs]
    simp only [ModuleCat.hom_id]
    exact (LinearMap.lTensor_def B _).symm
  have hstd : deltaA ≫ mapm ≫ muA = epsA ≫ etaA := by
    rw [hmap]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    change
      galoisAlgebraMultiplicationLinearMap L B
          ((LinearMap.lTensor B (HopfAlgebraStruct.antipode L))
            (CoalgebraStruct.comul x)) =
        Algebra.linearMap L B (CoalgebraStruct.counit x)
    exact LinearMap.congr_fun
      (HopfAlgebra.mul_antipode_lTensor_comul (R := L) (A := B)) x
  have hcover :
      comulA ≫ tm ≫ mulA = counitA ≫ unitA := by
    calc
      comulA ≫ tm ≫ mulA =
          (comulA ≫ eT.hom) ≫
            (eT.inv ≫ tm ≫ eT.hom) ≫ (eT.inv ≫ mulA) := by
              simp only [Category.assoc, eT.hom_inv_id_assoc]
      _ = deltaA ≫ mapm ≫ muA := by rw [hc, htm, hm]
      _ = epsA ≫ etaA := hstd
      _ = (counitA ≫ eU.hom) ≫ (eU.inv ≫ unitA) := by rw [he, hu]
      _ = counitA ≫ unitA := by
            simp only [Category.assoc, eU.hom_inv_id_assoc]
  ext i
  cases i
  change comulA ≫ tm ≫ mulA = counitA ≫ unitA
  exact hcover

/-- The finite-Galois D4 coordinate maps form a commutative Hopf algebra
object in the selected affine Čech tensor structure. -/
noncomputable def relatedTripleCoordinateGaloisSelectedCommHopfAlgebraObject
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    let f := CommRingCat.ofHom (algebraMap K L)
    let hf := galoisFieldAlgebraMap_faithfullyFlat K L
    AffineCechSelectedCommHopfAlgebraObject f hf := by
  dsimp only
  let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
  exact
    { obj := D
      mul := relatedTripleCoordinateGaloisSelectedMulDescentMap K L diagram
      unit := relatedTripleCoordinateGaloisSelectedUnitDescentMap K L diagram
      mul_assoc := relatedTripleCoordinateGaloisSelectedMul_assoc K L diagram
      unit_mul := relatedTripleCoordinateGaloisSelectedUnit_mul K L diagram
      mul_unit := relatedTripleCoordinateGaloisSelectedMul_unit K L diagram
      comul :=
        relatedTripleCoordinateGaloisSelectedComulDescentMap K L diagram
      counit :=
        relatedTripleCoordinateGaloisSelectedCounitDescentMap K L diagram
      comul_assoc :=
        relatedTripleCoordinateGaloisSelectedComul_coassoc K L diagram
      counit_left :=
        relatedTripleCoordinateGaloisSelectedCounit_left K L diagram
      counit_right :=
        relatedTripleCoordinateGaloisSelectedCounit_right K L diagram
      comul_mul :=
        relatedTripleCoordinateGaloisSelectedComul_mul K L diagram
      comul_unit :=
        relatedTripleCoordinateGaloisSelectedComul_unit K L diagram
      counit_mul :=
        relatedTripleCoordinateGaloisSelectedCounit_mul K L diagram
      counit_unit :=
        relatedTripleCoordinateGaloisSelectedCounit_unit K L diagram
      antipode :=
        relatedTripleCoordinateGaloisSelectedAntipodeDescentMap K L diagram
      antipode_mul_left :=
        relatedTripleCoordinateGaloisSelectedAntipode_mul_left K L diagram
      antipode_mul_right :=
        relatedTripleCoordinateGaloisSelectedAntipode_mul_right K L diagram
      mul_comm := relatedTripleCoordinateGaloisSelectedMul_comm K L diagram }

end

end RiemannResearch.AlgebraicGeometry
