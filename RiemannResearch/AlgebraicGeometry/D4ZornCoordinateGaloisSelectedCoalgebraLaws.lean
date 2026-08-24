/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.D4ZornCoordinateGaloisSelectedHopfAssembly

/-!
# Selected D4 coalgebra laws in affine Čech descent

This module proves the coalgebra equations for the finite-Galois D4 coordinate
maps conjugated into the tensor structure selected by effective affine Čech
descent.  Coassociativity is transported from the ordinary coordinate Hopf
algebra by the exact left- and right-nested cover formulas.

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

set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 200000 in
-- Cover-comparison conjugation elaborates several nested tensor objects.
set_option maxHeartbeats 3000000 in
set_option linter.style.haveILetI false in
/-- The selected coordinate comultiplication is coassociative with respect to
the selected tensor associator. -/
theorem relatedTripleCoordinateGaloisSelectedComul_coassoc
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    let f := CommRingCat.ofHom (algebraMap K L)
    let hf := galoisFieldAlgebraMap_faithfullyFlat K L
    let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
    let comul :=
      relatedTripleCoordinateGaloisSelectedComulDescentMap K L diagram
    comul ≫ affineCechSelectedTensorMap f hf comul (𝟙 D) ≫
        (affineCechSelectedTensorAssociatorIso f hf D D D).hom =
      comul ≫ affineCechSelectedTensorMap f hf (𝟙 D) comul := by
  dsimp only
  let f := CommRingCat.ofHom (algebraMap K L)
  let hf := galoisFieldAlgebraMap_faithfullyFlat K L
  let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
  let comul :=
    relatedTripleCoordinateGaloisSelectedComulDescentMap K L diagram
  let eL := affineCechSelectedTensorLeftAssociatedCoverIso f hf D D D
  let eR := affineCechSelectedTensorRightAssociatedCoverIso f hf D D D
  let B := RelatedTripleCoordinateScalarExtension L
  let deltaA : ModuleCat.of L B ⟶
      ModuleCat.of L (TensorProduct L B B) :=
    ModuleCat.ofHom (CoalgebraStruct.comul : B →ₗ[L] TensorProduct L B B)
  let leftA : ModuleCat.of L (TensorProduct L B B) ⟶
      ModuleCat.of L (TensorProduct L (TensorProduct L B B) B) :=
    ModuleCat.ofHom (TensorProduct.map
      (CoalgebraStruct.comul : B →ₗ[L] TensorProduct L B B) LinearMap.id)
  let rightA : ModuleCat.of L (TensorProduct L B B) ⟶
      ModuleCat.of L (TensorProduct L B (TensorProduct L B B)) :=
    ModuleCat.ofHom (TensorProduct.map LinearMap.id
      (CoalgebraStruct.comul : B →ₗ[L] TensorProduct L B B))
  let assocA : ModuleCat.of L (TensorProduct L (TensorProduct L B B) B) ⟶
      ModuleCat.of L (TensorProduct L B (TensorProduct L B B)) :=
    ModuleCat.ofHom (TensorProduct.assoc L B B B).toLinearMap
  let a :=
    (affineCechSelectedTensorAssociatorIso f hf D D D).hom.hom PUnit.unit
  let tmL :=
    (affineCechSelectedTensorMap f hf comul (𝟙 D)).hom PUnit.unit
  let tmR :=
    (affineCechSelectedTensorMap f hf (𝟙 D) comul).hom PUnit.unit
  let comulA := comul.hom PUnit.unit
  have ha : a ≫ eR.hom = eL.hom ≫ assocA := by
    exact affineCechSelectedTensorAssociatorIso_cover f hf D D D
  have hl : comulA ≫ tmL ≫ eL.hom = deltaA ≫ leftA := by
    simpa only [comulA, tmL, eL, deltaA, leftA] using
      (relatedTripleCoordinateGaloisSelectedComulLeftNestedCover K L diagram)
  have hr : comulA ≫ tmR ≫ eR.hom = deltaA ≫ rightA := by
    simpa only [comulA, tmR, eR, deltaA, rightA] using
      (relatedTripleCoordinateGaloisSelectedComulRightNestedCover K L diagram)
  have hstd : deltaA ≫ leftA ≫ assocA = deltaA ≫ rightA := by
    apply ModuleCat.hom_ext
    exact Coalgebra.coassoc
  ext i
  cases i
  change comulA ≫ tmL ≫ a = comulA ≫ tmR
  letI : IsIso eR.hom := eR.isIso_hom
  letI : Mono eR.hom := IsIso.mono_of_iso eR.hom
  apply (cancel_mono eR.hom).mp
  have h0 :
      (comulA ≫ tmL ≫ a) ≫ eR.hom =
        (comulA ≫ tmL ≫ eL.hom) ≫ assocA := by
    let p := comulA ≫ tmL
    have h0raw := congrArg (fun z => p ≫ z) ha
    exact (Category.assoc p a eR.hom).trans
      (h0raw.trans (Category.assoc p eL.hom assocA).symm)
  have h1 :
      (comulA ≫ tmL ≫ eL.hom) ≫ assocA =
        (deltaA ≫ leftA) ≫ assocA :=
    congrArg (fun z => z ≫ assocA) hl
  have h2 : (deltaA ≫ leftA) ≫ assocA = deltaA ≫ rightA := by
    simpa only [Category.assoc] using hstd
  exact h0.trans (h1.trans (h2.trans hr.symm))

set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 200000 in
-- The cover proof conjugates the selected unit and tensor comparisons.
set_option maxHeartbeats 3000000 in
set_option linter.style.haveILetI false in
/-- The selected coordinate counit satisfies the left counit equation. -/
theorem relatedTripleCoordinateGaloisSelectedCounit_left
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    let f := CommRingCat.ofHom (algebraMap K L)
    let hf := galoisFieldAlgebraMap_faithfullyFlat K L
    let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
    let comul :=
      relatedTripleCoordinateGaloisSelectedComulDescentMap K L diagram
    let counit :=
      relatedTripleCoordinateGaloisSelectedCounitDescentMap K L diagram
    comul ≫ affineCechSelectedTensorMap f hf counit (𝟙 D) ≫
        (affineCechSelectedTensorLeftUnitorIso f hf D).hom =
      𝟙 D := by
  dsimp only
  let f := CommRingCat.ofHom (algebraMap K L)
  let hf := galoisFieldAlgebraMap_faithfullyFlat K L
  let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
  let U := affineCechSelectedTensorUnitDescentData f
  let T := affineCechSelectedTensorDescentData f hf D D
  let B := RelatedTripleCoordinateScalarExtension L
  let comul :=
    relatedTripleCoordinateGaloisSelectedComulDescentMap K L diagram
  let counit :=
    relatedTripleCoordinateGaloisSelectedCounitDescentMap K L diagram
  let DA : ModuleCat L := (AffineCechModuleDescentData.evaluation f).obj D
  let UA : ModuleCat L := (AffineCechModuleDescentData.evaluation f).obj U
  let TA : ModuleCat L := (AffineCechModuleDescentData.evaluation f).obj T
  let eT : TA ≅ ModuleCat.of L (TensorProduct L DA DA) :=
    affineCechSelectedTensorDescentDataCoverIso f hf D D
  let eU : UA ≅ ModuleCat.of L L :=
    affineCechSelectedTensorUnitCoverIso f
  let cL : (AffineCechModuleDescentData.evaluation f).obj
      (affineCechSelectedTensorDescentData f hf U D) ≅
      ModuleCat.of L (TensorProduct L UA DA) :=
    affineCechSelectedTensorDescentDataCoverIso f hf U D
  let qL := (TensorProduct.congr eU.toLinearEquiv
      (LinearEquiv.refl L DA)).toModuleIso
  let eL := affineCechSelectedTensorLeftUnitorCoverIso f hf D
  let comulA : DA ⟶ TA := comul.hom PUnit.unit
  let counitA : DA ⟶ UA := counit.hom PUnit.unit
  let deltaA : ModuleCat.of L B ⟶ ModuleCat.of L (TensorProduct L B B) :=
    ModuleCat.ofHom (CoalgebraStruct.comul :
      B →ₗ[L] TensorProduct L B B)
  let epsA : ModuleCat.of L B ⟶ ModuleCat.of L L :=
    ModuleCat.ofHom (CoalgebraStruct.counit :
      B →ₗ[L] L)
  let tm :=
    (affineCechSelectedTensorMap f hf counit (𝟙 D)).hom PUnit.unit
  let mapc : ModuleCat.of L (TensorProduct L DA DA) ⟶
      ModuleCat.of L (TensorProduct L UA DA) :=
    ModuleCat.ofHom (TensorProduct.map
      (ModuleCat.Hom.hom
        ((AffineCechModuleDescentData.evaluation f).map counit))
      (ModuleCat.Hom.hom
        ((AffineCechModuleDescentData.evaluation f).map (𝟙 D))))
  let std : ModuleCat.of L (TensorProduct L B B) ⟶
      ModuleCat.of L (TensorProduct L L B) :=
    ModuleCat.ofHom (TensorProduct.map (ModuleCat.Hom.hom epsA) LinearMap.id)
  let lidA : ModuleCat.of L (TensorProduct L L B) ⟶ ModuleCat.of L B :=
    ModuleCat.ofHom (TensorProduct.lid L B).toLinearMap
  have hc : comulA ≫ eT.hom = deltaA := by
    exact relatedTripleCoordinateGaloisSelectedComulDescentMap_cover K L diagram
  have he : counitA ≫ eU.hom = epsA := by
    exact relatedTripleCoordinateGaloisSelectedCounitDescentMap_cover K L diagram
  have hn : tm ≫ cL.hom = eT.hom ≫ mapc := by
    exact affineCechSelectedTensorDescentDataCoverIso_natural
      f hf counit (𝟙 D)
  have hpre : mapc ≫ qL.hom = std := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
        have hx := congrArg (fun z => ModuleCat.Hom.hom z x) he
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hx
        exact congrArg (fun z => z ⊗ₜ[L] (show DA from y)) hx
    | add x y hx hy => simp only [map_add, hx, hy]
  have hcoal :
      deltaA ≫ std =
        ModuleCat.ofHom ((TensorProduct.mk L L B) (1 : L)) := by
    apply ModuleCat.hom_ext
    exact Coalgebra.rTensor_counit_comp_comul
  have hstd : deltaA ≫ std ≫ lidA = 𝟙 (ModuleCat.of L B) := by
    have hcoal' := congrArg (fun z => z ≫ lidA) hcoal
    have hunit :
        ModuleCat.ofHom ((TensorProduct.mk L L B) (1 : L)) ≫ lidA =
          𝟙 (ModuleCat.of L B) := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (1 : L) • (show B from x) = x
      exact one_smul L x
    exact (Category.assoc deltaA std lidA).symm.trans
      (hcoal'.trans hunit)
  have h1 := congrArg (fun z => comulA ≫ z ≫ qL.hom ≫ lidA) hn
  have h2 := congrArg (fun z => z ≫ mapc ≫ qL.hom ≫ lidA) hc
  have h3 := congrArg (fun z => deltaA ≫ z ≫ lidA) hpre
  have hcover : comulA ≫ tm ≫ eL.hom ≫ lidA = 𝟙 DA := by
    change comulA ≫ tm ≫ (cL.hom ≫ qL.hom) ≫ lidA = 𝟙 DA
    exact h1.trans (h2.trans (h3.trans hstd))
  ext i
  cases i
  let ul :=
    (affineCechSelectedTensorLeftUnitorIso f hf D).hom.hom PUnit.unit
  have hu : ul = eL.hom ≫ lidA := by
    exact affineCechSelectedTensorLeftUnitorIso_cover f hf D
  change comulA ≫ tm ≫ ul = 𝟙 DA
  exact (congrArg (fun z => comulA ≫ tm ≫ z) hu).trans hcover

set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 200000 in
-- The cover proof conjugates the selected unit and tensor comparisons.
set_option maxHeartbeats 3000000 in
set_option linter.style.haveILetI false in
/-- The selected coordinate counit satisfies the right counit equation. -/
theorem relatedTripleCoordinateGaloisSelectedCounit_right
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    let f := CommRingCat.ofHom (algebraMap K L)
    let hf := galoisFieldAlgebraMap_faithfullyFlat K L
    let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
    let comul :=
      relatedTripleCoordinateGaloisSelectedComulDescentMap K L diagram
    let counit :=
      relatedTripleCoordinateGaloisSelectedCounitDescentMap K L diagram
    comul ≫ affineCechSelectedTensorMap f hf (𝟙 D) counit ≫
        (affineCechSelectedTensorRightUnitorIso f hf D).hom =
      𝟙 D := by
  dsimp only
  let f := CommRingCat.ofHom (algebraMap K L)
  let hf := galoisFieldAlgebraMap_faithfullyFlat K L
  let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
  let U := affineCechSelectedTensorUnitDescentData f
  let T := affineCechSelectedTensorDescentData f hf D D
  let B := RelatedTripleCoordinateScalarExtension L
  let comul :=
    relatedTripleCoordinateGaloisSelectedComulDescentMap K L diagram
  let counit :=
    relatedTripleCoordinateGaloisSelectedCounitDescentMap K L diagram
  let DA : ModuleCat L := (AffineCechModuleDescentData.evaluation f).obj D
  let UA : ModuleCat L := (AffineCechModuleDescentData.evaluation f).obj U
  let TA : ModuleCat L := (AffineCechModuleDescentData.evaluation f).obj T
  let eT : TA ≅ ModuleCat.of L (TensorProduct L DA DA) :=
    affineCechSelectedTensorDescentDataCoverIso f hf D D
  let eU : UA ≅ ModuleCat.of L L :=
    affineCechSelectedTensorUnitCoverIso f
  let cR : (AffineCechModuleDescentData.evaluation f).obj
      (affineCechSelectedTensorDescentData f hf D U) ≅
      ModuleCat.of L (TensorProduct L DA UA) :=
    affineCechSelectedTensorDescentDataCoverIso f hf D U
  let qR := (TensorProduct.congr (LinearEquiv.refl L DA)
      eU.toLinearEquiv).toModuleIso
  let eR := affineCechSelectedTensorRightUnitorCoverIso f hf D
  let comulA : DA ⟶ TA := comul.hom PUnit.unit
  let counitA : DA ⟶ UA := counit.hom PUnit.unit
  let deltaA : ModuleCat.of L B ⟶ ModuleCat.of L (TensorProduct L B B) :=
    ModuleCat.ofHom (CoalgebraStruct.comul :
      B →ₗ[L] TensorProduct L B B)
  let epsA : ModuleCat.of L B ⟶ ModuleCat.of L L :=
    ModuleCat.ofHom (CoalgebraStruct.counit : B →ₗ[L] L)
  let tm :=
    (affineCechSelectedTensorMap f hf (𝟙 D) counit).hom PUnit.unit
  let mapc : ModuleCat.of L (TensorProduct L DA DA) ⟶
      ModuleCat.of L (TensorProduct L DA UA) :=
    ModuleCat.ofHom (TensorProduct.map
      (ModuleCat.Hom.hom
        ((AffineCechModuleDescentData.evaluation f).map (𝟙 D)))
      (ModuleCat.Hom.hom
        ((AffineCechModuleDescentData.evaluation f).map counit)))
  let std : ModuleCat.of L (TensorProduct L B B) ⟶
      ModuleCat.of L (TensorProduct L B L) :=
    ModuleCat.ofHom (TensorProduct.map LinearMap.id (ModuleCat.Hom.hom epsA))
  let ridA : ModuleCat.of L (TensorProduct L B L) ⟶ ModuleCat.of L B :=
    ModuleCat.ofHom (TensorProduct.rid L B).toLinearMap
  have hc : comulA ≫ eT.hom = deltaA := by
    exact relatedTripleCoordinateGaloisSelectedComulDescentMap_cover K L diagram
  have he : counitA ≫ eU.hom = epsA := by
    exact relatedTripleCoordinateGaloisSelectedCounitDescentMap_cover K L diagram
  have hn : tm ≫ cR.hom = eT.hom ≫ mapc := by
    exact affineCechSelectedTensorDescentDataCoverIso_natural
      f hf (𝟙 D) counit
  have hpre : mapc ≫ qR.hom = std := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
        have hy := congrArg (fun z => ModuleCat.Hom.hom z y) he
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hy
        exact congrArg (fun z => (show DA from x) ⊗ₜ[L] z) hy
    | add x y hx hy => simp only [map_add, hx, hy]
  have hcoal :
      deltaA ≫ std =
        ModuleCat.ofHom (((TensorProduct.mk L B L).flip) (1 : L)) := by
    apply ModuleCat.hom_ext
    exact Coalgebra.lTensor_counit_comp_comul
  have hstd : deltaA ≫ std ≫ ridA = 𝟙 (ModuleCat.of L B) := by
    have hcoal' := congrArg (fun z => z ≫ ridA) hcoal
    have hunit :
        ModuleCat.ofHom (((TensorProduct.mk L B L).flip) (1 : L)) ≫ ridA =
          𝟙 (ModuleCat.of L B) := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (1 : L) • (show B from x) = x
      exact one_smul L x
    exact (Category.assoc deltaA std ridA).symm.trans
      (hcoal'.trans hunit)
  have h1 := congrArg (fun z => comulA ≫ z ≫ qR.hom ≫ ridA) hn
  have h2 := congrArg (fun z => z ≫ mapc ≫ qR.hom ≫ ridA) hc
  have h3 := congrArg (fun z => deltaA ≫ z ≫ ridA) hpre
  have hcover : comulA ≫ tm ≫ eR.hom ≫ ridA = 𝟙 DA := by
    change comulA ≫ tm ≫ (cR.hom ≫ qR.hom) ≫ ridA = 𝟙 DA
    exact h1.trans (h2.trans (h3.trans hstd))
  ext i
  cases i
  let ur :=
    (affineCechSelectedTensorRightUnitorIso f hf D).hom.hom PUnit.unit
  have hu : ur = eR.hom ≫ ridA := by
    exact affineCechSelectedTensorRightUnitorIso_cover f hf D
  change comulA ≫ tm ≫ ur = 𝟙 DA
  exact (congrArg (fun z => comulA ≫ tm ≫ z) hu).trans hcover

/-- The finite-Galois D4 coordinate maps form a coalgebra object in the
selected affine Čech tensor structure. -/
noncomputable def relatedTripleCoordinateGaloisSelectedCoalgebraObject
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    let f := CommRingCat.ofHom (algebraMap K L)
    let hf := galoisFieldAlgebraMap_faithfullyFlat K L
    AffineCechSelectedCoalgebraObject f hf := by
  dsimp only
  let f := CommRingCat.ofHom (algebraMap K L)
  let hf := galoisFieldAlgebraMap_faithfullyFlat K L
  let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
  exact
    { obj := D
      comul :=
        relatedTripleCoordinateGaloisSelectedComulDescentMap K L diagram
      counit :=
        relatedTripleCoordinateGaloisSelectedCounitDescentMap K L diagram
      comul_assoc :=
        relatedTripleCoordinateGaloisSelectedComul_coassoc K L diagram
      counit_left :=
        relatedTripleCoordinateGaloisSelectedCounit_left K L diagram
      counit_right :=
        relatedTripleCoordinateGaloisSelectedCounit_right K L diagram }

end

end RiemannResearch.AlgebraicGeometry
