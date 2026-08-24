/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.D4ZornCoordinateGaloisSelectedCoalgebraLaws

/-!
# Selected D4 bialgebra laws in affine Čech descent

This module packages the selected finite-Galois D4 coordinate multiplication
as a commutative algebra object, proves all four compatibility equations
between that algebra object and the selected coalgebra object, and packages
the resulting commutative bialgebra object.

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

private abbrev ASelectedBialgebra := RelatedTripleCoordinateRing.{0}

local instance coordinateGaloisSelectedBialgebraCommRing :
    CommRing ASelectedBialgebra :=
  inferInstance

/-- The finite-Galois D4 coordinate multiplication and unit form a
commutative algebra object in the selected affine Čech tensor structure. -/
noncomputable def relatedTripleCoordinateGaloisSelectedCommAlgebraObject
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    let f := CommRingCat.ofHom (algebraMap K L)
    let hf := galoisFieldAlgebraMap_faithfullyFlat K L
    AffineCechSelectedCommAlgebraObject f hf := by
  dsimp only
  let f := CommRingCat.ofHom (algebraMap K L)
  let hf := galoisFieldAlgebraMap_faithfullyFlat K L
  let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
  exact
    { obj := D
      mul := relatedTripleCoordinateGaloisSelectedMulDescentMap K L diagram
      unit := relatedTripleCoordinateGaloisSelectedUnitDescentMap K L diagram
      mul_assoc := relatedTripleCoordinateGaloisSelectedMul_assoc K L diagram
      unit_mul := relatedTripleCoordinateGaloisSelectedUnit_mul K L diagram
      mul_unit := relatedTripleCoordinateGaloisSelectedMul_unit K L diagram
      mul_comm := relatedTripleCoordinateGaloisSelectedMul_comm K L diagram }

set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 200000 in
-- The cover proof conjugates both selected tensor-unit comparisons.
set_option maxHeartbeats 3000000 in
set_option linter.style.haveILetI false in
/-- The selected coordinate counit sends the selected coordinate unit to the
tensor-unit identity. -/
theorem relatedTripleCoordinateGaloisSelectedCounit_unit
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    let f := CommRingCat.ofHom (algebraMap K L)
    let unit :=
      relatedTripleCoordinateGaloisSelectedUnitDescentMap K L diagram
    let counit :=
      relatedTripleCoordinateGaloisSelectedCounitDescentMap K L diagram
    unit ≫ counit = 𝟙 (affineCechSelectedTensorUnitDescentData f) := by
  dsimp only
  let f := CommRingCat.ofHom (algebraMap K L)
  let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
  let U := affineCechSelectedTensorUnitDescentData f
  let B := RelatedTripleCoordinateScalarExtension L
  let unit :=
    relatedTripleCoordinateGaloisSelectedUnitDescentMap K L diagram
  let counit :=
    relatedTripleCoordinateGaloisSelectedCounitDescentMap K L diagram
  let UA : ModuleCat L := (AffineCechModuleDescentData.evaluation f).obj U
  let DA : ModuleCat L := (AffineCechModuleDescentData.evaluation f).obj D
  let eU : UA ≅ ModuleCat.of L L :=
    affineCechSelectedTensorUnitCoverIso f
  let unitA : UA ⟶ DA := unit.hom PUnit.unit
  let counitA : DA ⟶ UA := counit.hom PUnit.unit
  let etaA : ModuleCat.of L L ⟶ ModuleCat.of L B :=
    ModuleCat.ofHom (Algebra.linearMap L B)
  let epsA : ModuleCat.of L B ⟶ ModuleCat.of L L :=
    ModuleCat.ofHom (CoalgebraStruct.counit : B →ₗ[L] L)
  have hu : eU.inv ≫ unitA = etaA := by
    exact relatedTripleCoordinateGaloisSelectedUnitDescentMap_cover K L diagram
  have he : counitA ≫ eU.hom = epsA := by
    exact relatedTripleCoordinateGaloisSelectedCounitDescentMap_cover K L diagram
  have hstd : etaA ≫ epsA = 𝟙 (ModuleCat.of L L) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change CoalgebraStruct.counit (algebraMap L B x) = x
    calc
      CoalgebraStruct.counit (algebraMap L B x) =
          CoalgebraStruct.counit (x • (1 : B)) := by
        congr 1
        exact ((Algebra.smul_def x (1 : B)).trans (mul_one _)).symm
      _ = x • CoalgebraStruct.counit (1 : B) :=
        LinearMap.map_smul_of_tower _ _ _
      _ = x := by rw [Bialgebra.counit_one]; simp
  have h1 := congrArg (fun z => z ≫ counitA ≫ eU.hom) hu
  have h2 := congrArg (fun z => etaA ≫ z) he
  have hconj :
      eU.inv ≫ unitA ≫ counitA ≫ eU.hom =
        𝟙 (ModuleCat.of L L) := by
    exact h1.trans (h2.trans hstd)
  have hcover : unitA ≫ counitA = 𝟙 UA := by
    letI : IsIso eU.inv := eU.isIso_inv
    letI : Epi eU.inv := IsIso.epi_of_iso eU.inv
    apply (cancel_epi eU.inv).mp
    letI : IsIso eU.hom := eU.isIso_hom
    letI : Mono eU.hom := IsIso.mono_of_iso eU.hom
    apply (cancel_mono eU.hom).mp
    simpa only [Category.assoc, Category.comp_id, eU.inv_hom_id]
      using hconj
  ext i
  cases i
  change unitA ≫ counitA = 𝟙 UA
  exact hcover

set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 200000 in
-- The cover calculation unfolds two nested selected tensor comparisons.
set_option maxHeartbeats 3000000 in
set_option linter.style.haveILetI false in
/-- On the selected tensor square of the tensor unit, the selected right
unitor becomes the ordinary right unitor after applying both tensor-unit cover
comparisons. -/
theorem relatedTripleCoordinateGaloisSelectedTensorUnitRightUnitor_cover
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    let f := CommRingCat.ofHom (algebraMap K L)
    let hf := galoisFieldAlgebraMap_faithfullyFlat K L
    let U := affineCechSelectedTensorUnitDescentData f
    let UU := affineCechSelectedTensorDescentData f hf U U
    let UA : ModuleCat L := (AffineCechModuleDescentData.evaluation f).obj U
    let UUA : ModuleCat L := (AffineCechModuleDescentData.evaluation f).obj UU
    let eU : UA ≅ ModuleCat.of L L := affineCechSelectedTensorUnitCoverIso f
    let eUU : UUA ≅ ModuleCat.of L (TensorProduct L UA UA) :=
      affineCechSelectedTensorDescentDataCoverIso f hf U U
    let qUU :=
      (TensorProduct.congr eU.toLinearEquiv eU.toLinearEquiv).toModuleIso
    let rL := (TensorProduct.rid L (ModuleCat.of L L)).toModuleIso
    let rU : UUA ⟶ UA :=
      (affineCechSelectedTensorRightUnitorIso f hf U).hom.hom PUnit.unit
    eUU.hom ≫ qUU.hom ≫ rL.hom = rU ≫ eU.hom := by
  dsimp only
  let f := CommRingCat.ofHom (algebraMap K L)
  let hf := galoisFieldAlgebraMap_faithfullyFlat K L
  let U := affineCechSelectedTensorUnitDescentData f
  let UU := affineCechSelectedTensorDescentData f hf U U
  let UA : ModuleCat L := (AffineCechModuleDescentData.evaluation f).obj U
  let UUA : ModuleCat L := (AffineCechModuleDescentData.evaluation f).obj UU
  let eU : UA ≅ ModuleCat.of L L := affineCechSelectedTensorUnitCoverIso f
  let eUU : UUA ≅ ModuleCat.of L (TensorProduct L UA UA) :=
    affineCechSelectedTensorDescentDataCoverIso f hf U U
  let qUU :=
    (TensorProduct.congr eU.toLinearEquiv eU.toLinearEquiv).toModuleIso
  let qR := (TensorProduct.congr (LinearEquiv.refl L UA)
    eU.toLinearEquiv).toModuleIso
  let rL := (TensorProduct.rid L (ModuleCat.of L L)).toModuleIso
  let rU : UUA ⟶ UA :=
    (affineCechSelectedTensorRightUnitorIso f hf U).hom.hom PUnit.unit
  let eR : UUA ≅ ModuleCat.of L (TensorProduct L UA (ModuleCat.of L L)) :=
    affineCechSelectedTensorRightUnitorCoverIso f hf U
  change eUU.hom ≫ qUU.hom ≫ rL.hom = rU ≫ eU.hom
  have hr0 := affineCechSelectedTensorRightUnitorIso_cover f hf U
  change rU = eR.hom ≫ _ at hr0
  have heR : eUU.inv ≫ eR.hom = qR.hom := by
    dsimp only [eR, affineCechSelectedTensorRightUnitorCoverIso]
    change eUU.inv ≫ (eUU.hom ≫ qR.hom) = qR.hom
    exact eUU.inv_hom_id_assoc qR.hom
  rw [hr0]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rw [← eUU.hom_inv_id_apply z]
  generalize eUU.hom z = w
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
        eUU.inv_hom_id_apply]
      have heRxy := congrArg
        (fun q => ModuleCat.Hom.hom q (x ⊗ₜ[L] y)) heR
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at heRxy
      rw [heRxy]
      change
        (TensorProduct.rid L L)
            ((TensorProduct.congr eU.toLinearEquiv eU.toLinearEquiv)
              (x ⊗ₜ[L] y)) =
          eU.hom
            ((TensorProduct.rid L UA)
              ((TensorProduct.congr (LinearEquiv.refl L UA)
                eU.toLinearEquiv) (x ⊗ₜ[L] y)))
      rw [TensorProduct.congr_tmul, TensorProduct.rid_tmul,
        TensorProduct.congr_tmul, TensorProduct.rid_tmul]
      change eU.hom y • eU.hom x = eU.hom (eU.hom y • x)
      exact ((ModuleCat.Hom.hom eU.hom).map_smul (eU.hom y) x).symm
  | add x y hx hy => simp only [map_add, hx, hy]

set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 200000 in
-- The proof combines tensor induction with nested cover conjugation.
set_option maxHeartbeats 3000000 in
set_option linter.style.haveILetI false in
/-- The selected coordinate counit preserves selected coordinate
multiplication. -/
theorem relatedTripleCoordinateGaloisSelectedCounit_mul
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    let f := CommRingCat.ofHom (algebraMap K L)
    let hf := galoisFieldAlgebraMap_faithfullyFlat K L
    let mul := relatedTripleCoordinateGaloisSelectedMulDescentMap K L diagram
    let counit :=
      relatedTripleCoordinateGaloisSelectedCounitDescentMap K L diagram
    mul ≫ counit =
      affineCechSelectedTensorMap f hf counit counit ≫
        (affineCechSelectedTensorRightUnitorIso f hf
          (affineCechSelectedTensorUnitDescentData f)).hom := by
  dsimp only
  let f := CommRingCat.ofHom (algebraMap K L)
  let hf := galoisFieldAlgebraMap_faithfullyFlat K L
  let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
  let U := affineCechSelectedTensorUnitDescentData f
  let T := affineCechSelectedTensorDescentData f hf D D
  let UU := affineCechSelectedTensorDescentData f hf U U
  let B := RelatedTripleCoordinateScalarExtension L
  let mul := relatedTripleCoordinateGaloisSelectedMulDescentMap K L diagram
  let counit :=
    relatedTripleCoordinateGaloisSelectedCounitDescentMap K L diagram
  let UA : ModuleCat L := (AffineCechModuleDescentData.evaluation f).obj U
  let DA : ModuleCat L := ModuleCat.of L B
  let TA : ModuleCat L := (AffineCechModuleDescentData.evaluation f).obj T
  let UUA : ModuleCat L := (AffineCechModuleDescentData.evaluation f).obj UU
  let eU : UA ≅ ModuleCat.of L L := affineCechSelectedTensorUnitCoverIso f
  let eT : TA ≅ ModuleCat.of L (TensorProduct L DA DA) :=
    affineCechSelectedTensorDescentDataCoverIso f hf D D
  let eUU : UUA ≅ ModuleCat.of L (TensorProduct L UA UA) :=
    affineCechSelectedTensorDescentDataCoverIso f hf U U
  let qUU :=
    (TensorProduct.congr eU.toLinearEquiv eU.toLinearEquiv).toModuleIso
  let mulA : TA ⟶ DA := mul.hom PUnit.unit
  let counitA : DA ⟶ UA := counit.hom PUnit.unit
  let muA : ModuleCat.of L (TensorProduct L DA DA) ⟶ DA :=
    ModuleCat.ofHom (galoisAlgebraMultiplicationLinearMap L B)
  let epsA : DA ⟶ ModuleCat.of L L :=
    ModuleCat.ofHom (CoalgebraStruct.counit : B →ₗ[L] L)
  let tm : TA ⟶ UUA :=
    (affineCechSelectedTensorMap f hf counit counit).hom PUnit.unit
  let mapm : ModuleCat.of L (TensorProduct L DA DA) ⟶
      ModuleCat.of L (TensorProduct L UA UA) :=
    ModuleCat.ofHom
      (TensorProduct.map
        (ModuleCat.Hom.hom
          ((AffineCechModuleDescentData.evaluation f).map counit))
        (ModuleCat.Hom.hom
          ((AffineCechModuleDescentData.evaluation f).map counit)))
  let rL := (TensorProduct.rid L (ModuleCat.of L L)).toModuleIso
  let rU : UUA ⟶ UA :=
    (affineCechSelectedTensorRightUnitorIso f hf U).hom.hom PUnit.unit
  have hm : eT.inv ≫ mulA = muA :=
    relatedTripleCoordinateGaloisSelectedMulDescentMap_cover K L diagram
  have he : counitA ≫ eU.hom = epsA :=
    relatedTripleCoordinateGaloisSelectedCounitDescentMap_cover K L diagram
  have hn : tm ≫ eUU.hom = eT.hom ≫ mapm :=
    affineCechSelectedTensorDescentDataCoverIso_natural
      f hf counit counit
  have hstd : muA ≫ epsA = mapm ≫ qUU.hom ≫ rL.hom := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
        change
          CoalgebraStruct.counit ((show B from x) * (show B from y)) =
            (TensorProduct.rid L L)
              ((TensorProduct.congr eU.toLinearEquiv eU.toLinearEquiv)
                (counitA x ⊗ₜ[L] counitA y))
        rw [TensorProduct.congr_tmul, TensorProduct.rid_tmul]
        change
          CoalgebraStruct.counit ((show B from x) * (show B from y)) =
            eU.hom (counitA y) * eU.hom (counitA x)
        have hex := congrArg (fun q => ModuleCat.Hom.hom q x) he
        have hey := congrArg (fun q => ModuleCat.Hom.hom q y) he
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hex hey
        rw [hex, hey]
        exact
          (LinearMap.congr_fun
            (LinearMap.congr_fun
              (Bialgebra.mul_compr₂_counit (R := L) (A := B)) x) y).trans
            (mul_comm _ _)
    | add x y hx hy => simp only [map_add, hx, hy]
  have hunit : eUU.hom ≫ qUU.hom ≫ rL.hom = rU ≫ eU.hom :=
    relatedTripleCoordinateGaloisSelectedTensorUnitRightUnitor_cover K L
  have hcover :
      eT.inv ≫ mulA ≫ counitA ≫ eU.hom =
        eT.inv ≫ tm ≫ rU ≫ eU.hom := by
    calc
      eT.inv ≫ mulA ≫ counitA ≫ eU.hom =
          (eT.inv ≫ mulA) ≫ (counitA ≫ eU.hom) := by
            simp only [Category.assoc]
      _ = muA ≫ epsA := by rw [hm, he]
      _ = mapm ≫ qUU.hom ≫ rL.hom := hstd
      _ = eT.inv ≫ tm ≫ eUU.hom ≫ qUU.hom ≫ rL.hom := by
        symm
        calc
          eT.inv ≫ tm ≫ eUU.hom ≫ qUU.hom ≫ rL.hom =
              eT.inv ≫ (tm ≫ eUU.hom) ≫ qUU.hom ≫ rL.hom := by
                simp only [Category.assoc]
          _ = eT.inv ≫ (eT.hom ≫ mapm) ≫ qUU.hom ≫ rL.hom := by
                rw [hn]
          _ = mapm ≫ qUU.hom ≫ rL.hom := by
                simp only [Category.assoc, eT.inv_hom_id_assoc]
      _ = eT.inv ≫ tm ≫ rU ≫ eU.hom := by
        simpa only [Category.assoc] using
          congrArg (fun z => eT.inv ≫ tm ≫ z) hunit
  ext i
  cases i
  change mulA ≫ counitA = tm ≫ rU
  letI : IsIso eT.inv := eT.isIso_inv
  letI : Epi eT.inv := IsIso.epi_of_iso eT.inv
  apply (cancel_epi eT.inv).mp
  letI : IsIso eU.hom := eU.isIso_hom
  letI : Mono eU.hom := IsIso.mono_of_iso eU.hom
  apply (cancel_mono eU.hom).mp
  simpa only [Category.assoc] using hcover

set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 200000 in
-- The proof uses inverse unitor transport and nested cover comparisons.
set_option maxHeartbeats 3000000 in
set_option linter.style.haveILetI false in
/-- The selected coordinate comultiplication sends the selected coordinate
unit to the tensor square of that unit. -/
theorem relatedTripleCoordinateGaloisSelectedComul_unit
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    let f := CommRingCat.ofHom (algebraMap K L)
    let hf := galoisFieldAlgebraMap_faithfullyFlat K L
    let unit := relatedTripleCoordinateGaloisSelectedUnitDescentMap K L diagram
    let comul := relatedTripleCoordinateGaloisSelectedComulDescentMap K L diagram
    unit ≫ comul =
      (affineCechSelectedTensorRightUnitorIso f hf
        (affineCechSelectedTensorUnitDescentData f)).inv ≫
          affineCechSelectedTensorMap f hf unit unit := by
  dsimp only
  let f := CommRingCat.ofHom (algebraMap K L)
  let hf := galoisFieldAlgebraMap_faithfullyFlat K L
  let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
  let U := affineCechSelectedTensorUnitDescentData f
  let T := affineCechSelectedTensorDescentData f hf D D
  let UU := affineCechSelectedTensorDescentData f hf U U
  let B := RelatedTripleCoordinateScalarExtension L
  let unit := relatedTripleCoordinateGaloisSelectedUnitDescentMap K L diagram
  let comul := relatedTripleCoordinateGaloisSelectedComulDescentMap K L diagram
  let UA : ModuleCat L := (AffineCechModuleDescentData.evaluation f).obj U
  let DA : ModuleCat L := ModuleCat.of L B
  let TA : ModuleCat L := (AffineCechModuleDescentData.evaluation f).obj T
  let UUA : ModuleCat L := (AffineCechModuleDescentData.evaluation f).obj UU
  let eU : UA ≅ ModuleCat.of L L := affineCechSelectedTensorUnitCoverIso f
  let eT : TA ≅ ModuleCat.of L (TensorProduct L DA DA) :=
    affineCechSelectedTensorDescentDataCoverIso f hf D D
  let eUU : UUA ≅ ModuleCat.of L (TensorProduct L UA UA) :=
    affineCechSelectedTensorDescentDataCoverIso f hf U U
  let qUU :=
    (TensorProduct.congr eU.toLinearEquiv eU.toLinearEquiv).toModuleIso
  let rL := (TensorProduct.rid L (ModuleCat.of L L)).toModuleIso
  let rU := affineCechSelectedTensorRightUnitorIso f hf U
  let rUhomA : UUA ⟶ UA := rU.hom.hom PUnit.unit
  let rUinvA : UA ⟶ UUA := rU.inv.hom PUnit.unit
  let unitA : UA ⟶ DA := unit.hom PUnit.unit
  let comulA : DA ⟶ TA := comul.hom PUnit.unit
  let etaA : ModuleCat.of L L ⟶ DA :=
    ModuleCat.ofHom (Algebra.linearMap L B)
  let deltaA : DA ⟶ ModuleCat.of L (TensorProduct L DA DA) :=
    ModuleCat.ofHom
      (CoalgebraStruct.comul : B →ₗ[L] TensorProduct L B B)
  let tm : UUA ⟶ TA :=
    (affineCechSelectedTensorMap f hf unit unit).hom PUnit.unit
  let mapm : ModuleCat.of L (TensorProduct L UA UA) ⟶
      ModuleCat.of L (TensorProduct L DA DA) :=
    ModuleCat.ofHom
      (TensorProduct.map
        (ModuleCat.Hom.hom
          ((AffineCechModuleDescentData.evaluation f).map unit))
        (ModuleCat.Hom.hom
          ((AffineCechModuleDescentData.evaluation f).map unit)))
  have hu : eU.inv ≫ unitA = etaA :=
    relatedTripleCoordinateGaloisSelectedUnitDescentMap_cover K L diagram
  have hc : comulA ≫ eT.hom = deltaA :=
    relatedTripleCoordinateGaloisSelectedComulDescentMap_cover K L diagram
  have hn : tm ≫ eT.hom = eUU.hom ≫ mapm :=
    affineCechSelectedTensorDescentDataCoverIso_natural f hf unit unit
  have hunit :
      eUU.hom ≫ qUU.hom ≫ rL.hom = rUhomA ≫ eU.hom :=
    relatedTripleCoordinateGaloisSelectedTensorUnitRightUnitor_cover K L
  have hri : rUinvA ≫ rUhomA = 𝟙 UA := by
    have h := congrArg (fun q => q.hom PUnit.unit) rU.inv_hom_id
    change rUinvA ≫ rUhomA = 𝟙 UA at h
    exact h
  have hunitInv :
      eU.inv ≫ rUinvA ≫ eUU.hom = rL.inv ≫ qUU.inv := by
    letI : IsIso qUU.hom := qUU.isIso_hom
    letI : Mono qUU.hom := IsIso.mono_of_iso qUU.hom
    letI : IsIso rL.hom := rL.isIso_hom
    letI : Mono rL.hom := IsIso.mono_of_iso rL.hom
    apply (cancel_mono (qUU.hom ≫ rL.hom)).mp
    calc
      eU.inv ≫ rUinvA ≫ eUU.hom ≫ qUU.hom ≫ rL.hom =
          eU.inv ≫ rUinvA ≫ (eUU.hom ≫ qUU.hom ≫ rL.hom) := by
            rfl
      _ = eU.inv ≫ rUinvA ≫ rUhomA ≫ eU.hom := by rw [hunit]
      _ = eU.inv ≫ (rUinvA ≫ rUhomA) ≫ eU.hom := by
            simp only [Category.assoc]
      _ = 𝟙 (ModuleCat.of L L) := by
            rw [hri]
            simp only [Category.id_comp, eU.inv_hom_id]
      _ = rL.inv ≫ qUU.inv ≫ qUU.hom ≫ rL.hom := by
            simp only [qUU.inv_hom_id_assoc, rL.inv_hom_id]
  have hstd : etaA ≫ deltaA = rL.inv ≫ qUU.inv ≫ mapm := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    have hr :
        rL.inv x = (x : L) ⊗ₜ[L] (1 : L) := by
      apply rL.toLinearEquiv.injective
      change rL.toLinearEquiv (rL.toLinearEquiv.symm x) =
        rL.toLinearEquiv (x ⊗ₜ[L] (1 : L))
      rw [rL.toLinearEquiv.apply_symm_apply]
      change x = (1 : L) • x
      rw [one_smul]
    rw [hr]
    change
      CoalgebraStruct.comul (algebraMap L B x) =
        (TensorProduct.map
          (ModuleCat.Hom.hom unitA) (ModuleCat.Hom.hom unitA))
          ((TensorProduct.congr eU.symm.toLinearEquiv
            eU.symm.toLinearEquiv) (x ⊗ₜ[L] (1 : L)))
    rw [TensorProduct.congr_tmul, TensorProduct.map_tmul]
    change
      CoalgebraStruct.comul (algebraMap L B x) =
        unitA (eU.inv x) ⊗ₜ[L] unitA (eU.inv (1 : L))
    have hux := congrArg (fun q => ModuleCat.Hom.hom q x) hu
    have hu1 := congrArg (fun q => ModuleCat.Hom.hom q (1 : L)) hu
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hux hu1
    rw [hux, hu1]
    change
      CoalgebraStruct.comul (algebraMap L B x) =
        algebraMap L B x ⊗ₜ[L] algebraMap L B 1
    rw [map_one]
    calc
      CoalgebraStruct.comul (algebraMap L B x) =
          CoalgebraStruct.comul (x • (1 : B)) := by
            congr 1
            exact ((Algebra.smul_def x (1 : B)).trans (mul_one _)).symm
      _ = x • CoalgebraStruct.comul (1 : B) :=
        LinearMap.map_smul_of_tower _ _ _
      _ = x • (1 : TensorProduct L B B) := by
        rw [Bialgebra.comul_one]
      _ = algebraMap L B x ⊗ₜ[L] (1 : B) := by
        rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul',
          Algebra.smul_def, mul_one]
  have hcover :
      eU.inv ≫ unitA ≫ comulA ≫ eT.hom =
        eU.inv ≫ rUinvA ≫ tm ≫ eT.hom := by
    calc
      eU.inv ≫ unitA ≫ comulA ≫ eT.hom =
          (eU.inv ≫ unitA) ≫ (comulA ≫ eT.hom) := by
            simp only [Category.assoc]
      _ = etaA ≫ deltaA := by rw [hu, hc]
      _ = rL.inv ≫ qUU.inv ≫ mapm := hstd
      _ = eU.inv ≫ rUinvA ≫ eUU.hom ≫ mapm := by
        simpa only [Category.assoc] using
          congrArg (fun z => z ≫ mapm) hunitInv.symm
      _ = eU.inv ≫ rUinvA ≫ tm ≫ eT.hom := by
        symm
        simpa only [Category.assoc] using
          congrArg (fun z => eU.inv ≫ rUinvA ≫ z) hn
  ext i
  cases i
  change unitA ≫ comulA = rUinvA ≫ tm
  letI : IsIso eU.inv := eU.isIso_inv
  letI : Epi eU.inv := IsIso.epi_of_iso eU.inv
  apply (cancel_epi eU.inv).mp
  letI : IsIso eT.hom := eT.isIso_hom
  letI : Mono eT.hom := IsIso.mono_of_iso eT.hom
  apply (cancel_mono eT.hom).mp
  simpa only [Category.assoc] using hcover

set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 200000 in
-- The proof conjugates the selected middle-four interchange on the cover.
set_option maxHeartbeats 3000000 in
set_option linter.style.haveILetI false in
/-- The selected coordinate comultiplication preserves selected coordinate
multiplication. -/
theorem relatedTripleCoordinateGaloisSelectedComul_mul
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    let f := CommRingCat.ofHom (algebraMap K L)
    let hf := galoisFieldAlgebraMap_faithfullyFlat K L
    let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
    let mul := relatedTripleCoordinateGaloisSelectedMulDescentMap K L diagram
    let comul := relatedTripleCoordinateGaloisSelectedComulDescentMap K L diagram
    mul ≫ comul =
      affineCechSelectedTensorMap f hf comul comul ≫
        (affineCechSelectedMiddleFourIso f hf D D D D).hom ≫
        affineCechSelectedTensorMap f hf mul mul := by
  dsimp only
  let f := CommRingCat.ofHom (algebraMap K L)
  let hf := galoisFieldAlgebraMap_faithfullyFlat K L
  let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
  let T := affineCechSelectedTensorDescentData f hf D D
  let TT := affineCechSelectedTensorDescentData f hf T T
  let B := RelatedTripleCoordinateScalarExtension L
  let mul := relatedTripleCoordinateGaloisSelectedMulDescentMap K L diagram
  let comul := relatedTripleCoordinateGaloisSelectedComulDescentMap K L diagram
  let DA : ModuleCat L := ModuleCat.of L B
  let TA : ModuleCat L := (AffineCechModuleDescentData.evaluation f).obj T
  let TTA : ModuleCat L := (AffineCechModuleDescentData.evaluation f).obj TT
  let eT : TA ≅ ModuleCat.of L (TensorProduct L DA DA) :=
    affineCechSelectedTensorDescentDataCoverIso f hf D D
  let eTT : TTA ≅ ModuleCat.of L (TensorProduct L TA TA) :=
    affineCechSelectedTensorDescentDataCoverIso f hf T T
  let qTT :=
    (TensorProduct.congr eT.toLinearEquiv eT.toLinearEquiv).toModuleIso
  let middle := tensorProductMiddleFourIso (CommRingCat.of L) DA DA DA DA
  let mulA : TA ⟶ DA := mul.hom PUnit.unit
  let comulA : DA ⟶ TA := comul.hom PUnit.unit
  let muA : ModuleCat.of L (TensorProduct L DA DA) ⟶ DA :=
    ModuleCat.ofHom (galoisAlgebraMultiplicationLinearMap L B)
  let deltaA : DA ⟶ ModuleCat.of L (TensorProduct L DA DA) :=
    ModuleCat.ofHom
      (CoalgebraStruct.comul : B →ₗ[L] TensorProduct L B B)
  let tmc : TA ⟶ TTA :=
    (affineCechSelectedTensorMap f hf comul comul).hom PUnit.unit
  let tmm : TTA ⟶ TA :=
    (affineCechSelectedTensorMap f hf mul mul).hom PUnit.unit
  let middleA : TTA ⟶ TTA :=
    (affineCechSelectedMiddleFourIso f hf D D D D).hom.hom PUnit.unit
  let mapc : ModuleCat.of L (TensorProduct L DA DA) ⟶
      ModuleCat.of L (TensorProduct L TA TA) :=
    ModuleCat.ofHom
      (TensorProduct.map
        (ModuleCat.Hom.hom
          ((AffineCechModuleDescentData.evaluation f).map comul))
        (ModuleCat.Hom.hom
          ((AffineCechModuleDescentData.evaluation f).map comul)))
  let mapm : ModuleCat.of L (TensorProduct L TA TA) ⟶
      ModuleCat.of L (TensorProduct L DA DA) :=
    ModuleCat.ofHom
      (TensorProduct.map
        (ModuleCat.Hom.hom
          ((AffineCechModuleDescentData.evaluation f).map mul))
        (ModuleCat.Hom.hom
          ((AffineCechModuleDescentData.evaluation f).map mul)))
  let stdc : ModuleCat.of L (TensorProduct L DA DA) ⟶
      ModuleCat.of L
        (TensorProduct L (TensorProduct L DA DA) (TensorProduct L DA DA)) :=
    ModuleCat.ofHom
      (TensorProduct.map
        (CoalgebraStruct.comul : B →ₗ[L] TensorProduct L B B)
        (CoalgebraStruct.comul : B →ₗ[L] TensorProduct L B B))
  let stdm : ModuleCat.of L
        (TensorProduct L (TensorProduct L DA DA) (TensorProduct L DA DA)) ⟶
      ModuleCat.of L (TensorProduct L DA DA) :=
    ModuleCat.ofHom
      (TensorProduct.map
        (galoisAlgebraMultiplicationLinearMap L B)
        (galoisAlgebraMultiplicationLinearMap L B))
  have hm : eT.inv ≫ mulA = muA :=
    relatedTripleCoordinateGaloisSelectedMulDescentMap_cover K L diagram
  have hc : comulA ≫ eT.hom = deltaA :=
    relatedTripleCoordinateGaloisSelectedComulDescentMap_cover K L diagram
  have hnc : tmc ≫ eTT.hom = eT.hom ≫ mapc :=
    affineCechSelectedTensorDescentDataCoverIso_natural f hf comul comul
  have hnm : tmm ≫ eT.hom = eTT.hom ≫ mapm :=
    affineCechSelectedTensorDescentDataCoverIso_natural f hf mul mul
  have hmiddle :
      middleA ≫ eTT.hom ≫ qTT.hom =
        eTT.hom ≫ qTT.hom ≫ middle.hom := by
    have h := affineCechSelectedMiddleFourIso_cover f hf D D D D
    change middleA ≫ (eTT.hom ≫ qTT.hom) =
      (eTT.hom ≫ qTT.hom) ≫ middle.hom at h
    simpa only [Category.assoc] using h
  have htc : eT.inv ≫ tmc ≫ eTT.hom = mapc := by
    have h := congrArg (fun z => eT.inv ≫ z) hnc
    simpa only [Category.assoc, eT.inv_hom_id_assoc] using h
  have htm : eTT.inv ≫ tmm ≫ eT.hom = mapm := by
    have h := congrArg (fun z => eTT.inv ≫ z) hnm
    simpa only [Category.assoc, eTT.inv_hom_id_assoc] using h
  have hmid :
      eTT.inv ≫ middleA ≫ eTT.hom =
        qTT.hom ≫ middle.hom ≫ qTT.inv := by
    have h := congrArg (fun z => eTT.inv ≫ z ≫ qTT.inv) hmiddle
    simpa only [Category.assoc, eTT.inv_hom_id_assoc,
      qTT.hom_inv_id, Category.comp_id] using h
  have hpre : mapc ≫ qTT.hom = stdc := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
        change
          eT.hom (comulA x) ⊗ₜ[L] eT.hom (comulA y) =
            ModuleCat.Hom.hom deltaA x ⊗ₜ[L]
              ModuleCat.Hom.hom deltaA y
        have hx := congrArg (fun q => ModuleCat.Hom.hom q x) hc
        have hy := congrArg (fun q => ModuleCat.Hom.hom q y) hc
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hx hy
        rw [hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hpost : qTT.inv ≫ mapm = stdm := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
        change
          ModuleCat.Hom.hom (eT.inv ≫ mulA) x ⊗ₜ[L]
              ModuleCat.Hom.hom (eT.inv ≫ mulA) y =
            ModuleCat.Hom.hom muA x ⊗ₜ[L] ModuleCat.Hom.hom muA y
        rw [hm]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hstd : muA ≫ deltaA = stdc ≫ middle.hom ≫ stdm := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
        change
          CoalgebraStruct.comul ((show B from x) * (show B from y)) =
            (TensorProduct.map
              (galoisAlgebraMultiplicationLinearMap L B)
              (galoisAlgebraMultiplicationLinearMap L B))
              ((tensorProductMiddleFourIso (CommRingCat.of L) DA DA DA DA).hom
                ((CoalgebraStruct.comul :
                    B →ₗ[L] TensorProduct L B B) (show B from x) ⊗ₜ[L]
                  (CoalgebraStruct.comul :
                    B →ₗ[L] TensorProduct L B B) (show B from y)))
        rw [Bialgebra.comul_mul]
        generalize (CoalgebraStruct.comul :
          B →ₗ[L] TensorProduct L B B) (show B from x) = w
        generalize (CoalgebraStruct.comul :
          B →ₗ[L] TensorProduct L B B) (show B from y) = v
        induction w using TensorProduct.induction_on with
        | zero => simp only [TensorProduct.zero_tmul, map_zero, zero_mul]
        | tmul a b =>
            induction v using TensorProduct.induction_on with
            | zero => simp only [TensorProduct.tmul_zero, map_zero, mul_zero]
            | tmul c d =>
                rw [tensorProductMiddleFourIso_hom_tmul,
                  TensorProduct.map_tmul,
                  Algebra.TensorProduct.tmul_mul_tmul]
                change (a * c) ⊗ₜ[L] (b * d) =
                  (a * c) ⊗ₜ[L] (b * d)
                rfl
            | add v₁ v₂ hv₁ hv₂ =>
                simp only [TensorProduct.tmul_add, map_add, mul_add, hv₁, hv₂]
        | add w₁ w₂ hw₁ hw₂ =>
            simp only [TensorProduct.add_tmul, map_add, add_mul, hw₁, hw₂]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hcover :
      eT.inv ≫ mulA ≫ comulA ≫ eT.hom =
        eT.inv ≫ tmc ≫ middleA ≫ tmm ≫ eT.hom := by
    calc
      eT.inv ≫ mulA ≫ comulA ≫ eT.hom =
          (eT.inv ≫ mulA) ≫ (comulA ≫ eT.hom) := by
            simp only [Category.assoc]
      _ = muA ≫ deltaA := by rw [hm, hc]
      _ = stdc ≫ middle.hom ≫ stdm := hstd
      _ = mapc ≫ qTT.hom ≫ middle.hom ≫ qTT.inv ≫ mapm := by
        rw [← hpre, ← hpost]
        simp only [Category.assoc]
      _ = (eT.inv ≫ tmc ≫ eTT.hom) ≫
          (eTT.inv ≫ middleA ≫ eTT.hom) ≫
          (eTT.inv ≫ tmm ≫ eT.hom) := by
        rw [htc, hmid, htm]
        simp only [Category.assoc]
      _ = eT.inv ≫ tmc ≫ middleA ≫ tmm ≫ eT.hom := by
        simp only [Category.assoc, eTT.hom_inv_id_assoc]
  ext i
  cases i
  change mulA ≫ comulA = tmc ≫ middleA ≫ tmm
  letI : IsIso eT.inv := eT.isIso_inv
  letI : Epi eT.inv := IsIso.epi_of_iso eT.inv
  apply (cancel_epi eT.inv).mp
  letI : IsIso eT.hom := eT.isIso_hom
  letI : Mono eT.hom := IsIso.mono_of_iso eT.hom
  apply (cancel_mono eT.hom).mp
  simpa only [Category.assoc] using hcover

/-- The finite-Galois D4 coordinate maps form a commutative bialgebra
object in the selected affine Čech tensor structure. -/
noncomputable def relatedTripleCoordinateGaloisSelectedCommBialgebraObject
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    let f := CommRingCat.ofHom (algebraMap K L)
    let hf := galoisFieldAlgebraMap_faithfullyFlat K L
    AffineCechSelectedCommBialgebraObject f hf := by
  dsimp only
  let f := CommRingCat.ofHom (algebraMap K L)
  let hf := galoisFieldAlgebraMap_faithfullyFlat K L
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
      mul_comm := relatedTripleCoordinateGaloisSelectedMul_comm K L diagram }

end

end RiemannResearch.AlgebraicGeometry
