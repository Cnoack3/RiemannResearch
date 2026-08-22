/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.D4ZornCoordinateGaloisSelectedTensorComparison

/-!
# Selected D4 Hopf-map assembly in affine Čech descent

This module identifies the finite-Galois tensor-unit and tensor-square Čech
isomorphisms with the cover comparisons selected by effective affine Čech
module descent. It then conjugates multiplication, unit, comultiplication,
counit, and antipode into the selected tensor structure and proves that all
five maps recover the canonical coordinate Hopf operations on the cover.

The selected Hopf-object equations remain the next assembly step.

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

local instance coordinateGaloisSelectedHopfAssemblyCommRing : CommRing ASelected :=
  inferInstance

set_option maxHeartbeats 1000000 in
-- Tensor induction unfolds the bridge-defined unit comparison.
set_option linter.style.haveILetI false in
/-- The finite-Galois tensor-unit Čech isomorphism is exactly the cover
comparison selected by effective affine Čech descent. -/
theorem relatedTripleCoordinateGaloisSelectedTensorUnitCechIso_cover
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    let f := CommRingCat.ofHom (algebraMap K L)
    (relatedTripleCoordinateGaloisSelectedTensorUnitCechIso K L).hom.hom
        PUnit.unit =
      (affineCechSelectedTensorUnitCoverIso f).hom := by
  dsimp only
  let f := CommRingCat.ofHom (algebraMap K L)
  let e := relatedTripleCoordinateGaloisSelectedTensorUnitCechIso K L
  let c := affineCechSelectedTensorUnitCoverIso f
  let LK := (ModuleCat.restrictScalars (algebraMap K L)).obj
    (ModuleCat.of L L)
  letI : Module K LK := LK.isModule
  letI : IsScalarTower K L LK :=
    IsScalarTower.of_algebraMap_smul (by intro k x; rfl)
  let T := TensorProduct K LK K
  let lhs : T →ₗ[L] L := ModuleCat.Hom.hom (e.hom.hom PUnit.unit)
  let rhs : T →ₗ[L] L := ModuleCat.Hom.hom c.hom
  have heRaw : e.hom.hom PUnit.unit =
      ModuleCat.ofHom
        (relatedTripleCoordinateGaloisComparisonTensorUnitLinearEquiv
          K L).toLinearMap := by
    rfl
  have hlhs : lhs =
      (relatedTripleCoordinateGaloisComparisonTensorUnitLinearEquiv
        K L).toLinearMap := by
    exact congrArg ModuleCat.Hom.hom heRaw
  apply ModuleCat.hom_ext
  change lhs = rhs
  rw [hlhs]
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul l k =>
      change L at l
      have hrhs : rhs (l ⊗ₜ[K] k) = algebraMap K L k * l := by
        rfl
      change
        relatedTripleCoordinateGaloisComparisonTensorUnitLinearEquiv K L
            ((relatedTripleCoordinateGaloisScalarRestrictLinearEquiv
              K L l) ⊗ₜ[K] k) =
          rhs (l ⊗ₜ[K] k)
      rw [relatedTripleCoordinateGaloisComparisonTensorUnitLinearEquiv_tmul,
        hrhs]
      exact mul_comm _ _
  | add x y hx hy => simp only [map_add, hx, hy]

set_option maxHeartbeats 1200000 in
-- Nested tensor induction unfolds both bridge-defined factor comparisons.
set_option linter.style.haveILetI false in
/-- The finite-Galois tensor-square Čech isomorphism is exactly the cover
comparison selected by effective affine Čech descent. -/
theorem relatedTripleCoordinateGaloisSelectedTensorSquareCechIso_cover
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    let f := CommRingCat.ofHom (algebraMap K L)
    let hf := galoisFieldAlgebraMap_faithfullyFlat K L
    let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
    (relatedTripleCoordinateGaloisSelectedTensorSquareCechIso
        K L diagram).hom.hom PUnit.unit =
      (affineCechSelectedTensorDescentDataCoverIso f hf D D).hom := by
  dsimp only
  let f := CommRingCat.ofHom (algebraMap K L)
  let hf := galoisFieldAlgebraMap_faithfullyFlat K L
  let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
  let a :=
    (relatedTripleCoordinateGaloisSemilinearAlgebraAction
      K L diagram).toModuleAction K L
      (RelatedTripleCoordinateScalarExtension L)
  let M := galoisSemilinearDescendedModule K L
    (RelatedTripleCoordinateScalarExtension L) a
  let e := relatedTripleCoordinateGaloisSelectedTensorSquareCechIso
    K L diagram
  let c := affineCechSelectedTensorDescentDataCoverIso f hf D D
  let LK := (ModuleCat.restrictScalars (algebraMap K L)).obj
    (ModuleCat.of L L)
  letI : Module K LK := LK.isModule
  letI : IsScalarTower K L LK :=
    IsScalarTower.of_algebraMap_smul (by intro k x; rfl)
  let T := TensorProduct K LK (TensorProduct K M M)
  let X := TensorProduct L (RelatedTripleCoordinateScalarExtension L)
    (RelatedTripleCoordinateScalarExtension L)
  let lhs : T →ₗ[L] X := ModuleCat.Hom.hom (e.hom.hom PUnit.unit)
  let rhs : T →ₗ[L] X := ModuleCat.Hom.hom c.hom
  have heRaw : e.hom.hom PUnit.unit =
      ModuleCat.ofHom
        (relatedTripleCoordinateGaloisComparisonTensorSquareLinearEquiv
          K L diagram).toLinearMap := by
    rfl
  have hlhs : lhs =
      (relatedTripleCoordinateGaloisComparisonTensorSquareLinearEquiv
        K L diagram).toLinearMap := by
    exact congrArg ModuleCat.Hom.hom heRaw
  apply ModuleCat.hom_ext
  change lhs = rhs
  rw [hlhs]
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul l z =>
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul m n =>
          change L at l
          have hrhs := affineCechDescendedTensorBaseChangeIso_hom_tmul
            f hf D D l m n
          change rhs (l ⊗ₜ[K] (m ⊗ₜ[K] n)) =
              ((galoisSemilinearDescendedModuleBaseChangeIso K L
                (RelatedTripleCoordinateScalarExtension L) a).hom
                  (l ⊗ₜ[K] m)) ⊗ₜ[L]
                ((galoisSemilinearDescendedModuleBaseChangeIso K L
                  (RelatedTripleCoordinateScalarExtension L) a).hom
                    ((1 : L) ⊗ₜ[K] n)) at hrhs
          change
            relatedTripleCoordinateGaloisComparisonTensorSquareLinearEquiv
                K L diagram
                ((relatedTripleCoordinateGaloisScalarRestrictLinearEquiv
                  K L l) ⊗ₜ[K] (m ⊗ₜ[K] n)) =
              rhs (l ⊗ₜ[K] (m ⊗ₜ[K] n))
          rw [
            relatedTripleCoordinateGaloisComparisonTensorSquareLinearEquiv_tmul,
            hrhs]
          rfl
      | add x y hx hy =>
          rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- Coordinate multiplication conjugated into the selected affine Čech tensor
square. -/
noncomputable def relatedTripleCoordinateGaloisSelectedMulDescentMap
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    let f := CommRingCat.ofHom (algebraMap K L)
    let hf := galoisFieldAlgebraMap_faithfullyFlat K L
    let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
    affineCechSelectedTensorDescentData f hf D D ⟶ D := by
  dsimp only
  exact
    (relatedTripleCoordinateGaloisSelectedTensorSquareCechIso
        K L diagram).hom ≫
      relatedTripleCoordinateGaloisCechMulDescentMap K L diagram

/-- Coordinate unit conjugated out of the selected affine Čech tensor unit. -/
noncomputable def relatedTripleCoordinateGaloisSelectedUnitDescentMap
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    let f := CommRingCat.ofHom (algebraMap K L)
    let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
    affineCechSelectedTensorUnitDescentData f ⟶ D := by
  dsimp only
  exact
    (relatedTripleCoordinateGaloisSelectedTensorUnitCechIso K L).hom ≫
      relatedTripleCoordinateGaloisCechUnitDescentMap K L diagram

/-- Coordinate comultiplication conjugated into the selected affine Čech
tensor square. -/
noncomputable def relatedTripleCoordinateGaloisSelectedComulDescentMap
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    let f := CommRingCat.ofHom (algebraMap K L)
    let hf := galoisFieldAlgebraMap_faithfullyFlat K L
    let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
    D ⟶ affineCechSelectedTensorDescentData f hf D D := by
  dsimp only
  exact relatedTripleCoordinateGaloisCechComulDescentMap K L diagram ≫
    (relatedTripleCoordinateGaloisSelectedTensorSquareCechIso
      K L diagram).inv

/-- Coordinate counit conjugated into the selected affine Čech tensor unit. -/
noncomputable def relatedTripleCoordinateGaloisSelectedCounitDescentMap
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    let f := CommRingCat.ofHom (algebraMap K L)
    let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
    D ⟶ affineCechSelectedTensorUnitDescentData f := by
  dsimp only
  exact relatedTripleCoordinateGaloisCechCounitDescentMap K L diagram ≫
    (relatedTripleCoordinateGaloisSelectedTensorUnitCechIso K L).inv

/-- Coordinate antipode as a selected affine Čech endomorphism. -/
noncomputable def relatedTripleCoordinateGaloisSelectedAntipodeDescentMap
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
    D ⟶ D := by
  dsimp only
  exact relatedTripleCoordinateGaloisCechAntipodeDescentMap K L diagram

/-- The conjugated selected multiplication is exactly coordinate
multiplication on the cover. -/
theorem relatedTripleCoordinateGaloisSelectedMulDescentMap_cover
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    let f := CommRingCat.ofHom (algebraMap K L)
    let hf := galoisFieldAlgebraMap_faithfullyFlat K L
    let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
    (affineCechSelectedTensorDescentDataCoverIso f hf D D).inv ≫
        (AffineCechModuleDescentData.evaluation f).map
          (relatedTripleCoordinateGaloisSelectedMulDescentMap
            K L diagram) =
      ModuleCat.ofHom
        (galoisAlgebraMultiplicationLinearMap L
          (RelatedTripleCoordinateScalarExtension L)) := by
  dsimp only
  change
    (affineCechSelectedTensorDescentDataCoverIso
        (CommRingCat.ofHom (algebraMap K L))
        (galoisFieldAlgebraMap_faithfullyFlat K L) _ _).inv ≫
      (relatedTripleCoordinateGaloisSelectedTensorSquareCechIso
        K L diagram).hom.hom PUnit.unit ≫
      ModuleCat.ofHom _ = ModuleCat.ofHom _
  rw [relatedTripleCoordinateGaloisSelectedTensorSquareCechIso_cover]
  let c := affineCechSelectedTensorDescentDataCoverIso
    (CommRingCat.ofHom (algebraMap K L))
    (galoisFieldAlgebraMap_faithfullyFlat K L)
    (relatedTripleCoordinateGaloisCechModuleDescentData K L diagram)
    (relatedTripleCoordinateGaloisCechModuleDescentData K L diagram)
  exact c.inv_hom_id_assoc _

/-- The conjugated selected unit is exactly the coordinate algebra unit on
the cover. -/
theorem relatedTripleCoordinateGaloisSelectedUnitDescentMap_cover
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    let f := CommRingCat.ofHom (algebraMap K L)
    (affineCechSelectedTensorUnitCoverIso f).inv ≫
        (AffineCechModuleDescentData.evaluation f).map
          (relatedTripleCoordinateGaloisSelectedUnitDescentMap
            K L diagram) =
      ModuleCat.ofHom
        (Algebra.linearMap L (RelatedTripleCoordinateScalarExtension L)) := by
  dsimp only
  change
    (affineCechSelectedTensorUnitCoverIso
      (CommRingCat.ofHom (algebraMap K L))).inv ≫
      (relatedTripleCoordinateGaloisSelectedTensorUnitCechIso
        K L).hom.hom PUnit.unit ≫ ModuleCat.ofHom _ = ModuleCat.ofHom _
  rw [relatedTripleCoordinateGaloisSelectedTensorUnitCechIso_cover]
  let c := affineCechSelectedTensorUnitCoverIso
    (CommRingCat.ofHom (algebraMap K L))
  exact c.inv_hom_id_assoc _

/-- The conjugated selected comultiplication is exactly coordinate
comultiplication on the cover. -/
theorem relatedTripleCoordinateGaloisSelectedComulDescentMap_cover
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    let f := CommRingCat.ofHom (algebraMap K L)
    let hf := galoisFieldAlgebraMap_faithfullyFlat K L
    let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
    (AffineCechModuleDescentData.evaluation f).map
          (relatedTripleCoordinateGaloisSelectedComulDescentMap
            K L diagram) ≫
        (affineCechSelectedTensorDescentDataCoverIso f hf D D).hom =
      ModuleCat.ofHom (CoalgebraStruct.comul :
        RelatedTripleCoordinateScalarExtension L →ₗ[L]
          TensorProduct L (RelatedTripleCoordinateScalarExtension L)
            (RelatedTripleCoordinateScalarExtension L)) := by
  dsimp only
  change ModuleCat.ofHom _ ≫
    (relatedTripleCoordinateGaloisSelectedTensorSquareCechIso
      K L diagram).inv.hom PUnit.unit ≫
    (affineCechSelectedTensorDescentDataCoverIso
      (CommRingCat.ofHom (algebraMap K L))
      (galoisFieldAlgebraMap_faithfullyFlat K L) _ _).hom = ModuleCat.ofHom _
  rw [← relatedTripleCoordinateGaloisSelectedTensorSquareCechIso_cover]
  let f := CommRingCat.ofHom (algebraMap K L)
  let e := relatedTripleCoordinateGaloisSelectedTensorSquareCechIso
    K L diagram
  let ee := (AffineCechModuleDescentData.evaluation f).mapIso e
  let q := ModuleCat.ofHom (CoalgebraStruct.comul :
    RelatedTripleCoordinateScalarExtension L →ₗ[L]
      TensorProduct L (RelatedTripleCoordinateScalarExtension L)
        (RelatedTripleCoordinateScalarExtension L))
  change q ≫ (ee.inv ≫ ee.hom) = q
  calc
    _ = q ≫ 𝟙 _ := congrArg (fun z => q ≫ z) ee.inv_hom_id
    _ = q := Category.comp_id q

/-- The conjugated selected counit is exactly the coordinate coalgebra counit
on the cover. -/
theorem relatedTripleCoordinateGaloisSelectedCounitDescentMap_cover
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    let f := CommRingCat.ofHom (algebraMap K L)
    (AffineCechModuleDescentData.evaluation f).map
          (relatedTripleCoordinateGaloisSelectedCounitDescentMap
            K L diagram) ≫
        (affineCechSelectedTensorUnitCoverIso f).hom =
      ModuleCat.ofHom (CoalgebraStruct.counit :
        RelatedTripleCoordinateScalarExtension L →ₗ[L] L) := by
  dsimp only
  change ModuleCat.ofHom _ ≫
    (relatedTripleCoordinateGaloisSelectedTensorUnitCechIso
      K L).inv.hom PUnit.unit ≫
    (affineCechSelectedTensorUnitCoverIso
      (CommRingCat.ofHom (algebraMap K L))).hom = ModuleCat.ofHom _
  rw [← relatedTripleCoordinateGaloisSelectedTensorUnitCechIso_cover]
  let f := CommRingCat.ofHom (algebraMap K L)
  let e := relatedTripleCoordinateGaloisSelectedTensorUnitCechIso K L
  let ee := (AffineCechModuleDescentData.evaluation f).mapIso e
  let q := ModuleCat.ofHom (CoalgebraStruct.counit :
    RelatedTripleCoordinateScalarExtension L →ₗ[L] L)
  change q ≫ (ee.inv ≫ ee.hom) = q
  calc
    _ = q ≫ 𝟙 _ := congrArg (fun z => q ≫ z) ee.inv_hom_id
    _ = q := Category.comp_id q

/-- The selected antipode is exactly the coordinate antipode on the cover. -/
theorem relatedTripleCoordinateGaloisSelectedAntipodeDescentMap_cover
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    let f := CommRingCat.ofHom (algebraMap K L)
    (AffineCechModuleDescentData.evaluation f).map
        (relatedTripleCoordinateGaloisSelectedAntipodeDescentMap
          K L diagram) =
      ModuleCat.ofHom (HopfAlgebraStruct.antipode L :
        RelatedTripleCoordinateScalarExtension L →ₗ[L]
          RelatedTripleCoordinateScalarExtension L) := by
  dsimp only
  exact relatedTripleCoordinateGaloisCechAntipodeDescentMap_hom
    K L diagram

set_option maxRecDepth 4000 in
/-- After identifying the right-associated selected triple tensor with the
ordinary right-associated cover tensor, applying multiplication in the inner
right pair and then once more is exactly the ordinary nested coordinate
multiplication. -/
theorem relatedTripleCoordinateGaloisSelectedMulRightNestedCover
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    let f := CommRingCat.ofHom (algebraMap K L)
    let hf := galoisFieldAlgebraMap_faithfullyFlat K L
    let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
    let mul := relatedTripleCoordinateGaloisSelectedMulDescentMap K L diagram
    let eR := affineCechSelectedTensorRightAssociatedCoverIso f hf D D D
    let muA := ModuleCat.ofHom
      (galoisAlgebraMultiplicationLinearMap L (RelatedTripleCoordinateScalarExtension L))
    eR.inv ≫ (affineCechSelectedTensorMap f hf (𝟙 D) mul).hom PUnit.unit ≫
        mul.hom PUnit.unit =
      ModuleCat.ofHom (TensorProduct.map LinearMap.id
        (galoisAlgebraMultiplicationLinearMap L
          (RelatedTripleCoordinateScalarExtension L))) ≫ muA := by
  dsimp only
  let f := CommRingCat.ofHom (algebraMap K L)
  let hf := galoisFieldAlgebraMap_faithfullyFlat K L
  let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
  let mul := relatedTripleCoordinateGaloisSelectedMulDescentMap K L diagram
  let T := affineCechSelectedTensorDescentData f hf D D
  let DA : ModuleCat L := (AffineCechModuleDescentData.evaluation f).obj D
  let TA : ModuleCat L := (AffineCechModuleDescentData.evaluation f).obj T
  let eT : TA ≅ ModuleCat.of L (TensorProduct L DA DA) :=
    affineCechSelectedTensorDescentDataCoverIso f hf D D
  let cR : (AffineCechModuleDescentData.evaluation f).obj
      (affineCechSelectedTensorDescentData f hf D T) ≅
      ModuleCat.of L (TensorProduct L DA TA) :=
    affineCechSelectedTensorDescentDataCoverIso f hf D T
  let qR := (TensorProduct.congr (LinearEquiv.refl L DA)
      eT.toLinearEquiv).toModuleIso
  let eR := affineCechSelectedTensorRightAssociatedCoverIso f hf D D D
  let mulA : TA ⟶ DA := mul.hom PUnit.unit
  let muA : ModuleCat.of L (TensorProduct L DA DA) ⟶ DA :=
    ModuleCat.ofHom
      (galoisAlgebraMultiplicationLinearMap L (RelatedTripleCoordinateScalarExtension L))
  let tm := (affineCechSelectedTensorMap f hf (𝟙 D) mul).hom PUnit.unit
  let mapm : ModuleCat.of L (TensorProduct L DA TA) ⟶
      ModuleCat.of L (TensorProduct L DA DA) :=
    ModuleCat.ofHom
      (TensorProduct.map
        (ModuleCat.Hom.hom ((AffineCechModuleDescentData.evaluation f).map (𝟙 D)))
        (ModuleCat.Hom.hom ((AffineCechModuleDescentData.evaluation f).map mul)))
  have hm : eT.inv ≫ mulA = muA := by
    exact relatedTripleCoordinateGaloisSelectedMulDescentMap_cover K L diagram
  have hn : tm ≫ eT.hom = cR.hom ≫ mapm := by
    exact affineCechSelectedTensorDescentDataCoverIso_natural f hf (𝟙 D) mul
  have h1 := congrArg (fun z => qR.inv ≫ cR.inv ≫ z ≫ eT.inv ≫
    mulA) hn
  have h2 := congrArg (fun z => qR.inv ≫ z ≫ eT.inv ≫ mulA)
    (cR.inv_hom_id_assoc mapm)
  have h3 := congrArg (fun z => qR.inv ≫ mapm ≫ z) hm
  change eR.inv ≫ tm ≫ mulA =
      ModuleCat.ofHom (TensorProduct.map LinearMap.id
        (galoisAlgebraMultiplicationLinearMap L
          (RelatedTripleCoordinateScalarExtension L))) ≫ muA
  change (qR.inv ≫ cR.inv) ≫ tm ≫ mulA = _
  rw [← eT.hom_inv_id_assoc (mulA)]
  simp only [Category.assoc]
  refine h1.trans (h2.trans (h3.trans ?_))
  let std :
      ModuleCat.of L (TensorProduct L DA (TensorProduct L DA DA)) ⟶
        ModuleCat.of L (TensorProduct L DA DA) :=
    ModuleCat.ofHom (TensorProduct.map LinearMap.id (ModuleCat.Hom.hom muA))
  have hpre : qR.inv ≫ mapm = std := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
        change (show DA from x) ⊗ₜ[L]
            ModuleCat.Hom.hom (eT.inv ≫ mulA) y =
          (show DA from x) ⊗ₜ[L] ModuleCat.Hom.hom muA y
        rw [hm]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hpost := congrArg (fun z => z ≫ muA) hpre
  exact (Category.assoc qR.inv mapm muA).symm.trans hpost

set_option maxRecDepth 4000 in
/-- After identifying the left-associated selected triple tensor with the
ordinary left-associated cover tensor, applying multiplication in the inner
left pair and then once more is exactly the ordinary nested coordinate
multiplication. -/
theorem relatedTripleCoordinateGaloisSelectedMulLeftNestedCover
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    let f := CommRingCat.ofHom (algebraMap K L)
    let hf := galoisFieldAlgebraMap_faithfullyFlat K L
    let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
    let mul := relatedTripleCoordinateGaloisSelectedMulDescentMap K L diagram
    let eL := affineCechSelectedTensorLeftAssociatedCoverIso f hf D D D
    let muA := ModuleCat.ofHom
      (galoisAlgebraMultiplicationLinearMap L (RelatedTripleCoordinateScalarExtension L))
    eL.inv ≫ (affineCechSelectedTensorMap f hf mul (𝟙 D)).hom PUnit.unit ≫
        mul.hom PUnit.unit =
      ModuleCat.ofHom (TensorProduct.map
        (galoisAlgebraMultiplicationLinearMap L
          (RelatedTripleCoordinateScalarExtension L)) LinearMap.id) ≫ muA := by
  dsimp only
  let f := CommRingCat.ofHom (algebraMap K L)
  let hf := galoisFieldAlgebraMap_faithfullyFlat K L
  let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
  let mul := relatedTripleCoordinateGaloisSelectedMulDescentMap K L diagram
  let T := affineCechSelectedTensorDescentData f hf D D
  let DA : ModuleCat L := (AffineCechModuleDescentData.evaluation f).obj D
  let TA : ModuleCat L := (AffineCechModuleDescentData.evaluation f).obj T
  let eT : TA ≅ ModuleCat.of L (TensorProduct L DA DA) :=
    affineCechSelectedTensorDescentDataCoverIso f hf D D
  let cL : (AffineCechModuleDescentData.evaluation f).obj
      (affineCechSelectedTensorDescentData f hf T D) ≅
      ModuleCat.of L (TensorProduct L TA DA) :=
    affineCechSelectedTensorDescentDataCoverIso f hf T D
  let qL := (TensorProduct.congr eT.toLinearEquiv
      (LinearEquiv.refl L DA)).toModuleIso
  let eL := affineCechSelectedTensorLeftAssociatedCoverIso f hf D D D
  let mulA : TA ⟶ DA := mul.hom PUnit.unit
  let muA : ModuleCat.of L (TensorProduct L DA DA) ⟶ DA :=
    ModuleCat.ofHom
      (galoisAlgebraMultiplicationLinearMap L (RelatedTripleCoordinateScalarExtension L))
  let tm := (affineCechSelectedTensorMap f hf mul (𝟙 D)).hom PUnit.unit
  let mapm : ModuleCat.of L (TensorProduct L TA DA) ⟶
      ModuleCat.of L (TensorProduct L DA DA) :=
    ModuleCat.ofHom
      (TensorProduct.map
        (ModuleCat.Hom.hom ((AffineCechModuleDescentData.evaluation f).map mul))
        (ModuleCat.Hom.hom ((AffineCechModuleDescentData.evaluation f).map (𝟙 D))))
  have hm : eT.inv ≫ mulA = muA := by
    exact relatedTripleCoordinateGaloisSelectedMulDescentMap_cover K L diagram
  have hn : tm ≫ eT.hom = cL.hom ≫ mapm := by
    exact affineCechSelectedTensorDescentDataCoverIso_natural f hf mul (𝟙 D)
  have h1 := congrArg (fun z => qL.inv ≫ cL.inv ≫ z ≫ eT.inv ≫
    mulA) hn
  have h2 := congrArg (fun z => qL.inv ≫ z ≫ eT.inv ≫ mulA)
    (cL.inv_hom_id_assoc mapm)
  have h3 := congrArg (fun z => qL.inv ≫ mapm ≫ z) hm
  change eL.inv ≫ tm ≫ mulA =
      ModuleCat.ofHom (TensorProduct.map
        (galoisAlgebraMultiplicationLinearMap L
          (RelatedTripleCoordinateScalarExtension L)) LinearMap.id) ≫ muA
  change (qL.inv ≫ cL.inv) ≫ tm ≫ mulA = _
  rw [← eT.hom_inv_id_assoc (mulA)]
  simp only [Category.assoc]
  refine h1.trans (h2.trans (h3.trans ?_))
  let std :
      ModuleCat.of L (TensorProduct L (TensorProduct L DA DA) DA) ⟶
        ModuleCat.of L (TensorProduct L DA DA) :=
    ModuleCat.ofHom (TensorProduct.map (ModuleCat.Hom.hom muA) LinearMap.id)
  have hpre : qL.inv ≫ mapm = std := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
        change
          ModuleCat.Hom.hom (eT.inv ≫ mulA) x ⊗ₜ[L] (show DA from y) =
            ModuleCat.Hom.hom muA x ⊗ₜ[L] (show DA from y)
        rw [hm]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hpost := congrArg (fun z => z ≫ muA) hpre
  exact (Category.assoc qL.inv mapm muA).symm.trans hpost

set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 200000 in
-- Tensor induction needs the coordinate scalar-extension instances.
set_option maxHeartbeats 1000000 in
-- The cover proof combines nested categorical cancellation and tensor induction.
/-- The selected coordinate multiplication is associative. -/
theorem relatedTripleCoordinateGaloisSelectedMul_assoc
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    let f := CommRingCat.ofHom (algebraMap K L)
    let hf := galoisFieldAlgebraMap_faithfullyFlat K L
    let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
    let mul := relatedTripleCoordinateGaloisSelectedMulDescentMap K L diagram
    (affineCechSelectedTensorAssociatorIso f hf D D D).hom ≫
        affineCechSelectedTensorMap f hf (𝟙 D) mul ≫ mul =
      affineCechSelectedTensorMap f hf mul (𝟙 D) ≫ mul := by
  dsimp only
  let f := CommRingCat.ofHom (algebraMap K L)
  let hf := galoisFieldAlgebraMap_faithfullyFlat K L
  let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
  let mul := relatedTripleCoordinateGaloisSelectedMulDescentMap K L diagram
  let eL := affineCechSelectedTensorLeftAssociatedCoverIso f hf D D D
  let eR := affineCechSelectedTensorRightAssociatedCoverIso f hf D D D
  let B := RelatedTripleCoordinateScalarExtension L
  let muA : ModuleCat.of L (TensorProduct L B B) ⟶ ModuleCat.of L B :=
    ModuleCat.ofHom (galoisAlgebraMultiplicationLinearMap L B)
  let assocA : ModuleCat.of L (TensorProduct L (TensorProduct L B B) B) ⟶
      ModuleCat.of L (TensorProduct L B (TensorProduct L B B)) :=
    ModuleCat.ofHom (TensorProduct.assoc L B B B).toLinearMap
  let rightA : ModuleCat.of L (TensorProduct L B (TensorProduct L B B)) ⟶
      ModuleCat.of L (TensorProduct L B B) :=
    ModuleCat.ofHom (TensorProduct.map LinearMap.id
      (galoisAlgebraMultiplicationLinearMap L B))
  let leftA : ModuleCat.of L (TensorProduct L (TensorProduct L B B) B) ⟶
      ModuleCat.of L (TensorProduct L B B) :=
    ModuleCat.ofHom (TensorProduct.map
      (galoisAlgebraMultiplicationLinearMap L B) LinearMap.id)
  ext i
  cases i
  let q := ((affineCechSelectedTensorAssociatorIso f hf D D D).hom ≫
    affineCechSelectedTensorMap f hf (𝟙 D) mul ≫ mul).hom PUnit.unit
  let r := (affineCechSelectedTensorMap f hf mul (𝟙 D) ≫ mul).hom PUnit.unit
  have ha : ((affineCechSelectedTensorAssociatorIso f hf D D D).hom.hom
      PUnit.unit) ≫ eR.hom = eL.hom ≫ assocA := by
    exact affineCechSelectedTensorAssociatorIso_cover f hf D D D
  have hr : eR.inv ≫ (affineCechSelectedTensorMap f hf (𝟙 D) mul).hom
      PUnit.unit ≫ mul.hom PUnit.unit = rightA ≫ muA := by
    simpa only [rightA, muA] using
      (relatedTripleCoordinateGaloisSelectedMulRightNestedCover K L diagram)
  have hl : eL.inv ≫ (affineCechSelectedTensorMap f hf mul (𝟙 D)).hom
      PUnit.unit ≫ mul.hom PUnit.unit = leftA ≫ muA := by
    simpa only [leftA, muA] using
      (relatedTripleCoordinateGaloisSelectedMulLeftNestedCover K L diagram)
  have hstd : assocA ≫ rightA ≫ muA = leftA ≫ muA := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul z w =>
      induction z using TensorProduct.induction_on with
      | zero => simp only [TensorProduct.zero_tmul, map_zero]
      | tmul x y =>
        change (show B from x) * ((show B from y) * (show B from w)) =
          ((show B from x) * (show B from y)) * (show B from w)
        exact (mul_assoc _ _ _).symm
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  let a :=
    (affineCechSelectedTensorAssociatorIso f hf D D D).hom.hom PUnit.unit
  let t :=
    (affineCechSelectedTensorMap f hf (𝟙 D) mul).hom PUnit.unit ≫
      mul.hom PUnit.unit
  have ha0 : eL.inv ≫ a ≫ eR.hom = assocA := by
    dsimp only [a]
    rw [ha]
    exact eL.inv_hom_id_assoc assocA
  have hconj := congrArg (fun z => z ≫ eR.inv ≫ t) ha0
  rw [← Category.assoc eL.inv a eR.hom] at hconj
  rw [Category.assoc (eL.inv ≫ a) eR.hom (eR.inv ≫ t),
    eR.hom_inv_id_assoc t] at hconj
  have hconj' :
      eL.inv ≫ a ≫ t = assocA ≫ eR.inv ≫ t :=
    (Category.assoc eL.inv a t).symm.trans hconj
  have hr0 : eR.inv ≫ t = rightA ≫ muA := by
    simpa only [t] using hr
  have hright :
      assocA ≫ eR.inv ≫ t = assocA ≫ (rightA ≫ muA) :=
    congrArg (fun z => assocA ≫ z) hr0
  have hstd0 : assocA ≫ (rightA ≫ muA) = leftA ≫ muA := by
    simpa only [Category.assoc] using hstd
  have hpre : eL.inv ≫ q = eL.inv ≫ r := by
    dsimp [q, r]
    exact hconj'.trans (hright.trans (hstd0.trans hl.symm))
  have hfin : q = r := by
    rw [← eL.hom_inv_id_assoc q, ← eL.hom_inv_id_assoc r]
    exact congrArg (fun z => eL.hom ≫ z) hpre
  exact hfin

set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 3000000 in
/-- The selected coordinate unit is a left unit for selected coordinate
multiplication. -/
theorem relatedTripleCoordinateGaloisSelectedUnit_mul
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    let f := CommRingCat.ofHom (algebraMap K L)
    let hf := galoisFieldAlgebraMap_faithfullyFlat K L
    let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
    let mul := relatedTripleCoordinateGaloisSelectedMulDescentMap K L diagram
    let unit := relatedTripleCoordinateGaloisSelectedUnitDescentMap K L diagram
    affineCechSelectedTensorMap f hf unit (𝟙 D) ≫ mul =
      (affineCechSelectedTensorLeftUnitorIso f hf D).hom := by
  dsimp only
  let f := CommRingCat.ofHom (algebraMap K L)
  let hf := galoisFieldAlgebraMap_faithfullyFlat K L
  let D := relatedTripleCoordinateGaloisCechModuleDescentData K L diagram
  let U := affineCechSelectedTensorUnitDescentData f
  let unit := relatedTripleCoordinateGaloisSelectedUnitDescentMap K L diagram
  let mul := relatedTripleCoordinateGaloisSelectedMulDescentMap K L diagram
  let T := affineCechSelectedTensorDescentData f hf D D
  let UA : ModuleCat L := (AffineCechModuleDescentData.evaluation f).obj U
  let DA : ModuleCat L := (AffineCechModuleDescentData.evaluation f).obj D
  let TA : ModuleCat L := (AffineCechModuleDescentData.evaluation f).obj T
  let eU : UA ≅ ModuleCat.of L L :=
    affineCechSelectedTensorUnitCoverIso f
  let eT : TA ≅ ModuleCat.of L (TensorProduct L DA DA) :=
    affineCechSelectedTensorDescentDataCoverIso f hf D D
  let cL : (AffineCechModuleDescentData.evaluation f).obj
      (affineCechSelectedTensorDescentData f hf U D) ≅
      ModuleCat.of L (TensorProduct L UA DA) :=
    affineCechSelectedTensorDescentDataCoverIso f hf U D
  let qL := (TensorProduct.congr eU.toLinearEquiv
      (LinearEquiv.refl L DA)).toModuleIso
  let eL := affineCechSelectedTensorLeftUnitorCoverIso f hf D
  let unitA : UA ⟶ DA := unit.hom PUnit.unit
  let mulA : TA ⟶ DA := mul.hom PUnit.unit
  let etaA : ModuleCat.of L L ⟶ DA :=
    ModuleCat.ofHom
      (Algebra.linearMap L (RelatedTripleCoordinateScalarExtension L))
  let muA : ModuleCat.of L (TensorProduct L DA DA) ⟶ DA :=
    ModuleCat.ofHom
      (galoisAlgebraMultiplicationLinearMap L
        (RelatedTripleCoordinateScalarExtension L))
  let tm := (affineCechSelectedTensorMap f hf unit (𝟙 D)).hom PUnit.unit
  let mapm : ModuleCat.of L (TensorProduct L UA DA) ⟶
      ModuleCat.of L (TensorProduct L DA DA) :=
    ModuleCat.ofHom
      (TensorProduct.map
        (ModuleCat.Hom.hom
          ((AffineCechModuleDescentData.evaluation f).map unit))
        (ModuleCat.Hom.hom
          ((AffineCechModuleDescentData.evaluation f).map (𝟙 D))))
  let lidA : ModuleCat.of L (TensorProduct L L DA) ⟶ DA :=
    ModuleCat.ofHom (TensorProduct.lid L DA).toLinearMap
  have hu : eU.inv ≫ unitA = etaA := by
    change
      (affineCechSelectedTensorUnitCoverIso f).inv ≫
          (AffineCechModuleDescentData.evaluation f).map unit =
        ModuleCat.ofHom
          (Algebra.linearMap L (RelatedTripleCoordinateScalarExtension L))
    exact relatedTripleCoordinateGaloisSelectedUnitDescentMap_cover K L diagram
  have hm : eT.inv ≫ mulA = muA := by
    change
      (affineCechSelectedTensorDescentDataCoverIso f hf D D).inv ≫
          (AffineCechModuleDescentData.evaluation f).map mul =
        ModuleCat.ofHom (galoisAlgebraMultiplicationLinearMap L
          (RelatedTripleCoordinateScalarExtension L))
    exact relatedTripleCoordinateGaloisSelectedMulDescentMap_cover K L diagram
  have hn : tm ≫ eT.hom = cL.hom ≫ mapm := by
    exact affineCechSelectedTensorDescentDataCoverIso_natural
      f hf unit (𝟙 D)
  have h1 := congrArg
    (fun z => qL.inv ≫ cL.inv ≫ z ≫ eT.inv ≫ mulA) hn
  have h2 := congrArg
    (fun z => qL.inv ≫ z ≫ eT.inv ≫ mulA)
    (cL.inv_hom_id_assoc mapm)
  have h3 := congrArg (fun z => qL.inv ≫ mapm ≫ z) hm
  have hstd : qL.inv ≫ mapm ≫ muA = lidA := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x =>
        change
          ModuleCat.Hom.hom muA
              (ModuleCat.Hom.hom (eU.inv ≫ unitA) a ⊗ₜ[L]
                (show DA from x)) =
            (show L from a) • (show DA from x)
        rw [hu]
        change
          (algebraMap L (RelatedTripleCoordinateScalarExtension L)
              (show L from a)) *
              (show RelatedTripleCoordinateScalarExtension L from x) =
            (show L from a) •
              (show RelatedTripleCoordinateScalarExtension L from x)
        exact (Algebra.smul_def _ _).symm
    | add x y hx hy => simp only [map_add, hx, hy]
  have hcover : eL.inv ≫ tm ≫ mulA = lidA := by
    change (qL.inv ≫ cL.inv) ≫ tm ≫ mulA = lidA
    rw [← eT.hom_inv_id_assoc mulA]
    simp only [Category.assoc]
    exact h1.trans (h2.trans (h3.trans hstd))
  ext i
  cases i
  rw [affineCechSelectedTensorLeftUnitorIso_cover]
  change tm ≫ mulA = eL.hom ≫ lidA
  letI : IsIso eL.inv := eL.isIso_inv
  letI : Epi eL.inv := IsIso.epi_of_iso eL.inv
  apply (cancel_epi eL.inv).mp
  exact hcover.trans (eL.inv_hom_id_assoc lidA).symm

end

end RiemannResearch.AlgebraicGeometry
