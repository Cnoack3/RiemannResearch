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

end

end RiemannResearch.AlgebraicGeometry
