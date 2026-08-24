/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.D4ZornCoordinateGaloisSelectedCoalgebraLaws

/-!
# Selected D4 bialgebra laws in affine Čech descent

This module packages the selected finite-Galois D4 coordinate multiplication
as a commutative algebra object and begins the four compatibility equations
between that algebra object and the selected coalgebra object.

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

end

end RiemannResearch.AlgebraicGeometry
