/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.AffineCechHopfDescent
import RiemannResearch.AlgebraicGeometry.D4ZornCoordinateModuleDescent
import RiemannResearch.LinearAlgebra.RootSystem.D4ZornCoordinateGaloisSemilinearHopfDescent

/-!
# Finite-Galois Čech Hopf maps for D4 related triples

This module transports the five structure maps of the scalar-extended D4
related-triple coordinate Hopf algebra from finite-Galois
extension--restriction coalgebras to canonical affine Čech module descent
data.  The transported maps recover multiplication, unit, comultiplication,
counit, and antipode exactly on the unique cover.

The tensor-square and scalar Čech data constructed here are the raw Galois
diagonal-action data.  Identifying them with the tensor product and tensor
unit selected by effective affine Čech descent is the remaining coherence
step before these maps can be assembled into an
`AffineCechSelectedCommHopfAlgebraObject`.

Source: user-provided D4 Hopf-descent program.
-/

namespace RiemannResearch.AlgebraicGeometry

noncomputable section

open RiemannResearch.GaloisCohomology
open RiemannResearch.LinearAlgebra.RootSystem.D4Triality
open RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn
open scoped TensorProduct

universe u

private abbrev ASelected := RelatedTripleCoordinateRing.{0}

local instance coordinateGaloisSelectedCommRing : CommRing ASelected :=
  inferInstance

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L] [IsGalois K L]
variable (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry)

private noncomputable abbrev coordinateAction :=
  (relatedTripleCoordinateGaloisSemilinearAlgebraAction K L diagram).toModuleAction
    K L (RelatedTripleCoordinateScalarExtension L)

private noncomputable abbrev tensorSquareAction :=
  galoisSemilinearTensorSquareAction K L
    (RelatedTripleCoordinateScalarExtension L)
    (relatedTripleCoordinateGaloisSemilinearAlgebraAction K L diagram)

private noncomputable abbrev scalarAction :=
  (galoisScalarSemilinearAlgebraAction K L).toModuleAction K L L

/-- The canonical affine Čech datum for the diagonal action on the coordinate
tensor square. -/
noncomputable def relatedTripleCoordinateGaloisTensorSquareCechModuleDescentData :
    AffineCechModuleDescentData
      (CommRingCat.ofHom (algebraMap K L)) :=
  galoisSemilinearCechModuleDescentData K L
    (TensorProduct L (RelatedTripleCoordinateScalarExtension L)
      (RelatedTripleCoordinateScalarExtension L))
    (tensorSquareAction K L diagram)

/-- The canonical affine Čech datum for the scalar Galois action on `L`. -/
noncomputable def relatedTripleCoordinateGaloisScalarCechModuleDescentData :
    AffineCechModuleDescentData
      (CommRingCat.ofHom (algebraMap K L)) :=
  galoisSemilinearCechModuleDescentData K L L (scalarAction K L)

/-- Coordinate multiplication transported to canonical affine Čech descent
data. -/
noncomputable def relatedTripleCoordinateGaloisCechMulDescentMap :
    relatedTripleCoordinateGaloisTensorSquareCechModuleDescentData
        K L diagram ⟶
      relatedTripleCoordinateGaloisCechModuleDescentData K L diagram :=
  galoisSemilinearCechModuleDescentMap K L _ _
    (tensorSquareAction K L diagram) (coordinateAction K L diagram)
    (galoisAlgebraMultiplicationLinearMap L
      (RelatedTripleCoordinateScalarExtension L))
    (galoisSemilinearAlgebraMul_equivariant K L
      (RelatedTripleCoordinateScalarExtension L)
      (relatedTripleCoordinateGaloisSemilinearAlgebraAction K L diagram))

/-- Coordinate unit transported to canonical affine Čech descent data. -/
noncomputable def relatedTripleCoordinateGaloisCechUnitDescentMap :
    relatedTripleCoordinateGaloisScalarCechModuleDescentData K L ⟶
      relatedTripleCoordinateGaloisCechModuleDescentData K L diagram :=
  galoisSemilinearCechModuleDescentMap K L _ _
    (scalarAction K L) (coordinateAction K L diagram)
    (Algebra.linearMap L (RelatedTripleCoordinateScalarExtension L))
    (galoisSemilinearAlgebraUnit_equivariant K L
      (RelatedTripleCoordinateScalarExtension L)
      (relatedTripleCoordinateGaloisSemilinearAlgebraAction K L diagram))

/-- Coordinate comultiplication transported to canonical affine Čech descent
data. -/
noncomputable def relatedTripleCoordinateGaloisCechComulDescentMap :
    relatedTripleCoordinateGaloisCechModuleDescentData K L diagram ⟶
      relatedTripleCoordinateGaloisTensorSquareCechModuleDescentData
        K L diagram :=
  galoisSemilinearCechModuleDescentMap K L _ _
    (coordinateAction K L diagram) (tensorSquareAction K L diagram)
    CoalgebraStruct.comul
    (relatedTripleCoordinateGaloisSemilinearComul_equivariant K L diagram)

/-- Coordinate counit transported to canonical affine Čech descent data. -/
noncomputable def relatedTripleCoordinateGaloisCechCounitDescentMap :
    relatedTripleCoordinateGaloisCechModuleDescentData K L diagram ⟶
      relatedTripleCoordinateGaloisScalarCechModuleDescentData K L :=
  galoisSemilinearCechModuleDescentMap K L _ _
    (coordinateAction K L diagram) (scalarAction K L)
    CoalgebraStruct.counit
    (relatedTripleCoordinateGaloisSemilinearCounit_equivariant K L diagram)

/-- Coordinate antipode transported to canonical affine Čech descent data. -/
noncomputable def relatedTripleCoordinateGaloisCechAntipodeDescentMap :
    relatedTripleCoordinateGaloisCechModuleDescentData K L diagram ⟶
      relatedTripleCoordinateGaloisCechModuleDescentData K L diagram :=
  galoisSemilinearCechModuleDescentMap K L _ _
    (coordinateAction K L diagram) (coordinateAction K L diagram)
    (HopfAlgebraStruct.antipode L)
    (relatedTripleCoordinateGaloisSemilinearAntipode_equivariant K L diagram)

/-- On the cover, the transported Čech multiplication is the original
coordinate multiplication. -/
@[simp] theorem relatedTripleCoordinateGaloisCechMulDescentMap_hom :
    (relatedTripleCoordinateGaloisCechMulDescentMap
        K L diagram).hom PUnit.unit =
      ModuleCat.ofHom
        (galoisAlgebraMultiplicationLinearMap L
          (RelatedTripleCoordinateScalarExtension L)) := by
  apply galoisSemilinearCechModuleDescentMap_hom

/-- On the cover, the transported Čech unit is the original coordinate unit. -/
@[simp] theorem relatedTripleCoordinateGaloisCechUnitDescentMap_hom :
    (relatedTripleCoordinateGaloisCechUnitDescentMap
        K L diagram).hom PUnit.unit =
      ModuleCat.ofHom
        (Algebra.linearMap L (RelatedTripleCoordinateScalarExtension L)) := by
  apply galoisSemilinearCechModuleDescentMap_hom

/-- On the cover, the transported Čech comultiplication is the original
coordinate comultiplication. -/
@[simp] theorem relatedTripleCoordinateGaloisCechComulDescentMap_hom :
    (relatedTripleCoordinateGaloisCechComulDescentMap
        K L diagram).hom PUnit.unit =
      ModuleCat.ofHom (CoalgebraStruct.comul :
        RelatedTripleCoordinateScalarExtension L →ₗ[L]
          TensorProduct L (RelatedTripleCoordinateScalarExtension L)
            (RelatedTripleCoordinateScalarExtension L)) := by
  apply galoisSemilinearCechModuleDescentMap_hom

/-- On the cover, the transported Čech counit is the original coordinate
counit. -/
@[simp] theorem relatedTripleCoordinateGaloisCechCounitDescentMap_hom :
    (relatedTripleCoordinateGaloisCechCounitDescentMap
        K L diagram).hom PUnit.unit =
      ModuleCat.ofHom (CoalgebraStruct.counit :
        RelatedTripleCoordinateScalarExtension L →ₗ[L] L) := by
  apply galoisSemilinearCechModuleDescentMap_hom

/-- On the cover, the transported Čech antipode is the original coordinate
antipode. -/
@[simp] theorem relatedTripleCoordinateGaloisCechAntipodeDescentMap_hom :
    (relatedTripleCoordinateGaloisCechAntipodeDescentMap
        K L diagram).hom PUnit.unit =
      ModuleCat.ofHom
        (HopfAlgebraStruct.antipode L :
          RelatedTripleCoordinateScalarExtension L →ₗ[L]
            RelatedTripleCoordinateScalarExtension L) := by
  apply galoisSemilinearCechModuleDescentMap_hom

end

end RiemannResearch.AlgebraicGeometry
