/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.AffineModuleComonadicBridge
import RiemannResearch.GaloisCohomology.GaloisSemilinearModuleComonadicDescent
import RiemannResearch.LinearAlgebra.RootSystem.D4ZornCoordinateGaloisSemilinearModuleDescent
import RiemannResearch.LinearAlgebra.RootSystem.D4ZornCoordinateTriality

/-!
# Effective module descent for the D4 coordinate algebra

This module first records the effective-descent consequence available from a
supplied chosen Čech module datum for the scalar-extended split-Zorn
related-triple coordinate algebra.

For a finite Galois extension, it then constructs that datum canonically from
the diagram-twisted semilinear Galois action, selects a descended K-module, and
identifies its scalar extension with the original coordinate module. Thus the
finite-Galois result no longer assumes a supplied datum or cover isomorphism.

No multiplication, unit, comultiplication, counit, antipode, Hopf identity, or
represented affine group scheme is descended here.

Source: user-provided D4 semilinear-triality descent program. The construction
uses the generic comonadic semilinear module descent theorem and the established
affine Čech/comonadic bridge.
-/

open CategoryTheory

namespace RiemannResearch.AlgebraicGeometry

open RiemannResearch.GaloisCohomology
open RiemannResearch.LinearAlgebra.RootSystem.D4Triality
open RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn

universe u

noncomputable section

/-- The underlying L-module of the scalar-extended integral related-triple
coordinate algebra. -/
def relatedTripleCoordinateScalarExtensionModule
    (L : Type u) [CommRing L] : ModuleCat L :=
  ModuleCat.of L
    (TensorProduct ℤ L RelatedTripleCoordinateRing.{0})

/-- Once a chosen Cech datum with the expected cover module is supplied,
faithfully flat module descent produces an underlying module over the base
field whose scalar extension is that coordinate module. -/
theorem relatedTripleCoordinateCechModuleDescent_effective
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (D : AffineCechModuleDescentData
      (CommRingCat.ofHom (algebraMap K L)))
    (coverIso : D.obj PUnit.unit ≅
      relatedTripleCoordinateScalarExtensionModule L) :
    ∃ N : ModuleCat K,
      Nonempty ((ModuleCat.extendScalars (algebraMap K L)).obj N ≅
        relatedTripleCoordinateScalarExtensionModule L) := by
  have hf : (algebraMap K L).FaithfullyFlat := by
    unfold RingHom.FaithfullyFlat
    infer_instance
  let F := affineCechModuleDescentComparison
    (CommRingCat.ofHom (algebraMap K L))
  let _ : F.IsEquivalence :=
    affineCechModuleDescentComparison_isEquivalence _ hf
  let N := F.objPreimage D
  let eD : F.obj N ≅ D := F.objObjPreimageIso D
  let eL : (ModuleCat.extendScalars (algebraMap K L)).obj N ≅
      D.obj PUnit.unit :=
    (AffineCechModuleDescentData.evaluation
      (CommRingCat.ofHom (algebraMap K L))).mapIso eD
  exact ⟨N, ⟨eL ≪≫ coverIso⟩⟩

/-- The canonical chosen Čech module datum for the diagram-twisted D4
related-triple coordinate module. -/
noncomputable def relatedTripleCoordinateGaloisCechModuleDescentData
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    AffineCechModuleDescentData
      (CommRingCat.ofHom (algebraMap K L)) :=
  galoisSemilinearCechModuleDescentData K L
    (RelatedTripleCoordinateScalarExtension L)
    (relatedTripleCoordinateGaloisSemilinearModuleAction K L diagram)

/-- The cover object of the canonical D4 Čech datum is the scalar-extended
related-triple coordinate module. -/
noncomputable def relatedTripleCoordinateGaloisCechModuleDescentData_coverIso
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    (relatedTripleCoordinateGaloisCechModuleDescentData
      K L diagram).obj PUnit.unit ≅
      relatedTripleCoordinateScalarExtensionModule L :=
  galoisSemilinearCechModuleDescentData_coverIso K L
    (RelatedTripleCoordinateScalarExtension L)
    (relatedTripleCoordinateGaloisSemilinearModuleAction K L diagram)

/-- The canonically selected base-field module descending the diagram-twisted
D4 related-triple coordinate module. -/
noncomputable def relatedTripleCoordinateGaloisDescendedModule
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) : ModuleCat K :=
  galoisSemilinearDescendedModule K L
    (RelatedTripleCoordinateScalarExtension L)
    (relatedTripleCoordinateGaloisSemilinearModuleAction K L diagram)

/-- Scalar extension of the canonical descended D4 module recovers the
scalar-extended related-triple coordinate module. -/
noncomputable def relatedTripleCoordinateGaloisDescendedModuleBaseChangeIso
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    (ModuleCat.extendScalars (algebraMap K L)).obj
        (relatedTripleCoordinateGaloisDescendedModule K L diagram) ≅
      relatedTripleCoordinateScalarExtensionModule L :=
  galoisSemilinearDescendedModuleBaseChangeIso K L
    (RelatedTripleCoordinateScalarExtension L)
    (relatedTripleCoordinateGaloisSemilinearModuleAction K L diagram)

/-- Finite-Galois diagram-twisted D4 coordinate-module descent is effective
without a supplied Čech datum or cover identification. -/
theorem relatedTripleCoordinateGaloisModuleDescent_effective
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    ∃ N : ModuleCat K,
      Nonempty ((ModuleCat.extendScalars (algebraMap K L)).obj N ≅
        relatedTripleCoordinateScalarExtensionModule L) :=
  ⟨relatedTripleCoordinateGaloisDescendedModule K L diagram,
    ⟨relatedTripleCoordinateGaloisDescendedModuleBaseChangeIso
      K L diagram⟩⟩

end

end RiemannResearch.AlgebraicGeometry
