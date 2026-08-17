/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.AffineModuleComonadicBridge
import RiemannResearch.LinearAlgebra.RootSystem.D4ZornCoordinateTriality

/-!
# Effective module descent boundary for the D4 coordinate algebra

This module records the exact effective-descent consequence available once a
chosen Cech module descent datum has been constructed for the scalar-extended
split-Zorn related-triple coordinate algebra.

Faithful flatness alone then produces a K-module whose scalar extension is the
underlying L-module of the coordinate algebra. Finite-dimensionality and the
Galois condition are not needed for this effectiveness step; they belong in a
future construction of the Cech datum from the semilinear coordinate action.

No multiplication, unit, comultiplication, counit, antipode, Hopf identity, or
represented affine group scheme is descended here.
-/

open CategoryTheory

namespace RiemannResearch.AlgebraicGeometry

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

end

end RiemannResearch.AlgebraicGeometry
