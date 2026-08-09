/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.FieldTheory.Galois.Basic
import RiemannResearch.AlgebraicGeometry.FpqcCover

/-!
# Finite-Galois singleton fpqc covers

A finite Galois field extension determines the singleton fpqc cover used by
the Čech/Galois comparison.
-/

namespace RiemannResearch.AlgebraicGeometry

open CategoryTheory
universe u₁ v₁ w₁ x₁

noncomputable section

/-- The morphism Spec L → Spec K associated to a finite Galois field
extension. -/
def finiteGaloisCoverHom
    (K L : Type u₁) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    _root_.AlgebraicGeometry.Spec (CommRingCat.of L) ⟶
      _root_.AlgebraicGeometry.Spec (CommRingCat.of K) :=
  _root_.AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (algebraMap K L))

/-- A finite Galois field extension gives a singleton fpqc cover
Spec L → Spec K. Flatness, surjectivity, and quasi-compactness are supplied by
Mathlib from finite-dimensionality and affineness. -/
def finiteGaloisFpqcCover
    (K L : Type u₁) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    FpqcCover (CommRingCat.of K) PUnit :=
  FpqcCover.singleton (finiteGaloisCoverHom K L)

end

end RiemannResearch.AlgebraicGeometry
