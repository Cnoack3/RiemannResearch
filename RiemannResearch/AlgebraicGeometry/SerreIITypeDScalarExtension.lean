/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.FpqcH1ScalarExtension
import RiemannResearch.AlgebraicGeometry.SerreIITypeD

/-!
# Concrete field-extension data for the type-D reduction

This module adapts a typed family of finite field extensions and fpqc-H¹
scalar-extension maps to the restriction-data interface used by the
trialitarian zero-cycle reduction.

The adapter removes the former ambiguity about the local pointed sets and
degrees. It does not construct the scalar-extension maps themselves.
-/

namespace RiemannResearch.AlgebraicGeometry

universe u

noncomputable section

namespace SerreII.TrialitarianRestrictionData

/-- Regard a concrete fpqc-H¹ restriction system as the restriction data used
by the trialitarian zero-cycle and coprime-splitting reductions. -/
def ofFpqcH1RestrictionSystem
    (K A : Type u) [Field K] [CommRing A] [HopfAlgebra K A]
    (D : FpqcH1RestrictionSystem K A) :
    SerreII.TrialitarianRestrictionData
      (FpqcH1 (CommRingCat.of K) (CommRingCat.of A))
      (FpqcH1.neutral (CommRingCat.of K) (CommRingCat.of A)) where
  Extension := D.Index
  LocalClass i := baseChangedFpqcH1 K A (D.extension i)
  neutral i := FpqcH1.neutral
    (CommRingCat.of (D.extension i).Extension)
    (CommRingCat.of
      (affineGroupBaseChangeCoordinate K (D.extension i).Extension A))
  restrict i := (D.map i).toFun
  restrict_neutral i := (D.map i).map_neutral
  isFinite _ := True
  degree := D.degree

@[simp] theorem ofFpqcH1RestrictionSystem_degree
    (K A : Type u) [Field K] [CommRing A] [HopfAlgebra K A]
    (D : FpqcH1RestrictionSystem K A) (i : D.Index) :
    (ofFpqcH1RestrictionSystem K A D).degree i = D.degree i :=
  rfl

@[simp] theorem ofFpqcH1RestrictionSystem_restrict_neutral
    (K A : Type u) [Field K] [CommRing A] [HopfAlgebra K A]
    (D : FpqcH1RestrictionSystem K A) (i : D.Index) :
    (ofFpqcH1RestrictionSystem K A D).restrict i
        (FpqcH1.neutral (CommRingCat.of K) (CommRingCat.of A)) =
      (ofFpqcH1RestrictionSystem K A D).neutral i :=
  (D.map i).map_neutral

end SerreII.TrialitarianRestrictionData

end

end RiemannResearch.AlgebraicGeometry
