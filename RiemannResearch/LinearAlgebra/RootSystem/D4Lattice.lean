/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.LinearAlgebra.RootSystem.D4Triality

/-!
# The based D4 root and weight lattices

This file gives the integral coordinate layer beneath both the type-D and E8
uses of D4 triality. In Mathlib's order `V, central, S+, S-`, both the
simple-root coordinates and the fundamental-weight coordinates are copies of
`Fin 4 → ℤ`. The Cartan matrix maps the former into the latter.

These are based lattice coordinates. The declarations do not construct
representations with the displayed highest weights, a Spin(8) group scheme, or
a lift of diagram triality to such a group scheme.
-/

open Matrix

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality

/-- Integral coordinates in the chosen simple-root basis. -/
abbrev RootCoordinates := Fin 4 → ℤ

/-- Integral coordinates in the chosen fundamental-weight basis. -/
abbrev WeightCoordinates := Fin 4 → ℤ

/-- A coordinate basis vector. -/
def coordinateVector (i : Fin 4) : WeightCoordinates :=
  Pi.single i 1

/-- A simple root written in simple-root coordinates. -/
abbrev simpleRootCoordinate := coordinateVector

/-- A fundamental weight written in fundamental-weight coordinates. -/
abbrev fundamentalWeightCoordinate := coordinateVector

/-- The D4 Cartan map from simple-root to fundamental-weight coordinates. -/
def cartanMap : RootCoordinates →+ WeightCoordinates where
  toFun := cartanFinFour.mulVec
  map_zero' := Matrix.mulVec_zero cartanFinFour
  map_add' := Matrix.mulVec_add cartanFinFour

@[simp]
theorem cartanMap_apply (x : RootCoordinates) :
    cartanMap x = ![
      2 * x 0 - x 1,
      -x 0 + 2 * x 1 - x 2 - x 3,
      -x 1 + 2 * x 2,
      -x 1 + 2 * x 3] := by
  rw [show cartanMap x = cartanFinFour.mulVec x from rfl,
    cartanFinFour_eq_mathlib]
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, CartanMatrix.D,
      Fin.sum_univ_succ] <;> ring

@[simp]
theorem cartanMap_simpleRootCoordinate (i j : Fin 4) :
    cartanMap (simpleRootCoordinate i) j = cartanFinFour j i := by
  change cartanFinFour.mulVec (Pi.single i 1) j = cartanFinFour j i
  rw [Matrix.mulVec_single_one]
  rfl

/-- The based D4 root sublattice inside the weight-coordinate lattice. -/
def rootSublattice : AddSubgroup WeightCoordinates :=
  cartanMap.range

theorem mem_rootSublattice_iff (x : WeightCoordinates) :
    x ∈ rootSublattice ↔ ∃ y : RootCoordinates, cartanMap y = x :=
  Iff.rfl

/-- The determinant of the D4 Cartan matrix is four. -/
theorem cartanFinFour_det : cartanFinFour.det = 4 := by
  rw [cartanFinFour_eq_mathlib]
  decide

/-- The three outer fundamental weights in the published
`V, central, S+, S-` order. These are weight vectors, not constructed
representations. -/
def outerFundamentalWeight : TrialityLabel → WeightCoordinates
  | .vector => ![1, 0, 0, 0]
  | .halfSpinPlus => ![0, 0, 1, 0]
  | .halfSpinMinus => ![0, 0, 0, 1]

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality
