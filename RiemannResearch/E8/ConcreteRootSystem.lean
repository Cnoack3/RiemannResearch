/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E8.GroupSchemeFoundation

/-!
# A concrete finite certificate for the `E₈` root system

This file gives an explicit 240-element model of the `E₈` roots in doubled
Euclidean coordinates.

* 112 roots have two nonzero coordinates, each equal to `±2`;
* 128 roots have all coordinates equal to `±1`, with an even number of minus
  signs.

The eight simple roots use the same numbering as `CartanMatrix.E₈`.  Their
Gram matrix is `4 · CartanMatrix.E₈`, because all Euclidean coordinates have
been doubled.  An explicit integral coefficient extractor reconstructs every
root from the simple roots.

All finite certificates use kernel reduction through `decide`; no
`native_decide`, external certificate, or provider proposition is used.
-/

namespace RiemannResearch
namespace E8
namespace ConcreteRootSystem

/-- Parameters for the 112 roots of the form `±2eᵢ ± 2eⱼ`, with `i < j`. -/
abbrev IntegerRootParam :=
  {p : (Fin 8 × Fin 8) × (Bool × Bool) // p.1.1 < p.1.2}

/-- Number of negative coordinates in a Boolean sign vector. -/
def minusCount (s : Fin 8 → Bool) : Nat :=
  (Finset.univ.filter fun i => s i).card

/-- Parameters for the 128 half-integral roots in doubled coordinates. -/
abbrev HalfRootParam :=
  {s : Fin 8 → Bool // minusCount s % 2 = 0}

/-- The concrete finite root type. -/
abbrev Root := IntegerRootParam ⊕ HalfRootParam

/-- Doubled Euclidean coordinate vectors. -/
abbrev Vector := Fin 8 → ℤ

/-- Interpret a Boolean as a sign: `false` is positive and `true` negative. -/
def signed (n : ℤ) (b : Bool) : ℤ :=
  if b then -n else n

/-- Doubled coordinates of an integer root. -/
def integerRootVector (p : IntegerRootParam) : Vector := fun k =>
  if k = p.1.1.1 then signed 2 p.1.2.1
  else if k = p.1.1.2 then signed 2 p.1.2.2
  else 0

/-- Doubled coordinates of a half-integral root. -/
def halfRootVector (p : HalfRootParam) : Vector := fun k =>
  signed 1 (p.1 k)

/-- Doubled Euclidean coordinates of a concrete root. -/
def rootVector : Root → Vector
  | Sum.inl p => integerRootVector p
  | Sum.inr p => halfRootVector p

/-- Euclidean dot product in doubled coordinates. -/
def dot (x y : Vector) : ℤ :=
  ∑ i, x i * y i

set_option maxRecDepth 100000 in
/-- There are exactly 112 integer roots. -/
theorem card_integerRootParam :
    Fintype.card IntegerRootParam = 112 := by
  decide

set_option maxRecDepth 100000 in
/-- There are exactly 128 half-integral roots. -/
theorem card_halfRootParam :
    Fintype.card HalfRootParam = 128 := by
  decide

set_option maxRecDepth 100000 in
/-- The concrete root type has exactly 240 elements. -/
theorem card_root :
    Fintype.card Root = 240 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Distinct root parameters give distinct Euclidean vectors. -/
theorem rootVector_injective :
    Function.Injective rootVector := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Every doubled root has squared norm `8`, corresponding to norm `2` before
doubling. -/
theorem rootVector_norm :
    ∀ r : Root, dot (rootVector r) (rootVector r) = 8 := by
  decide

/-- The eight simple roots in the numbering of `CartanMatrix.E₈`. -/
def simpleRoot : Fin 8 → Vector := ![
  ![1, -1, -1, -1, -1, -1, -1, 1],
  ![2, 2, 0, 0, 0, 0, 0, 0],
  ![-2, 2, 0, 0, 0, 0, 0, 0],
  ![0, -2, 2, 0, 0, 0, 0, 0],
  ![0, 0, -2, 2, 0, 0, 0, 0],
  ![0, 0, 0, -2, 2, 0, 0, 0],
  ![0, 0, 0, 0, -2, 2, 0, 0],
  ![0, 0, 0, 0, 0, -2, 2, 0]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The concrete simple-root Gram matrix is the repository's `E₈` Cartan
matrix, scaled by four because the coordinates are doubled. -/
theorem simpleRoot_gram :
    ∀ i j : Fin 8,
      dot (simpleRoot i) (simpleRoot j) =
        4 * CartanMatrix.E₈ i j := by
  decide

/-- Linear combination of the concrete simple roots. -/
def simpleCombination (c : Vector) : Vector := fun k =>
  ∑ i, c i * simpleRoot i k

/-- Coefficients in the concrete simple-root basis. -/
def coefficients (v : Vector) : Vector := ![
  v 7,
  (v 0 + v 1 + v 2 + v 3 + v 4 + v 5 + v 6 + 5 * v 7) / 4,
  (-v 0 + v 1 + v 2 + v 3 + v 4 + v 5 + v 6 + 7 * v 7) / 4,
  (v 2 + v 3 + v 4 + v 5 + v 6 + 5 * v 7) / 2,
  (v 3 + v 4 + v 5 + v 6 + 4 * v 7) / 2,
  (v 4 + v 5 + v 6 + 3 * v 7) / 2,
  (v 5 + v 6 + 2 * v 7) / 2,
  (v 6 + v 7) / 2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- Every concrete root has integral simple-root coefficients, and the
explicit coefficient extractor reconstructs it. -/
theorem simpleCombination_coefficients_root :
    ∀ r : Root,
      simpleCombination (coefficients (rootVector r)) = rootVector r := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The coefficient extractor sends the simple roots to the standard basis. -/
theorem coefficients_simpleRoot :
    ∀ i j : Fin 8,
      coefficients (simpleRoot i) j = if i = j then 1 else 0 := by
  decide

/-- A root is positive when all coefficients in the fixed simple-root basis
are nonnegative. -/
def IsPositive (r : Root) : Prop :=
  ∀ i : Fin 8, 0 ≤ coefficients (rootVector r) i

instance isPositiveDecidable (r : Root) : Decidable (IsPositive r) :=
  Fintype.decidableForallFintype

/-- The finite set of positive roots determined by the displayed simple
roots. -/
def positiveRoots : Finset Root :=
  Finset.univ.filter IsPositive

/-- Height in the fixed simple-root basis. -/
def height (r : Root) : ℤ :=
  ∑ i, coefficients (rootVector r) i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Exactly half of the 240 concrete roots are positive. -/
theorem card_positiveRoots :
    positiveRoots.card = 120 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Positive-root heights range from one through twenty-nine. -/
theorem positive_height_bounds :
    ∀ r : Root, IsPositive r → 1 ≤ height r ∧ height r ≤ 29 := by
  decide

/-- Multiplicity of each positive-root height, indexed by heights `1, …, 29`. -/
def heightMultiplicity : Fin 29 → Nat :=
  ![8, 7, 7, 7, 7, 7, 7, 6, 6, 6, 6, 5, 5, 4, 4, 4, 4,
    3, 3, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Complete height distribution of the 120 positive roots. -/
theorem positive_height_distribution :
    ∀ h : Fin 29,
      (positiveRoots.filter fun r =>
        height r = Int.ofNat (h.val + 1)).card = heightMultiplicity h := by
  decide

/-- The highest root in the repository's `CartanMatrix.E₈` numbering. -/
def highestRoot : Root :=
  Sum.inl ⟨(((6 : Fin 8), (7 : Fin 8)), (false, false)), by decide⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- The corrected highest-root coefficient vector is
`(2,3,4,6,5,4,3,2)`. -/
theorem highestRoot_coefficients :
    coefficients (rootVector highestRoot) =
      ![2, 3, 4, 6, 5, 4, 3, 2] := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- The displayed highest root is the unique positive root of height 29. -/
theorem highestRoot_unique_maximum :
    ∀ r : Root, IsPositive r → (height r = 29 ↔ r = highestRoot) := by
  decide

/-- The root attached to the coefficient vector previously displayed as the
highest root. -/
def previouslyMislabelledRoot : Root :=
  Sum.inl ⟨(((2 : Fin 8), (7 : Fin 8)), (false, false)), by decide⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- The previously displayed vector is indeed an E8 root, but its height is
only 25. -/
theorem previouslyMislabelledRoot_coefficients :
    coefficients (rootVector previouslyMislabelledRoot) =
      ![2, 3, 4, 6, 4, 3, 2, 1] := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem previouslyMislabelledRoot_height :
    height previouslyMislabelledRoot = 25 := by
  decide

set_option maxRecDepth 100000 in
theorem previouslyMislabelledRoot_ne_highestRoot :
    previouslyMislabelledRoot ≠ highestRoot := by
  decide

end ConcreteRootSystem
end E8
end RiemannResearch
