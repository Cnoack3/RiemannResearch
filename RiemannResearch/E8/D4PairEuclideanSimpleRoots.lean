/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E8.GroupSchemeFoundation
import RiemannResearch.LinearAlgebra.RootSystem.D4PairDiscriminant

/-!
# Explicit E8 simple roots in diagonal D4-by-D4 glue

This file checks the eight Euclidean-coordinate roots supplied by the
D4-by-D4 handoff. Coordinates are doubled in `scaledSimpleRoots`, making the
four diagonal glue cosets visible by parity and by the coordinate sum modulo
four. The first row is in the diagonal `S-` coset, the sixth is in the
diagonal vector coset, and the other six are in the base lattice.

The rows have Gram matrix the Bourbaki E8 Cartan matrix and have an explicit
rational inverse, so they form a basis. The coordinate name `S-` is a
convention fixed here by odd doubled coordinates whose sum is
two modulo four; swapping the two spinor names does not change the diagonal
graph.

This is an exact root-datum certificate. It does not construct an embedding
of group schemes, a torsor reduction, or a proof of Serre II.
-/

open Matrix

namespace RiemannResearch.E8.D4PairEuclideanSimpleRoots

open RiemannResearch.LinearAlgebra.RootSystem.D4Triality

abbrev Mat8Q := Matrix (Fin 8) (Fin 8) ℚ
abbrev Mat8Z := Matrix (Fin 8) (Fin 8) ℤ

/-- Twice the eight Euclidean simple roots, so every entry is integral. -/
def scaledSimpleRoots : Mat8Z := ![
  ![1,-1,-1,-1,-1,-1,-1,1],
  ![2,2,0,0,0,0,0,0],
  ![-2,2,0,0,0,0,0,0],
  ![0,-2,2,0,0,0,0,0],
  ![0,0,-2,2,0,0,0,0],
  ![0,0,0,-2,2,0,0,0],
  ![0,0,0,0,-2,2,0,0],
  ![0,0,0,0,0,-2,2,0]]

/-- The eight displayed Euclidean simple roots. -/
def simpleRoots : Mat8Q :=
  fun i j => (scaledSimpleRoots i j : ℚ) / 2

/-- The standard coordinate test for one D4 dual-lattice coset after scaling
coordinates by two. `none` denotes the base root lattice. -/
def halfCoset (label : Option TrialityLabel) (a b c d : ℤ) : Prop :=
  match label with
  | none =>
      a % 2 = 0 ∧ b % 2 = 0 ∧ c % 2 = 0 ∧ d % 2 = 0 ∧
        (a + b + c + d) % 4 = 0
  | some .vector =>
      a % 2 = 0 ∧ b % 2 = 0 ∧ c % 2 = 0 ∧ d % 2 = 0 ∧
        (a + b + c + d) % 4 = 2
  | some .halfSpinPlus =>
      a % 2 = 1 ∧ b % 2 = 1 ∧ c % 2 = 1 ∧ d % 2 = 1 ∧
        (a + b + c + d) % 4 = 0
  | some .halfSpinMinus =>
      a % 2 = 1 ∧ b % 2 = 1 ∧ c % 2 = 1 ∧ d % 2 = 1 ∧
        (a + b + c + d) % 4 = 2

private instance halfCosetDecidable
    (label : Option TrialityLabel) (a b c d : ℤ) :
    Decidable (halfCoset label a b c d) := by
  unfold halfCoset
  split <;> infer_instance

/-- Both D4 halves of a scaled coordinate vector have the same glue label. -/
def pairCoset (label : Option TrialityLabel) (x : Fin 8 → ℤ) : Prop :=
  halfCoset label (x 0) (x 1) (x 2) (x 3) ∧
    halfCoset label (x 4) (x 5) (x 6) (x 7)

private instance pairCosetDecidable
    (label : Option TrialityLabel) (x : Fin 8 → ℤ) :
    Decidable (pairCoset label x) := by
  unfold pairCoset
  infer_instance

/-- Glue labels of the eight rows: spinor, four base roots, vector bridge,
then two base roots. -/
def simpleRootGlueLabel : Fin 8 → Option TrialityLabel :=
  ![some .halfSpinMinus, none, none, none, none, some .vector, none, none]

/-- The pair discriminant class named by one diagonal glue label. -/
def graphClass : Option TrialityLabel → PairDiscriminantGroup
  | none => 0
  | some label => (fundamentalClass label, fundamentalClass label)

/-- Every diagonal glue label belongs to the identity discriminant graph. -/
theorem graphClass_mem_identityGraph (label : Option TrialityLabel) :
    graphClass label ∈ discriminantGraph 1 := by
  cases label with
  | none => exact (discriminantGraph 1).zero_mem
  | some label =>
      rw [mem_discriminantGraph_iff]
      change fundamentalClass label =
        discriminantAction 1 (fundamentalClass label)
      rw [map_one]
      simp

set_option maxHeartbeats 0 in
-- Exhaustively reducing the eight finite coordinate cases needs no heartbeat bound.
/-- The eight rows lie in the claimed diagonal D4-by-D4 coordinate cosets. -/
theorem simpleRoots_pairCoset :
    ∀ i, pairCoset (simpleRootGlueLabel i) (scaledSimpleRoots i) := by
  intro i
  fin_cases i <;> decide

/-- The abstract discriminant class assigned to every row lies in the
identity graph. -/
theorem simpleRoots_graphClass_mem_identityGraph (i : Fin 8) :
    graphClass (simpleRootGlueLabel i) ∈ discriminantGraph 1 :=
  graphClass_mem_identityGraph _

/-- An explicit inverse for the displayed simple-root matrix. -/
def simpleRootsInv : Mat8Q := ![
  ![0, 1/2, -1/2, 0, 0, 0, 0, 0],
  ![0, 1/2, 1/2, 0, 0, 0, 0, 0],
  ![0, 1/2, 1/2, 1, 0, 0, 0, 0],
  ![0, 1/2, 1/2, 1, 1, 0, 0, 0],
  ![0, 1/2, 1/2, 1, 1, 1, 0, 0],
  ![0, 1/2, 1/2, 1, 1, 1, 1, 0],
  ![0, 1/2, 1/2, 1, 1, 1, 1, 1],
  ![2, 5/2, 7/2, 5, 4, 3, 2, 1]]

set_option maxHeartbeats 0 in
-- The 64 explicit rational inner products need an unrestricted heartbeat budget.
/-- The displayed inner products are exactly the Bourbaki E8 Cartan matrix. -/
theorem simpleRoots_gram :
    simpleRoots * simpleRoots.transpose =
      CartanMatrix.E₈.map (Int.castRingHom ℚ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [simpleRoots, scaledSimpleRoots, Matrix.mul_apply, dotProduct,
      Fin.sum_univ_succ, CartanMatrix.E₈]

set_option maxHeartbeats 0 in
-- The 64 entries of the explicit inverse product are checked independently.
/-- The displayed inverse is a right inverse for the simple-root matrix. -/
theorem simpleRoots_mul_inverse :
    simpleRoots * simpleRootsInv = 1 := by
  ext i j
  simp only [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [simpleRoots, scaledSimpleRoots, simpleRootsInv, dotProduct,
      Fin.sum_univ_succ]

/-- The eight displayed roots form a basis over the rationals. -/
theorem simpleRoots_isUnit : IsUnit simpleRoots := by
  rw [isUnit_iff_exists_inv]
  exact ⟨simpleRootsInv, simpleRoots_mul_inverse⟩

/-- Combined finite certificate: diagonal glue membership, the E8 Gram
matrix, and an explicit basis certificate. -/
theorem identityGraphGlue_has_E8_simpleRootData :
    (∀ i, pairCoset (simpleRootGlueLabel i) (scaledSimpleRoots i)) ∧
    (∀ i, graphClass (simpleRootGlueLabel i) ∈ discriminantGraph 1) ∧
    simpleRoots * simpleRoots.transpose =
      CartanMatrix.E₈.map (Int.castRingHom ℚ) ∧
    IsUnit simpleRoots := by
  exact ⟨simpleRoots_pairCoset, simpleRoots_graphClass_mem_identityGraph,
    simpleRoots_gram, simpleRoots_isUnit⟩

end RiemannResearch.E8.D4PairEuclideanSimpleRoots
