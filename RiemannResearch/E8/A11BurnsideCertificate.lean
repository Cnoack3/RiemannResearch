/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Data.List.Sort

/-!
# A11 Burnside-gluing finite certificate

This module embeds the finite integer and permutation data produced by the
rerunnable GAP certificate in
`E8/Certificates/A11_BURNSIDE_GLUING_CERTIFICATE.md`.  It checks the two
Burnside restriction-kernel equations, the global orbit-degree mismatch,
the parity correction by odd centralizers, and the final simultaneous even
conjugators on both gauge groups.

The identification of these arrays with the specified `2.A5` coset actions
and subgroup classes remains at the external GAP-certificate boundary.  The
field-theoretic realization in PDF Corollary 6.28 is not asserted here.
-/

namespace RiemannResearch.E8.A11BurnsideCertificate

/-- Dot product used to check the integer restriction matrices. -/
def intDotProduct (xs ys : List ℤ) : ℤ :=
  (List.zipWith (fun x y => x * y) xs ys).sum

/-- Matrix-vector multiplication over the integers. -/
def intMatrixMulVec (matrix : List (List ℤ)) (vector : List ℤ) : List ℤ :=
  matrix.map fun row => intDotProduct row vector

/-- Orders indexing the transitive `2.A5`-orbit basis. -/
def groupSubgroupOrders : List ℕ :=
  [1, 2, 3, 4, 5, 6, 8, 10, 12, 20, 24, 120]

/-- Orders indexing the transitive `2.A4`-orbit basis. -/
def hSubgroupOrders : List ℕ := [1, 2, 3, 4, 6, 8, 24]

/-- Orders indexing the transitive `2.D10`-orbit basis. -/
def kSubgroupOrders : List ℕ := [1, 2, 4, 5, 10, 20]

/-- Restriction matrix from `2.A5` to the order-24 gauge group. -/
def hRestrictionMatrix : List (List ℤ) := [
  [5, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  [0, 5, 0, 2, 0, 1, 1, 1, 0, 0, 0, 0],
  [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0],
  [0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0],
  [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
]

/-- Restriction matrix from `2.A5` to the order-20 gauge group. -/
def kRestrictionMatrix : List (List ℤ) := [
  [6, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  [0, 6, 0, 2, 0, 2, 0, 1, 0, 0, 0, 0],
  [0, 0, 0, 2, 0, 0, 3, 0, 2, 1, 1, 0],
  [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1]
]

/-- The Burnside vector `[G/U12] + [G/G] - [G/U20] - [G/U24]`. -/
def burnsideKernelVector : List ℤ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, 1]

/-- Lean checks both displayed Burnside restriction relations entry by entry. -/
theorem burnsideRestriction_certificate :
    hRestrictionMatrix.length = hSubgroupOrders.length ∧
      kRestrictionMatrix.length = kSubgroupOrders.length ∧
      (hRestrictionMatrix.all fun row =>
        row.length = groupSubgroupOrders.length) ∧
      (kRestrictionMatrix.all fun row =>
        row.length = groupSubgroupOrders.length) ∧
      intMatrixMulVec hRestrictionMatrix burnsideKernelVector =
        [0, 0, 0, 0, 0, 0, 0] ∧
      intMatrixMulVec kRestrictionMatrix burnsideKernelVector =
        [0, 0, 0, 0, 0, 0] := by
  decide

/-- The orbit-degree packets of the two externally identified actions. -/
def xOrbitDegrees : List ℕ := [10, 1]
def yOrbitDegrees : List ℕ := [6, 5]

/-- Both actions have degree eleven, but their global orbit packets differ. -/
theorem actionOrbitData_certificate :
    xOrbitDegrees.sum = 11 ∧ yOrbitDegrees.sum = 11 ∧
      xOrbitDegrees ≠ yOrbitDegrees ∧
      (11 * 10 * 9 * 8 * 7 * 6 * 5 * 4 * 3 * 2 * 1) / 2 = 19958400 := by
  decide

/-- The degree of the printed permutation arrays. -/
def permutationDegree : ℕ := 11

/-- Identity permutation in zero-based image-list form. -/
def permutationIdentity : List ℕ := List.range permutationDegree

/-- Apply a zero-based image-list permutation, with an irrelevant fallback for
malformed certificates.  Validity is checked separately below. -/
def permutationApply (p : List ℕ) (i : ℕ) : ℕ :=
  p.getD i i

/-- GAP-compatible permutation multiplication:
`i ^ (p * q) = (i ^ p) ^ q`. -/
def permutationMul (p q : List ℕ) : List ℕ :=
  (List.range permutationDegree).map fun i =>
    permutationApply q (permutationApply p i)

/-- Conjugation `q⁻¹ * p * q` in image-list form. -/
def permutationConjugate (qInv p q : List ℕ) : List ℕ :=
  permutationMul (permutationMul qInv p) q

/-- Boolean validity check for an eleven-point image-list permutation. -/
def isFinitePermutation (p : List ℕ) : Bool :=
  p.length == permutationDegree && p.Nodup &&
    p.all fun i => i < permutationDegree

/-- Boolean inverse check. -/
def areInversePermutations (p q : List ℕ) : Bool :=
  permutationMul p q == permutationIdentity &&
    permutationMul q p == permutationIdentity

/-- Boolean simultaneous-conjugacy check for two generator lists. -/
def simultaneouslyConjugates
    (q qInv : List ℕ) (source target : List (List ℕ)) : Bool :=
  areInversePermutations q qInv &&
    source.map (permutationConjugate qInv · q) == target

/-- Inversion count of a printed image list. -/
def inversionCount : List ℕ → ℕ
  | [] => 0
  | x :: xs => xs.countP (fun y => y < x) + inversionCount xs

/-- Parity check for a printed image-list permutation. -/
def isEvenPermutation (p : List ℕ) : Bool :=
  inversionCount p % 2 == 0

/-- Images of the two chosen generators in the global `X)-action. -/
def rhoXGenerators : List (List ℕ) := [
  [2, 1, 0, 4, 3, 5, 7, 6, 9, 8, 10],
  [5, 2, 7, 0, 6, 3, 9, 1, 8, 4, 10]
]

/-- Images of the two chosen generators in the global `Y)-action. -/
def rhoYGenerators : List (List ℕ) := [
  [4, 5, 2, 3, 0, 1, 7, 6, 9, 8, 10],
  [1, 5, 4, 2, 3, 0, 8, 7, 10, 9, 6]
]

def hXGenerators : List (List ℕ) := [
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
  [9, 1, 7, 5, 3, 4, 0, 8, 2, 6, 10],
  [1, 6, 4, 8, 5, 2, 0, 3, 7, 9, 10]
]

def hYGenerators : List (List ℕ) := [
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
  [3, 2, 5, 4, 0, 1, 6, 7, 10, 8, 9],
  [2, 5, 3, 0, 1, 4, 6, 10, 8, 7, 9]
]

def hInitialConjugator : List ℕ := [9, 7, 2, 4, 3, 0, 10, 5, 1, 8, 6]
def hInitialConjugatorInv : List ℕ := [5, 8, 2, 4, 3, 7, 10, 1, 9, 0, 6]
def hOddCentralizer : List ℕ := [0, 1, 3, 2, 8, 7, 6, 5, 4, 9, 10]
def hEvenConjugator : List ℕ := [9, 7, 4, 2, 1, 5, 10, 0, 3, 8, 6]
def hEvenConjugatorInv : List ℕ := [7, 4, 3, 8, 2, 5, 10, 1, 9, 0, 6]

def kXGenerators : List (List ℕ) := [
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
  [3, 4, 2, 0, 1, 8, 6, 9, 5, 7, 10],
  [9, 4, 7, 0, 8, 1, 5, 3, 6, 2, 10]
]

def kYGenerators : List (List ℕ) := [
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
  [0, 2, 1, 3, 5, 4, 10, 8, 7, 9, 6],
  [0, 2, 4, 5, 3, 1, 8, 10, 7, 6, 9]
]

def kInitialConjugator : List ℕ := [7, 1, 9, 8, 2, 5, 3, 6, 4, 10, 0]
def kInitialConjugatorInv : List ℕ := [10, 1, 4, 6, 8, 5, 7, 0, 3, 2, 9]
def kOddCentralizer : List ℕ := [4, 3, 6, 1, 0, 7, 2, 5, 9, 8, 10]
def kEvenConjugator : List ℕ := [7, 1, 9, 8, 2, 5, 3, 6, 4, 10, 0]
def kEvenConjugatorInv : List ℕ := [10, 1, 4, 6, 8, 5, 7, 0, 3, 2, 9]

/-- All printed action generators are valid even permutations, as required for
the two homomorphisms to land in `A11`. -/
theorem globalActionGenerators_certificate :
    (rhoXGenerators ++ rhoYGenerators).all isFinitePermutation = true ∧
      (rhoXGenerators ++ rhoYGenerators).all isEvenPermutation = true := by
  decide

/-- Lean independently checks the complete local parity correction.  The
order-24 initial conjugator and its centralizer correction are both odd,
their product is the displayed even conjugator, and the final element
simultaneously conjugates all three printed generators.  The order-20
initial conjugator is already even; its source centralizer nevertheless also
contains the displayed odd element, as claimed in the PDF. -/
theorem localEvenConjugators_certificate :
    (hXGenerators ++ hYGenerators ++ kXGenerators ++ kYGenerators).all
        isFinitePermutation = true ∧
      [hInitialConjugator, hInitialConjugatorInv, hOddCentralizer,
        hEvenConjugator, hEvenConjugatorInv, kInitialConjugator,
        kInitialConjugatorInv, kOddCentralizer, kEvenConjugator,
        kEvenConjugatorInv].all isFinitePermutation = true ∧
      isEvenPermutation hInitialConjugator = false ∧
      isEvenPermutation hOddCentralizer = false ∧
      isEvenPermutation hEvenConjugator = true ∧
      simultaneouslyConjugates hInitialConjugator hInitialConjugatorInv
        hXGenerators hYGenerators = true ∧
      simultaneouslyConjugates hOddCentralizer hOddCentralizer
        hXGenerators hXGenerators = true ∧
      permutationMul hOddCentralizer hInitialConjugator =
        hEvenConjugator ∧
      simultaneouslyConjugates hEvenConjugator hEvenConjugatorInv
        hXGenerators hYGenerators = true ∧
      isEvenPermutation kInitialConjugator = true ∧
      isEvenPermutation kOddCentralizer = false ∧
      isEvenPermutation kEvenConjugator = true ∧
      simultaneouslyConjugates kInitialConjugator kInitialConjugatorInv
        kXGenerators kYGenerators = true ∧
      simultaneouslyConjugates kOddCentralizer kOddCentralizer
        kXGenerators kXGenerators = true ∧
      kInitialConjugator = kEvenConjugator ∧
      simultaneouslyConjugates kEvenConjugator kEvenConjugatorInv
        kXGenerators kYGenerators = true := by
  decide

end RiemannResearch.E8.A11BurnsideCertificate
