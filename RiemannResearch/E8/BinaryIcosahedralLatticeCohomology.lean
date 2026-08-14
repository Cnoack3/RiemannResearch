/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Data.ZMod.Basic
import RiemannResearch.E8.BinaryIcosahedralAtlas

/-!
# Binary-icosahedral E8 lattice cohomology certificate

This module continues the integral ATLAS matrix calculation in
'BinaryIcosahedralAtlas'. It supplies an explicit degree-six binary-dihedral
subgroup in the same matrices, records the mod-two fixed-space cardinalities
for the full, degree-five, degree-six, and overlap generator packets, and gives
a small exact certificate that every mod-two cocycle for the projective
triangle presentation is a coboundary.

The matrices act on integral row vectors from the right. The associated left
action on mod-two column coordinates is inverse-transpose. Since 'A² = -1'
and 'B³ = 1', its generators are 'Aᵀ' and '(Bᵀ)²' modulo two.

The final matrix identities certify the calculation 'H¹(A5, E8/2E8) = 0' once
the standard '(2,3,5)' presentation and the identification of this matrix image
with the intended projective A5 row are supplied. They do not compute
field-valued torus cohomology and do not identify the other three binary TomLib
rows.

Source: user-provided Research Target 7.1 analysis and the committed ATLAS
matrices (14 August 2026); the source supports the computation and terminology.
-/

open Matrix

namespace RiemannResearch.E8.BinaryIcosahedralLatticeCohomology

open BinaryIcosahedralAtlas

/-- An order-five generator for an aligned binary-dihedral packet. -/
def binaryDihedralU : Mat8 := B * A * B * A

/-- An order-four generator for the same binary-dihedral packet. -/
def binaryDihedralI : Mat8 :=
  A * B * A * B * B * A * B * A * B * B * A

/-- The order-four generator is also the short stabilizer word 'w j'. -/
theorem binaryDihedralI_eq_wj :
    binaryDihedralI = w * j := by
  decide

/-- Exact matrix relations for the displayed 'Dic5' generator packet.

The last equality is the inverse-free form of
'i * u * i⁻¹ = u⁻¹', using 'i⁻¹ = i³' and 'u⁻¹ = u⁴'. -/
theorem binaryDihedral_relations :
    binaryDihedralU * binaryDihedralU * binaryDihedralU *
          binaryDihedralU * binaryDihedralU = (1 : Mat8) ∧
      binaryDihedralI * binaryDihedralI = -(1 : Mat8) ∧
      binaryDihedralI * binaryDihedralU *
          (binaryDihedralI * binaryDihedralI * binaryDihedralI) =
        binaryDihedralU * binaryDihedralU *
          binaryDihedralU * binaryDihedralU := by
  decide

abbrev F2 := ZMod 2
abbrev I16 := Fin 16
abbrev Vec8F2 := I8 → F2
abbrev Mat8F2 := Matrix I8 I8 F2

/-- Entrywise reduction of an integral E8 matrix modulo two. -/
def reduceModTwo (m : Mat8) : Mat8F2 :=
  fun i j => (m i j : F2)

/-- Right multiplication of a mod-two row vector by a matrix. -/
def rowMul (v : Vec8F2) (m : Mat8F2) : Vec8F2 :=
  fun j => ∑ i, v i * m i j

/-- Boolean fixedness under every matrix in a finite generator packet. -/
def fixedBy (gens : List Mat8) (v : Vec8F2) : Bool :=
  gens.all fun m => decide (rowMul v (reduceModTwo m) = v)

/-- All mod-two vectors fixed by a finite generator packet. -/
def fixedVectors (gens : List Mat8) : Finset Vec8F2 :=
  Finset.univ.filter fun v => fixedBy gens v

set_option maxHeartbeats 0 in
-- Exhaustive kernel reduction checks all 256 vectors against four packets.
set_option maxRecDepth 100000 in
/-- Exact mod-two fixed-space cardinalities for the binary packet.

The four cardinalities correspond to dimensions '0', '2', '0', and '4' for
the full '2.A5' packet, the displayed '2.A4' packet, the displayed 'Dic5'
packet, and their cyclic order-four overlap packet. -/
theorem binaryLattice_fixedModTwo_cardinalities :
    (fixedVectors [A, B]).card = 1 ∧
      (fixedVectors [w, j, r]).card = 4 ∧
      (fixedVectors [binaryDihedralU, binaryDihedralI]).card = 1 ∧
      (fixedVectors [binaryDihedralI]).card = 16 := by
  decide

/-! ## Projective mod-two cocycle calculation -/

/-- The projective order-two generator on column coordinates. -/
def aAction : Mat8F2 :=
  (reduceModTwo A).transpose

/-- The transpose of the integral order-three generator modulo two. -/
def bTranspose : Mat8F2 :=
  (reduceModTwo B).transpose

/-- The projective order-three generator on column coordinates.

This is inverse-transpose because the integral matrices act on rows from the
right. -/
def bAction : Mat8F2 :=
  bTranspose * bTranspose

/-- The product of the two projective generators. -/
def abAction : Mat8F2 :=
  aAction * bAction

/-- Fold a sixteen-coordinate cochain index into one eight-coordinate block. -/
def row8 (i : I16) : I8 :=
  ⟨i.val % 8, Nat.mod_lt _ (by decide)⟩

/-- The principal-cocycle map
'v ↦ ((a - 1)v, (b - 1)v)'. -/
def coboundaryMatrix : Matrix I16 I8 F2 :=
  fun i j =>
    if i.val < 8 then (aAction - 1) (row8 i) j
    else (bAction - 1) (row8 i) j

/-- The two nonvacuous triangle-relator constraints on generator values.

The upper block is '1 + a'; the lower block is '1 + b + b²'. The order-five
constraint is vacuous for this module by 'projective_ab_norm_zero'. -/
def relationMatrix : Matrix I16 I16 F2 :=
  fun i j =>
    if i.val < 8 then
      if j.val < 8 then (1 + aAction) (row8 i) (row8 j) else 0
    else
      if j.val < 8 then 0
      else (1 + bAction + bAction * bAction) (row8 i) (row8 j)

/-- A sparse mod-two matrix specified by the positions of its entries '1'. -/
def sparse {m n : ℕ} (support : List (ℕ × ℕ)) :
    Matrix (Fin m) (Fin n) F2 :=
  fun i j => if (i.val, j.val) ∈ support then 1 else 0

/-- An explicit potential for every cochain satisfying 'relationMatrix'. -/
def potentialMatrix : Matrix I8 I16 F2 := sparse [
  (0, 0), (0, 5), (0, 9),
  (1, 1), (1, 4), (1, 8),
  (2, 0), (2, 5), (2, 8), (2, 9),
  (3, 1), (3, 4), (3, 8), (3, 9),
  (4, 0), (4, 5), (4, 8), (4, 9), (4, 10),
  (5, 1), (5, 4), (5, 8), (5, 9), (5, 11),
  (6, 1), (6, 4), (6, 5), (6, 8), (6, 9), (6, 10),
  (7, 0), (7, 4), (7, 5), (7, 8), (7, 9), (7, 11)
]

/-- The explicit correction witnessing the projection identity below. -/
def correctionMatrix : Matrix I16 I16 F2 := sparse [
  (2, 1), (2, 4), (3, 0), (3, 5),
  (6, 0), (6, 1), (6, 4), (7, 0), (7, 1), (7, 5),
  (12, 8), (13, 9), (14, 14), (15, 15)
]

/-- The mod-two generators satisfy the '(2,3,5)' triangle relations. -/
theorem projective_triangle_relations :
    aAction * aAction = 1 ∧
      bAction * bAction * bAction = 1 ∧
      abAction * abAction * abAction * abAction * abAction = 1 := by
  decide

/-- The norm operator for the order-five generator vanishes on this module. -/
theorem projective_ab_norm_zero :
    1 + abAction + abAction * abAction +
          abAction * abAction * abAction +
          abAction * abAction * abAction * abAction = 0 := by
  decide

/-- Every principal cocycle satisfies the two relator constraints. -/
theorem projective_relation_coboundary_zero :
    relationMatrix * coboundaryMatrix = 0 := by
  decide

/-- The explicit potential is a left inverse to the principal-cocycle map. -/
theorem projective_potential_leftInverse :
    potentialMatrix * coboundaryMatrix = 1 := by
  decide

/-- Projection onto principal cocycles, modulo the relator constraints. -/
theorem projective_coboundary_projection :
    coboundaryMatrix * potentialMatrix =
      1 + correctionMatrix * relationMatrix := by
  decide

/-- Every projective generator-value pair satisfying the triangle cocycle
constraints is the principal cocycle of the displayed potential.

Together with 'projective_relation_coboundary_zero', this is the exact finite
linear-algebra certificate that the corresponding first cohomology vanishes. -/
theorem projectiveCocycle_has_potential
    (z : I16 → F2) (hz : relationMatrix.mulVec z = 0) :
    coboundaryMatrix.mulVec (potentialMatrix.mulVec z) = z := by
  rw [Matrix.mulVec_mulVec, projective_coboundary_projection]
  simp only [Matrix.add_mulVec, Matrix.one_mulVec]
  rw [← Matrix.mulVec_mulVec, hz]
  simp

end RiemannResearch.E8.BinaryIcosahedralLatticeCohomology
