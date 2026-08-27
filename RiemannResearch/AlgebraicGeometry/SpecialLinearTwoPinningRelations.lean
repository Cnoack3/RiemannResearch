/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.SpecialLinearTwoCorootHopf

/-!
# Integral rank-one pinning relations

This file proves the standard rank-one Chevalley/Steinberg identities for the
genuine integral root subgroups and coroot already constructed in `SL₂`.

For every commutative ring `S`, the positive and negative root subgroups are
conjugated by the diagonal coroot with weights `2` and `-2`.  The usual Weyl
representative

`n(u) = x₊(u) x₋(-u⁻¹) x₊(u)`

is constructed, identified with the matrix `[[0,u],[-u⁻¹,0]]`, proved natural
under arbitrary base change, and shown to satisfy the expected coroot and
root-conjugation relations.

These are actual identities in `SL₂(S)`; no supplied pinning interface or
unproved declaration is used.  They are the rank-one relations needed by a
future genuine Chevalley construction.  This file does not yet construct the
split E8 group scheme.
-/

namespace RiemannResearch
namespace AlgebraicGeometry
namespace SpecialLinearTwoPinning

open ChevalleyRankOne
open SpecialLinearTwoCoroot

noncomputable section

variable (S : Type) [CommRing S]

/-- Inversion of the diagonal coroot is computed in the source torus. -/
@[simp] theorem diagonalCoroot_inv (u : Sˣ) :
    (diagonalCoroot S u)⁻¹ = diagonalCoroot S (u⁻¹) := by
  exact (map_inv (diagonalCoroot S) u).symm

/-- The positive root has coroot weight `2`. -/
theorem diagonalCoroot_conj_positive (u : Sˣ) (t : S) :
    diagonalCoroot S u * positiveRoot S (Multiplicative.ofAdd t) *
        (diagonalCoroot S u)⁻¹ =
      positiveRoot S (Multiplicative.ofAdd ((u : S) ^ 2 * t)) := by
  rw [diagonalCoroot_inv]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  change
    ((!![(u : S), 0; 0, (↑(u⁻¹) : S)] *
          Matrix.transvection (0 : Fin 2) 1 t) *
        !![(↑(u⁻¹) : S), 0; 0, (u : S)]) i j =
      (Matrix.transvection (0 : Fin 2) 1 ((u : S) ^ 2 * t)) i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.transvection, Matrix.single, pow_two]
  all_goals ring

/-- The negative root has coroot weight `-2`. -/
theorem diagonalCoroot_conj_negative (u : Sˣ) (t : S) :
    diagonalCoroot S u * negativeRoot S (Multiplicative.ofAdd t) *
        (diagonalCoroot S u)⁻¹ =
      negativeRoot S
        (Multiplicative.ofAdd ((↑(u⁻¹) : S) ^ 2 * t)) := by
  rw [diagonalCoroot_inv]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  change
    ((!![(u : S), 0; 0, (↑(u⁻¹) : S)] *
          Matrix.transvection (1 : Fin 2) 0 t) *
        !![(↑(u⁻¹) : S), 0; 0, (u : S)]) i j =
      (Matrix.transvection (1 : Fin 2) 0
        ((↑(u⁻¹) : S) ^ 2 * t)) i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.transvection, Matrix.single, pow_two]
  all_goals ring

/-- The standard Weyl representative built from the two integral root
subgroups. -/
def weylPoint (u : Sˣ) : ChevalleyRankOne.SL2 S :=
  positiveRoot S (Multiplicative.ofAdd (u : S)) *
    negativeRoot S (Multiplicative.ofAdd (-(↑(u⁻¹) : S))) *
    positiveRoot S (Multiplicative.ofAdd (u : S))

/-- The root-subgroup factorization has the standard antidiagonal matrix. -/
@[simp] theorem weylPoint_matrix (u : Sˣ) :
    ((weylPoint S u : ChevalleyRankOne.SL2 S) :
        Matrix (Fin 2) (Fin 2) S) =
      !![0, (u : S); -(↑(u⁻¹) : S), 0] := by
  unfold weylPoint
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  change
    ((Matrix.transvection (0 : Fin 2) 1 (u : S) *
        Matrix.transvection (1 : Fin 2) 0 (-(↑(u⁻¹) : S))) *
      Matrix.transvection (0 : Fin 2) 1 (u : S)) i j = _
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.transvection, Matrix.single]

/-- The Weyl representative commutes with arbitrary base change. -/
theorem weylPoint_natural
    {T : Type} [CommRing T] (f : S →+* T) (u : Sˣ) :
    Matrix.SpecialLinearGroup.map f (weylPoint S u) =
      weylPoint T (Units.map f.toMonoidHom u) := by
  unfold weylPoint
  rw [map_mul, map_mul]
  rw [positiveRoot_natural, negativeRoot_natural]
  congr 2 <;> apply Multiplicative.toAdd.injective <;> simp

/-- The inverse Weyl representative is obtained by negating its unit
parameter. -/
@[simp] theorem weylPoint_inv (u : Sˣ) :
    (weylPoint S u)⁻¹ = weylPoint S (-u) := by
  symm
  apply (mul_eq_one_iff_eq_inv).mp
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  rw [weylPoint_matrix]
  rw [Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The standard Steinberg formula `h(u) = n(u)n(-1)`. -/
theorem weylPoint_mul_negOne (u : Sˣ) :
    weylPoint S u * weylPoint S (-1 : Sˣ) = diagonalCoroot S u := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  rw [weylPoint_matrix, weylPoint_matrix]
  change
    ((!![0, (u : S); -(↑(u⁻¹) : S), 0] *
        !![0, (-1 : S); -((↑((-1 : Sˣ)⁻¹) : S)), 0]) i j) =
      (!![(u : S), 0; 0, (↑(u⁻¹) : S)] i j)
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Every Weyl representative squares to the central element `h(-1)`. -/
theorem weylPoint_sq (u : Sˣ) :
    weylPoint S u * weylPoint S u =
      diagonalCoroot S (-1 : Sˣ) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  rw [weylPoint_matrix]
  change
    ((!![0, (u : S); -(↑(u⁻¹) : S), 0] *
        !![0, (u : S); -(↑(u⁻¹) : S), 0]) i j) =
      (!![(-1 : S), 0; 0, (-1 : S)] i j)
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Weyl conjugation exchanges the positive and negative roots with the
standard parameter factor. -/
theorem weylPoint_conj_positive (u : Sˣ) (t : S) :
    weylPoint S u * positiveRoot S (Multiplicative.ofAdd t) *
        (weylPoint S u)⁻¹ =
      negativeRoot S
        (Multiplicative.ofAdd (-((↑(u⁻¹) : S) ^ 2 * t))) := by
  rw [weylPoint_inv]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  rw [weylPoint_matrix, weylPoint_matrix]
  change
    ((!![0, (u : S); -(↑(u⁻¹) : S), 0] *
          Matrix.transvection (0 : Fin 2) 1 t) *
        !![0, (-u : S); -(↑((-u)⁻¹) : S), 0]) i j =
      (Matrix.transvection (1 : Fin 2) 0
        (-((↑(u⁻¹) : S) ^ 2 * t))) i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.transvection, Matrix.single, pow_two]
  all_goals ring

/-- The opposite Weyl conjugation formula. -/
theorem weylPoint_conj_negative (u : Sˣ) (t : S) :
    weylPoint S u * negativeRoot S (Multiplicative.ofAdd t) *
        (weylPoint S u)⁻¹ =
      positiveRoot S
        (Multiplicative.ofAdd (-((u : S) ^ 2 * t))) := by
  rw [weylPoint_inv]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  rw [weylPoint_matrix, weylPoint_matrix]
  change
    ((!![0, (u : S); -(↑(u⁻¹) : S), 0] *
          Matrix.transvection (1 : Fin 2) 0 t) *
        !![0, (-u : S); -(↑((-u)⁻¹) : S), 0]) i j =
      (Matrix.transvection (0 : Fin 2) 1
        (-((u : S) ^ 2 * t))) i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.transvection, Matrix.single, pow_two]
  all_goals ring

end

end SpecialLinearTwoPinning
end AlgebraicGeometry
end RiemannResearch
