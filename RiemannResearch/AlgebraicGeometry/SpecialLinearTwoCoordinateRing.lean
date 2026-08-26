/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# The integral coordinate ring of split `SL₂`

This file constructs the affine coordinate ring

`ℤ[a,b,c,d] / (ad - bc - 1)`

using the determinant of the generic `2 × 2` matrix.  It then proves the
set-valued representability equivalence

`(Coordinate →+* R) ≃ SL₂(R)`

for every commutative ring `R`, together with naturality under base change.

This module stops before installing the cogroup and Hopf-algebra maps.
-/

namespace RiemannResearch
namespace AlgebraicGeometry
namespace SpecialLinearTwo

noncomputable section

universe u v

/-- The four matrix-entry variables. -/
abbrev Variable := Fin 2 × Fin 2

/-- Polynomial algebra on the four entries of a generic `2 × 2` matrix. -/
abbrev Polynomial := MvPolynomial Variable ℤ

/-- The generic `2 × 2` matrix. -/
def genericMatrix : Matrix (Fin 2) (Fin 2) Polynomial :=
  fun i j => MvPolynomial.X (i, j)

/-- The single determinant-one relation. -/
def determinantRelation : Polynomial :=
  Matrix.det genericMatrix - 1

/-- The ideal cutting out `SL₂` inside affine four-space. -/
def determinantIdeal : Ideal Polynomial :=
  Ideal.span ({determinantRelation} : Set Polynomial)

/-- Integral coordinate ring of split `SL₂`. -/
abbrev Coordinate := Polynomial ⧸ determinantIdeal

/-- Quotient map to the `SL₂` coordinate ring. -/
def quotient : Polynomial →+* Coordinate :=
  Ideal.Quotient.mk determinantIdeal

/-- Generic determinant-one matrix over the coordinate ring. -/
def universalMatrix : Matrix (Fin 2) (Fin 2) Coordinate :=
  quotient.mapMatrix genericMatrix

/-- The universal matrix has determinant one in the quotient. -/
theorem universalMatrix_det : Matrix.det universalMatrix = 1 := by
  have hmem : determinantRelation ∈ determinantIdeal :=
    Ideal.subset_span (Set.mem_singleton determinantRelation)
  have hz : quotient determinantRelation = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rw [determinantRelation, map_sub, map_one] at hz
  have hmap := quotient.map_det genericMatrix
  change quotient (Matrix.det genericMatrix) =
    Matrix.det universalMatrix at hmap
  rw [hmap] at hz
  exact sub_eq_zero.mp hz

/-- The tautological `SL₂`-point over its coordinate ring. -/
def universalPoint : Matrix.SpecialLinearGroup (Fin 2) Coordinate :=
  ⟨universalMatrix, universalMatrix_det⟩

/-- Evaluation of the polynomial algebra at an `SL₂`-point. -/
def polynomialEvaluation
    {R : Type u} [CommRing R]
    (g : Matrix.SpecialLinearGroup (Fin 2) R) : Polynomial →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R)
    (fun ij => (g : Matrix (Fin 2) (Fin 2) R) ij.1 ij.2)

theorem polynomialEvaluation_genericMatrix
    {R : Type u} [CommRing R]
    (g : Matrix.SpecialLinearGroup (Fin 2) R) :
    (polynomialEvaluation g).mapMatrix genericMatrix =
      (g : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  simp [genericMatrix, polynomialEvaluation]

theorem polynomialEvaluation_determinantRelation
    {R : Type u} [CommRing R]
    (g : Matrix.SpecialLinearGroup (Fin 2) R) :
    polynomialEvaluation g determinantRelation = 0 := by
  rw [determinantRelation, map_sub, map_one, sub_eq_zero]
  rw [(polynomialEvaluation g).map_det]
  rw [polynomialEvaluation_genericMatrix g]
  exact g.prop

theorem determinantIdeal_le_evaluationKer
    {R : Type u} [CommRing R]
    (g : Matrix.SpecialLinearGroup (Fin 2) R) :
    determinantIdeal ≤ RingHom.ker (polynomialEvaluation g) := by
  rw [determinantIdeal, Ideal.span_le]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst x
  exact polynomialEvaluation_determinantRelation g

/-- Evaluation of the quotient coordinate ring at an `SL₂`-point. -/
def coordinateEvaluation
    {R : Type u} [CommRing R]
    (g : Matrix.SpecialLinearGroup (Fin 2) R) : Coordinate →+* R :=
  Ideal.Quotient.lift determinantIdeal (polynomialEvaluation g)
    (fun _ hx => determinantIdeal_le_evaluationKer g hx)

@[simp]
theorem coordinateEvaluation_quotient_X
    {R : Type u} [CommRing R]
    (g : Matrix.SpecialLinearGroup (Fin 2) R) (i j : Fin 2) :
    coordinateEvaluation g (quotient (MvPolynomial.X (i, j))) =
      (g : Matrix (Fin 2) (Fin 2) R) i j := by
  simp [coordinateEvaluation, quotient, polynomialEvaluation]

/-- Evaluating the universal point recovers the supplied `SL₂`-point. -/
theorem coordinateEvaluation_universal
    {R : Type u} [CommRing R]
    (g : Matrix.SpecialLinearGroup (Fin 2) R) :
    Matrix.SpecialLinearGroup.map (coordinateEvaluation g) universalPoint =
      g := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change coordinateEvaluation g (quotient (MvPolynomial.X (i, j))) =
    (g : Matrix (Fin 2) (Fin 2) R) i j
  exact coordinateEvaluation_quotient_X g i j

/-- A coordinate-ring morphism is determined by the image of the universal
matrix. -/
theorem coordinateEvaluation_baseChange
    {R : Type u} [CommRing R]
    (f : Coordinate →+* R) :
    coordinateEvaluation
        (Matrix.SpecialLinearGroup.map f universalPoint) = f := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [coordinateEvaluation, polynomialEvaluation]
  · intro ij
    rcases ij with ⟨i, j⟩
    change coordinateEvaluation
        (Matrix.SpecialLinearGroup.map f universalPoint)
          (quotient (MvPolynomial.X (i, j))) =
      f (quotient (MvPolynomial.X (i, j)))
    rw [coordinateEvaluation_quotient_X]
    rfl

/-- Ring morphisms from the integral coordinate algebra are naturally
identified with `SL₂`-points. -/
def coordinateRingHomEquiv
    (R : Type u) [CommRing R] :
    (Coordinate →+* R) ≃ Matrix.SpecialLinearGroup (Fin 2) R where
  toFun f := Matrix.SpecialLinearGroup.map f universalPoint
  invFun := coordinateEvaluation
  left_inv := coordinateEvaluation_baseChange
  right_inv := coordinateEvaluation_universal

/-- The representability equivalence commutes with base change. -/
@[simp]
theorem coordinateRingHomEquiv_naturality
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (φ : Coordinate →+* R) :
    coordinateRingHomEquiv S (f.comp φ) =
      Matrix.SpecialLinearGroup.map f (coordinateRingHomEquiv R φ) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rfl

end

end SpecialLinearTwo
end AlgebraicGeometry
end RiemannResearch
