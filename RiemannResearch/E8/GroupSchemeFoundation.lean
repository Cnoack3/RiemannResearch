import Mathlib.Algebra.Lie.SerreConstruction
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import RiemannResearch.AlgebraicGeometry.AffineGroupSchemeBaseChange

/-!
# Bounded foundations toward a split E8 group scheme

This file connects three pieces that are currently available in Mathlib:

* the abstract crystallographic root-datum interface;
* the explicit integral E8 Cartan matrix and its Serre Lie algebra;
* affine group schemes represented by commutative Hopf algebras.

The inverse matrix below is an exact, kernel-checked certificate that the E8
Cartan matrix is unimodular.  `BasedE8RootDatum` is an interface for a
*supplied* genuine root datum with an E8-labelled base; no inhabitant is
constructed here.

Crucially, this file does **not** construct the Chevalley coordinate Hopf
algebra, integrate the Serre Lie algebra, or prove smoothness and reductivity.
Thus it is a reusable foundation, not yet a reductive E8 group scheme.
-/

namespace RiemannResearch.E8

universe u v w

/-- A genuine reduced crystallographic root datum together with a chosen base
whose Cartan pairing is Mathlib's E8 Cartan matrix.

This structure is deliberately an interface: a value must supply all roots,
coroots, reflection axioms, finiteness, crystallographicity, and reducedness.
The eight chosen simple roots alone are not presented as a full root system.
-/
structure BasedE8RootDatum
    (ι : Type u) (X : Type v) (Y : Type w)
    [AddCommGroup X] [AddCommGroup Y] where
  datum : RootDatum ι X Y
  isRootSystem : datum.IsRootSystem
  isCrystallographic : datum.IsCrystallographic
  isReduced : datum.IsReduced
  base : datum.Base
  simpleEquiv : Fin 8 ≃ base.support
  cartan_eq : ∀ i j,
    datum.pairing (simpleEquiv i).1 (simpleEquiv j).1 =
      CartanMatrix.E₈ i j

namespace BasedE8RootDatum

/-- The matrix of pairings between the chosen simple roots and coroots. -/
def simpleCartanMatrix
    {ι : Type u} {X : Type v} {Y : Type w}
    [AddCommGroup X] [AddCommGroup Y]
    (D : BasedE8RootDatum ι X Y) :
    Matrix (Fin 8) (Fin 8) ℤ :=
  fun i j =>
    D.datum.pairing (D.simpleEquiv i).1 (D.simpleEquiv j).1

/-- The chosen simple-root pairing is exactly Mathlib's E8 Cartan matrix. -/
theorem simpleCartanMatrix_eq_E8
    {ι : Type u} {X : Type v} {Y : Type w}
    [AddCommGroup X] [AddCommGroup Y]
    (D : BasedE8RootDatum ι X Y) :
    D.simpleCartanMatrix = CartanMatrix.E₈ := by
  ext i j
  exact D.cartan_eq i j

/-- An E8-labelled base has exactly eight simple roots. -/
theorem simpleRootCount
    {ι : Type u} {X : Type v} {Y : Type w}
    [AddCommGroup X] [AddCommGroup Y]
    (D : BasedE8RootDatum ι X Y) :
    Fintype.card D.base.support = 8 := by
  rw [← Fintype.card_fin 8]
  exact Fintype.card_congr D.simpleEquiv.symm

/-- Every simple root has Cartan self-pairing two. -/
theorem simplePairing_self
    {ι : Type u} {X : Type v} {Y : Type w}
    [AddCommGroup X] [AddCommGroup Y]
    (D : BasedE8RootDatum ι X Y) (i : Fin 8) :
    D.datum.pairing (D.simpleEquiv i).1 (D.simpleEquiv i).1 = 2 := by
  rw [D.cartan_eq]
  exact CartanMatrix.E₈_diag i

/-- Mathlib's chosen E8 Cartan matrix is symmetric, hence so is the chosen
simple-root pairing. -/
theorem simplePairing_symm
    {ι : Type u} {X : Type v} {Y : Type w}
    [AddCommGroup X] [AddCommGroup Y]
    (D : BasedE8RootDatum ι X Y) (i j : Fin 8) :
    D.datum.pairing (D.simpleEquiv i).1 (D.simpleEquiv j).1 =
      D.datum.pairing (D.simpleEquiv j).1 (D.simpleEquiv i).1 := by
  rw [D.cartan_eq, D.cartan_eq]
  exact (CartanMatrix.E₈_isSymm.apply i j).symm

/-- Distinct simple roots have nonpositive Cartan pairing. -/
theorem simplePairing_offDiag_nonpos
    {ι : Type u} {X : Type v} {Y : Type w}
    [AddCommGroup X] [AddCommGroup Y]
    (D : BasedE8RootDatum ι X Y) {i j : Fin 8} (h : i ≠ j) :
    D.datum.pairing (D.simpleEquiv i).1 (D.simpleEquiv j).1 ≤ 0 := by
  rw [D.cartan_eq]
  exact CartanMatrix.E₈_off_diag_nonpos i j h

end BasedE8RootDatum

/-- An explicit integral inverse of Mathlib's E8 Cartan matrix. -/
def e8CartanInverse : Matrix (Fin 8) (Fin 8) ℤ :=
  !![4, 5, 7, 10, 8, 6, 4, 2;
     5, 8, 10, 15, 12, 9, 6, 3;
     7, 10, 14, 20, 16, 12, 8, 4;
     10, 15, 20, 30, 24, 18, 12, 6;
     8, 12, 16, 24, 20, 15, 10, 5;
     6, 9, 12, 18, 15, 12, 8, 4;
     4, 6, 8, 12, 10, 8, 6, 3;
     2, 3, 4, 6, 5, 4, 3, 2]

/-- Exact finite certificate: the displayed matrix is a right inverse. -/
theorem e8Cartan_mul_inverse :
    CartanMatrix.E₈ * e8CartanInverse = 1 := by
  decide

/-- Exact finite certificate: the displayed matrix is a left inverse. -/
theorem e8Cartan_inverse_mul :
    e8CartanInverse * CartanMatrix.E₈ = 1 := by
  decide

/-- The determinant of the E8 Cartan matrix is a unit in the integers. -/
theorem e8Cartan_det_isUnit : IsUnit CartanMatrix.E₈.det :=
  Matrix.isUnit_det_of_right_inverse e8Cartan_mul_inverse

/-- The E8 Cartan matrix is a unit in the matrix ring over the integers. -/
theorem e8Cartan_isUnit : IsUnit CartanMatrix.E₈ :=
  (Matrix.isUnit_iff_isUnit_det CartanMatrix.E₈).2 e8Cartan_det_isUnit

/-- The integral linear automorphism defined by the E8 Cartan matrix, with
inverse certified by `e8CartanInverse`. -/
noncomputable def e8CartanLinearEquiv :
    (Fin 8 → ℤ) ≃ₗ[ℤ] (Fin 8 → ℤ) :=
  Matrix.toLin'OfInv e8Cartan_mul_inverse e8Cartan_inverse_mul

/-- Stable local name for Mathlib's E8 Lie algebra defined by the Serre
presentation over a commutative ring. -/
abbrev e8SerreLieAlgebra (R : Type u) [CommRing R] :=
  LieAlgebra.e₈ R

/-- The local E8 Lie-algebra name unfolds to the Serre quotient attached to the
explicit E8 Cartan matrix. -/
theorem e8SerreLieAlgebra_eq_toLieAlgebra
    (R : Type u) [CommRing R] :
    e8SerreLieAlgebra R =
      Matrix.ToLieAlgebra R CartanMatrix.E₈ :=
  rfl

end RiemannResearch.E8
