/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import RiemannResearch.LinearAlgebra.RootSystem.D4ZornFiniteEquations

/-!
# A coordinate algebra for split-Zorn related triples

This module constructs the affine coordinate algebra cut out inside
`GL(8)^3` by the 728 coefficient residuals from
`D4ZornFiniteEquations`.

We present each general-linear factor by matrix variables together with
inverse-matrix variables and the equation `X * Y = 1`.  Square matrices
over a commutative ring form a Dedekind-finite monoid, so this one-sided
relation produces a unit.  We then quotient by all coefficient residuals.

The construction is universe-polymorphic: variables are lifted to the
universe of the target ring.  The universal point, the evaluation morphism
associated to every related triple, and mutually inverse maps

```
(RelatedTripleCoordinateRing →+* R) ≃ coefficientRelatedTripleGroup R
```

are constructed explicitly and proved natural in `R`. This is set-valued
representability. This module stops at that boundary: the compatible cogroup
maps and the resulting integral Hopf-algebra structure are supplied downstream
by `D4ZornCoordinateCogroup` and `D4ZornCoordinateHopf`, rather than
constructed here.
-/

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn

noncomputable section

universe u

/-- A ring map that kills the residuals of a matrix tuple sends it to a
solution of the coefficient equations. -/
theorem satisfies_map_of_residual_killed
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (g : MatrixTuple R)
    (h : ∀ e, f (relatedTripleCoefficientResidual g e) = 0) :
    SatisfiesRelatedTripleCoefficientEquations (matrixTupleMap f g) := by
  intro e
  exact (map_relatedTripleCoefficientResidual f g e).symm.trans (h e)

/-- Direct and inverse entries for three generic `8 × 8` matrices. -/
inductive RelatedTripleCoordinateVariable
  | matrix (l : TrialityLabel) (i j : Fin 8)
  | inverse (l : TrialityLabel) (i j : Fin 8)
  deriving DecidableEq

/-- Integral polynomial algebra on the direct and inverse matrix entries.
The `ULift` keeps the algebra in the same universe as a prospective
target ring. -/
abbrev RelatedTriplePolynomial :=
  MvPolynomial (ULift.{u} RelatedTripleCoordinateVariable) ℤ

def coordinateVariable (v : RelatedTripleCoordinateVariable) :
    ULift.{u} RelatedTripleCoordinateVariable :=
  ULift.up v

def genericMatrix (l : TrialityLabel) :
    Matrix (Fin 8) (Fin 8) RelatedTriplePolynomial :=
  fun i j => MvPolynomial.X (coordinateVariable (.matrix l i j))

def genericInverseMatrix (l : TrialityLabel) :
    Matrix (Fin 8) (Fin 8) RelatedTriplePolynomial :=
  fun i j => MvPolynomial.X (coordinateVariable (.inverse l i j))

/-- Entrywise equations saying that each direct matrix has the displayed
right inverse. -/
def generalLinearRelation
    (l : TrialityLabel) (i j : Fin 8) : RelatedTriplePolynomial :=
  (genericMatrix l * genericInverseMatrix l) i j -
    (1 : Matrix (Fin 8) (Fin 8) RelatedTriplePolynomial) i j

def generalLinearIdeal : Ideal RelatedTriplePolynomial :=
  Ideal.span (Set.range fun p : TrialityLabel × Fin 8 × Fin 8 =>
    generalLinearRelation p.1 p.2.1 p.2.2)

/-- Coordinate algebra of three general-linear matrices, before imposing
the norm and triality equations. -/
abbrev GeneralLinearCoordinateRing :=
  RelatedTriplePolynomial ⧸ generalLinearIdeal

def generalLinearQuotient :
    RelatedTriplePolynomial →+* GeneralLinearCoordinateRing :=
  Ideal.Quotient.mk generalLinearIdeal

def genericMatrixQuotient (l : TrialityLabel) :
    Matrix (Fin 8) (Fin 8) GeneralLinearCoordinateRing :=
  (genericMatrix l).map generalLinearQuotient

def genericInverseMatrixQuotient (l : TrialityLabel) :
    Matrix (Fin 8) (Fin 8) GeneralLinearCoordinateRing :=
  (genericInverseMatrix l).map generalLinearQuotient

theorem genericMatrix_mul_genericInverseMatrix (l : TrialityLabel) :
    genericMatrixQuotient l * genericInverseMatrixQuotient l = 1 := by
  ext i j
  have hmem : generalLinearRelation l i j ∈ generalLinearIdeal :=
    Ideal.subset_span (Set.mem_range_self (l, i, j))
  have hz : generalLinearQuotient (generalLinearRelation l i j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have hmul :
      generalLinearQuotient
          ((genericMatrix l * genericInverseMatrix l) i j) =
        (genericMatrixQuotient l * genericInverseMatrixQuotient l) i j := by
    have h := Matrix.map_mul
      (L := genericMatrix l) (M := genericInverseMatrix l)
      (f := generalLinearQuotient)
    exact congrFun (congrFun h i) j
  have hone :
      generalLinearQuotient
          ((1 : Matrix (Fin 8) (Fin 8) RelatedTriplePolynomial) i j) =
        (1 : Matrix (Fin 8) (Fin 8) GeneralLinearCoordinateRing) i j := by
    have h := Matrix.map_one (n := Fin 8)
      generalLinearQuotient (map_zero _) (map_one _)
    exact congrFun (congrFun h i) j
  rw [generalLinearRelation, map_sub, hmul, hone] at hz
  exact sub_eq_zero.mp hz

def genericMatrixUnit (l : TrialityLabel) :
    Matrix.GeneralLinearGroup (Fin 8) GeneralLinearCoordinateRing :=
  Units.mkOfMulEqOne (genericMatrixQuotient l)
    (genericInverseMatrixQuotient l)
    (genericMatrix_mul_genericInverseMatrix l)

@[simp] theorem genericMatrixUnit_inv_apply
    (l : TrialityLabel) (i j : Fin 8) :
    (↑((genericMatrixUnit l)⁻¹) :
        Matrix (Fin 8) (Fin 8) GeneralLinearCoordinateRing) i j =
      genericInverseMatrixQuotient l i j :=
  rfl

def genericMatrixTuple : MatrixTuple GeneralLinearCoordinateRing :=
  genericMatrixUnit

/-- The ideal generated by all 728 norm and triality residuals of the
generic general-linear triple. -/
def relatedTripleResidualIdeal : Ideal GeneralLinearCoordinateRing :=
  Ideal.span
    (Set.range (relatedTripleCoefficientResidual genericMatrixTuple))

/-- The explicit integral coordinate algebra of coefficient-related
triples. -/
abbrev RelatedTripleCoordinateRing :=
  GeneralLinearCoordinateRing ⧸ relatedTripleResidualIdeal

def relatedTripleCoordinateQuotient :
    GeneralLinearCoordinateRing →+* RelatedTripleCoordinateRing :=
  Ideal.Quotient.mk relatedTripleResidualIdeal

def universalRelatedTripleMatrixTuple :
    MatrixTuple RelatedTripleCoordinateRing :=
  matrixTupleMap relatedTripleCoordinateQuotient genericMatrixTuple

theorem universalRelatedTripleMatrixTuple_satisfies :
    SatisfiesRelatedTripleCoefficientEquations
      universalRelatedTripleMatrixTuple := by
  unfold universalRelatedTripleMatrixTuple
  apply satisfies_map_of_residual_killed
  intro e
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_range_self e))

/-- The tautological coefficient-related triple over its coordinate
algebra. -/
def universalCoefficientRelatedTriple :
    coefficientRelatedTripleGroup RelatedTripleCoordinateRing :=
  ⟨universalRelatedTripleMatrixTuple,
    universalRelatedTripleMatrixTuple_satisfies⟩

/-- Values assigned to direct variables and displayed inverse variables
by a matrix tuple. -/
def coordinateAssignment
    {R : Type u} [CommRing R] (g : MatrixTuple R) :
    ULift.{u} RelatedTripleCoordinateVariable → R
  | ⟨.matrix l i j⟩ =>
      (g l : Matrix (Fin 8) (Fin 8) R) i j
  | ⟨.inverse l i j⟩ =>
      ((g l)⁻¹ : Matrix.GeneralLinearGroup (Fin 8) R) i j

def polynomialEvaluation
    {R : Type u} [CommRing R] (g : MatrixTuple R) :
    RelatedTriplePolynomial →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R) (coordinateAssignment g)

theorem polynomialEvaluation_generalLinearRelation
    {R : Type u} [CommRing R] (g : MatrixTuple R)
    (l : TrialityLabel) (i j : Fin 8) :
    polynomialEvaluation g (generalLinearRelation l i j) = 0 := by
  rw [generalLinearRelation, map_sub, sub_eq_zero]
  have huv : (↑(g l) : Matrix (Fin 8) (Fin 8) R) *
      (↑((g l)⁻¹) : Matrix (Fin 8) (Fin 8) R) = 1 := by
    rw [← Units.val_mul]
    simp
  have hij := congrFun (congrFun huv i) j
  simpa [Matrix.mul_apply, genericMatrix, genericInverseMatrix,
    polynomialEvaluation, coordinateAssignment, coordinateVariable,
    Matrix.one_apply] using hij

theorem generalLinearIdeal_le_evaluationKer
    {R : Type u} [CommRing R] (g : MatrixTuple R) :
    generalLinearIdeal ≤ RingHom.ker (polynomialEvaluation g) := by
  rw [generalLinearIdeal, Ideal.span_le]
  rintro _ ⟨⟨l, i, j⟩, rfl⟩
  exact polynomialEvaluation_generalLinearRelation g l i j

/-- Evaluation of the three-`GL(8)` coordinate algebra at a matrix tuple. -/
def generalLinearEvaluation
    {R : Type u} [CommRing R] (g : MatrixTuple R) :
    GeneralLinearCoordinateRing →+* R :=
  Ideal.Quotient.lift generalLinearIdeal (polynomialEvaluation g)
    (fun _ ha => generalLinearIdeal_le_evaluationKer g ha)

theorem generalLinearEvaluation_genericMatrixUnit
    {R : Type u} [CommRing R] (g : MatrixTuple R)
    (l : TrialityLabel) :
    Matrix.GeneralLinearGroup.map (generalLinearEvaluation g)
      (genericMatrixUnit l) = g l := by
  apply Units.ext
  ext i j
  simp [Matrix.GeneralLinearGroup.map, genericMatrixUnit,
    genericMatrixQuotient, generalLinearEvaluation,
    generalLinearQuotient, polynomialEvaluation, genericMatrix,
    coordinateVariable, coordinateAssignment]

theorem generalLinearEvaluation_genericMatrixTuple
    {R : Type u} [CommRing R] (g : MatrixTuple R) :
    matrixTupleMap (generalLinearEvaluation g) genericMatrixTuple = g := by
  funext l
  exact generalLinearEvaluation_genericMatrixUnit g l

theorem relatedTripleResidualIdeal_le_evaluationKer
    {R : Type u} [CommRing R]
    (g : coefficientRelatedTripleGroup R) :
    relatedTripleResidualIdeal ≤
      RingHom.ker (generalLinearEvaluation g.1) := by
  rw [relatedTripleResidualIdeal, Ideal.span_le]
  rintro _ ⟨e, rfl⟩
  have hmap := map_relatedTripleCoefficientResidual
    (generalLinearEvaluation g.1) genericMatrixTuple e
  rw [generalLinearEvaluation_genericMatrixTuple g.1] at hmap
  exact hmap.trans (g.2 e)

/-- Evaluation of the final coordinate algebra at a coefficient-related
triple. -/
def relatedTripleCoordinateEvaluation
    {R : Type u} [CommRing R]
    (g : coefficientRelatedTripleGroup R) :
    RelatedTripleCoordinateRing →+* R :=
  Ideal.Quotient.lift relatedTripleResidualIdeal
    (generalLinearEvaluation g.1)
    (fun _ ha => relatedTripleResidualIdeal_le_evaluationKer g ha)

theorem relatedTripleCoordinateEvaluation_comp_quotient
    {R : Type u} [CommRing R]
    (g : coefficientRelatedTripleGroup R) :
    (relatedTripleCoordinateEvaluation g).comp
        relatedTripleCoordinateQuotient =
      generalLinearEvaluation g.1 := by
  apply Ideal.Quotient.ringHom_ext
  ext a <;>
    simp [relatedTripleCoordinateEvaluation,
      relatedTripleCoordinateQuotient, generalLinearEvaluation]

/-- Evaluating the universal point at a coefficient-related triple recovers
that triple.  This is the surjective half of the coordinate-ring universal
property. -/
theorem relatedTripleCoordinateEvaluation_universal
    {R : Type u} [CommRing R]
    (g : coefficientRelatedTripleGroup R) :
    coefficientRelatedTripleBaseChange
        (relatedTripleCoordinateEvaluation g)
        universalCoefficientRelatedTriple = g := by
  apply Subtype.ext
  change matrixTupleMap (relatedTripleCoordinateEvaluation g)
      universalRelatedTripleMatrixTuple = g.1
  unfold universalRelatedTripleMatrixTuple
  rw [← matrixTupleMap_comp,
    relatedTripleCoordinateEvaluation_comp_quotient,
    generalLinearEvaluation_genericMatrixTuple]

/-! ## Coordinate-ring universal property -/

/-- The coordinate-algebra evaluation is also injective: a ring morphism is
determined by the image of the universal related triple. -/
theorem relatedTripleCoordinateEvaluation_baseChange
    {R : Type u} [CommRing R]
    (f : RelatedTripleCoordinateRing →+* R) :
    relatedTripleCoordinateEvaluation
        (coefficientRelatedTripleBaseChange f
          universalCoefficientRelatedTriple) = f := by
  apply Ideal.Quotient.ringHom_ext
  change (relatedTripleCoordinateEvaluation
      ((coefficientRelatedTripleBaseChange f)
        universalCoefficientRelatedTriple)).comp
      relatedTripleCoordinateQuotient =
    f.comp relatedTripleCoordinateQuotient
  rw [relatedTripleCoordinateEvaluation_comp_quotient]
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [generalLinearEvaluation, polynomialEvaluation]
  · rintro ⟨v⟩
    cases v with
    | matrix l i j =>
        simp [generalLinearEvaluation, polynomialEvaluation,
          coordinateAssignment, coordinateVariable,
          universalCoefficientRelatedTriple,
          universalRelatedTripleMatrixTuple, genericMatrixTuple,
          genericMatrixUnit, genericMatrixQuotient, genericMatrix,
          relatedTripleCoordinateQuotient, generalLinearQuotient,
          matrixTupleMap, Matrix.GeneralLinearGroup.map]
    | inverse l i j =>
        suffices h :
            f (relatedTripleCoordinateQuotient
                ((genericMatrixQuotient l)⁻¹ i j)) =
              f (relatedTripleCoordinateQuotient
                (generalLinearQuotient
                  (MvPolynomial.X
                    (coordinateVariable (.inverse l i j))))) by
          simpa [generalLinearEvaluation, polynomialEvaluation,
            coordinateAssignment, coordinateVariable,
            universalCoefficientRelatedTriple,
            universalRelatedTripleMatrixTuple, genericMatrixTuple,
            genericMatrixUnit, relatedTripleCoordinateQuotient,
            generalLinearQuotient, matrixTupleMap,
            Matrix.GeneralLinearGroup.map] using h
        apply congrArg f
        rw [Matrix.inv_eq_right_inv
          (genericMatrix_mul_genericInverseMatrix l)]
        rfl


/-- Ring morphisms from the explicit coordinate algebra are naturally
identified with coefficient-related triples.  This is the complete
set-valued representability statement. -/
def relatedTripleCoordinateRingHomEquiv
    (R : Type u) [CommRing R] :
    (RelatedTripleCoordinateRing →+* R) ≃
      coefficientRelatedTripleGroup R where
  toFun f :=
    coefficientRelatedTripleBaseChange f
      universalCoefficientRelatedTriple
  invFun := relatedTripleCoordinateEvaluation
  left_inv := relatedTripleCoordinateEvaluation_baseChange
  right_inv := relatedTripleCoordinateEvaluation_universal


end

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn

/-- The coordinate-ring equivalence is natural in the target ring: extending
scalars on a represented point is the same as postcomposing its coordinate
map. -/
@[simp] theorem relatedTripleCoordinateRingHomEquiv_naturality
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (φ : RelatedTripleCoordinateRing →+* R) :
    coefficientRelatedTripleBaseChange f
        (relatedTripleCoordinateRingHomEquiv R φ) =
      relatedTripleCoordinateRingHomEquiv S (f.comp φ) := by
  change coefficientRelatedTripleBaseChange f
      (coefficientRelatedTripleBaseChange φ
        universalCoefficientRelatedTriple) =
    coefficientRelatedTripleBaseChange (f.comp φ)
      universalCoefficientRelatedTriple
  rw [coefficientRelatedTripleBaseChange_comp φ f]
  rfl

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn
