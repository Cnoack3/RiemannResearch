/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Ring.Basic
import RiemannResearch.LinearAlgebra.RootSystem.D4ZornPointFunctor

/-!
# Finite equations for the split-Zorn related-triples functor

The universal predicate in `D4ZornPointFunctor` quantifies over every scalar
extension in order to make base change honest over arbitrary commutative
rings. This module eliminates that quantifier. Norm preservation is
equivalent to preservation of the eight quadratic basis coefficients and the
sixty-four polar coefficients. Triality preservation is equivalent to its
`8^3` values on coordinate triples. Thus a related triple is cut out inside
`GL(8)^3` by one finite family of 728 integral coefficient residuals.

The proof is characteristic-free: the diagonal quadratic coefficients are
kept separately from the polar coefficients, so no division by two occurs.
The resulting finite-equation subgroup is proved equal, point by point and
naturally under base change, to the universal related-triples subgroup. The
existing twisted diagram action therefore transports to this finite model.

This is the finite closed-subfunctor input for a coordinate-ring
representability construction. It does not itself construct the quotient of
the coordinate ring of `GL(8)^3`, its Hopf structure, or an isomorphism with a
Clifford-theoretic Spin group scheme.

The related-triples terminology and split-octonion strategy follow
Alsaody--Gille, *Isotopes of Octonion Algebras, G2-Torsors and Triality*,
Theorem 3.12: <https://arxiv.org/abs/1704.05229>. The finite-basis expansion
proved here is an independent algebraic reformulation of the predicates.
-/

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn

open CategoryTheory
open scoped BigOperators

universe u

noncomputable section

/-- The `i`-th vector of the standard coordinate basis. -/
def coordinateVector (R : Type u) [CommRing R] (i : Fin 8) : Octonion R :=
  Pi.single i 1

/-- A triple of standard coordinate basis vectors. -/
def coordinateTriple (R : Type u) [CommRing R]
    (i : TrialityLabel → Fin 8) : TrialityLabel → Octonion R :=
  fun l => coordinateVector R (i l)

@[simp] theorem map_coordinateVector
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (i : Fin 8) :
    map f (coordinateVector R i) = coordinateVector S i := by
  ext j
  simp [map, coordinateVector, Pi.single_apply]

@[simp] theorem matrixApply_add
    {R : Type u} [CommRing R] (g : MatrixAutomorphism R)
    (x y : Octonion R) :
    matrixApply g (x + y) = matrixApply g x + matrixApply g y :=
  Matrix.mulVec_add g.1 x y

/-- Matrix application commutes with arbitrary scalar extension. -/
theorem map_matrixApply
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (g : MatrixAutomorphism R) (x : Octonion R) :
    map f (matrixApply g x) =
      matrixApply (Matrix.GeneralLinearGroup.map f g) (map f x) := by
  ext i
  simp [map, matrixApply, Matrix.mulVec, dotProduct,
    Matrix.GeneralLinearGroup.map_apply]

/-- Triality evaluation commutes with arbitrary scalar extension. -/
theorem map_trialityEval
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (x : TrialityLabel → Octonion R) :
    f (trialityEval R x) =
      trialityEval S (fun l => map f (x l)) := by
  simp [trialityEval]

/-- The norm after applying an invertible matrix. -/
def matrixNormForm {R : Type u} [CommRing R]
    (g : MatrixAutomorphism R) : QuadraticForm R (Octonion R) :=
  (normForm R).comp (Matrix.mulVecLin g.1)

@[simp] theorem matrixNormForm_apply
    {R : Type u} [CommRing R] (g : MatrixAutomorphism R)
    (x : Octonion R) :
    matrixNormForm g x = norm R (matrixApply g x) :=
  rfl

@[simp] theorem normForm_polar_eq
    {R : Type u} [CommRing R] (x y : Octonion R) :
    QuadraticMap.polar (normForm R) x y = normPolar R x y :=
  rfl

@[simp] theorem matrixNormForm_polar
    {R : Type u} [CommRing R] (g : MatrixAutomorphism R)
    (x y : Octonion R) :
    QuadraticMap.polar (matrixNormForm g) x y =
      normPolar R (matrixApply g x) (matrixApply g y) := by
  simp [QuadraticMap.polar, matrixNormForm, normPolar,
    matrixApply, Matrix.mulVec_add]

/-- Eight quadratic and sixty-four polar coefficient tests for norm
preservation. Keeping both is necessary in characteristic two. -/
def CoefficientNormPreserving
    {R : Type u} [CommRing R] (g : MatrixAutomorphism R) : Prop :=
  (∀ i,
    norm R (matrixApply g (coordinateVector R i)) =
      norm R (coordinateVector R i)) ∧
  (∀ i j,
    normPolar R (matrixApply g (coordinateVector R i))
        (matrixApply g (coordinateVector R j)) =
      normPolar R (coordinateVector R i) (coordinateVector R j))

/-- Quadratic forms in eight variables agree when their quadratic and polar
basis coefficients agree. -/
theorem quadraticForm_ext_coordinate
    {R : Type u} [CommRing R]
    (Q Q' : QuadraticForm R (Octonion R))
    (hq : ∀ i,
      Q (coordinateVector R i) = Q' (coordinateVector R i))
    (hp : ∀ i j,
      QuadraticMap.polar Q (coordinateVector R i) (coordinateVector R j) =
        QuadraticMap.polar Q' (coordinateVector R i)
          (coordinateVector R j)) :
    Q = Q' := by
  let b := Pi.basisFun R (Fin 8)
  have hpolMap : Q.polarBilin = Q'.polarBilin := by
    apply b.ext
    intro i
    apply b.ext
    intro j
    simpa [b, coordinateVector,
      QuadraticMap.polarBilin_apply_apply] using hp i j
  have hpolar (x y : Octonion R) :
      QuadraticMap.polar Q x y = QuadraticMap.polar Q' x y := by
    rw [← QuadraticMap.polarBilin_apply_apply,
      ← QuadraticMap.polarBilin_apply_apply, hpolMap]
  apply QuadraticMap.ext
  intro x
  have hsum : ∀ s : Finset (Fin 8),
      Q (∑ i ∈ s, (b.repr x) i • b i) =
        Q' (∑ i ∈ s, (b.repr x) i • b i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha,
          QuadraticMap.map_add Q, QuadraticMap.map_add Q',
          Q.map_smul, Q'.map_smul, ih, hpolar]
        simpa [b, coordinateVector] using congrArg
          (fun z => ((b.repr x) a * (b.repr x) a) • z) (hq a)
  simpa only [b.sum_repr] using hsum Finset.univ

/-- The finite norm test is equality of quadratic forms. -/
theorem coefficientNormPreserving_iff_matrixNormForm
    {R : Type u} [CommRing R] (g : MatrixAutomorphism R) :
    CoefficientNormPreserving g ↔
      matrixNormForm g = normForm R := by
  constructor
  · intro h
    apply quadraticForm_ext_coordinate
    · intro i
      exact h.1 i
    · intro i j
      simpa using h.2 i j
  · intro h
    constructor
    · intro i
      exact QuadraticMap.congr_fun h (coordinateVector R i)
    · intro i j
      have hp := congrArg
        (fun Q : QuadraticForm R (Octonion R) =>
          QuadraticMap.polar Q (coordinateVector R i)
            (coordinateVector R j)) h
      simpa using hp

/-- Finite norm coefficients are stable under scalar extension. -/
theorem coefficientNormPreserving_map
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (g : MatrixAutomorphism R)
    (h : CoefficientNormPreserving g) :
    CoefficientNormPreserving
      (Matrix.GeneralLinearGroup.map f g) := by
  constructor
  · intro i
    simpa only [map_norm, map_matrixApply, map_coordinateVector] using
      congrArg f (h.1 i)
  · intro i j
    simpa only [map_normPolar, map_matrixApply, map_coordinateVector] using
      congrArg f (h.2 i j)

/-- The finite norm test is equivalent to preservation after every scalar
extension. -/
theorem coefficientNormPreserving_iff_universally
    {R : Type u} [CommRing R] (g : MatrixAutomorphism R) :
    CoefficientNormPreserving g ↔ UniversallyNormPreserving g := by
  constructor
  · intro h S _ f x
    have hs := coefficientNormPreserving_map f g h
    have heq :=
      (coefficientNormPreserving_iff_matrixNormForm
        (Matrix.GeneralLinearGroup.map f g)).1 hs
    exact QuadraticMap.congr_fun heq x
  · intro h
    have hbase (x : Octonion R) :
        norm R (matrixApply g x) = norm R x := by
      have hx := h R (RingHom.id R) x
      have hm : Matrix.GeneralLinearGroup.map (RingHom.id R) g = g :=
        DFunLike.congr_fun Matrix.GeneralLinearGroup.map_id g
      rwa [hm] at hx
    constructor
    · exact fun i => hbase (coordinateVector R i)
    · intro i j
      simp only [normPolar]
      rw [← matrixApply_add, hbase, hbase, hbase]
/-- The split-Zorn triality tensor as a bundled trilinear map. -/
def trialityMultilinear (R : Type u) [CommRing R] :
    MultilinearMap R (fun _ : TrialityLabel => Octonion R) R where
  toFun := trialityEval R
  map_update_add' x l a b := by
    cases l <;>
      simp [trialityEval, trialityTensor, normPolar, paraMul, mul,
        conjugate, norm, Function.update] <;> ring
  map_update_smul' x l c a := by
    cases l <;>
      simp [trialityEval, trialityTensor, normPolar, paraMul, mul,
        conjugate, norm, Function.update] <;> ring

@[simp] theorem trialityMultilinear_apply
    (R : Type u) [CommRing R]
    (x : TrialityLabel → Octonion R) :
    trialityMultilinear R x = trialityEval R x :=
  rfl

/-- The triality tensor after applying one matrix in each slot. -/
def matrixTrialityMultilinear
    {R : Type u} [CommRing R] (g : MatrixTuple R) :
    MultilinearMap R (fun _ : TrialityLabel => Octonion R) R :=
  (trialityMultilinear R).compLinearMap
    (fun l => Matrix.mulVecLin (g l).1)

@[simp] theorem matrixTrialityMultilinear_apply
    {R : Type u} [CommRing R] (g : MatrixTuple R)
    (x : TrialityLabel → Octonion R) :
    matrixTrialityMultilinear g x =
      trialityEval R (fun l => matrixApply (g l) (x l)) :=
  rfl

/-- The `8^3` coordinate tests for preservation of the triality tensor. -/
def CoefficientRelated
    {R : Type u} [CommRing R] (g : MatrixTuple R) : Prop :=
  ∀ i : TrialityLabel → Fin 8,
    trialityEval R
        (fun l => matrixApply (g l) (coordinateVector R (i l))) =
      trialityEval R (coordinateTriple R i)

/-- Trilinear maps agree if they agree on all coordinate triples. -/
theorem multilinearMap_ext_coordinate
    {R : Type u} [CommRing R]
    (F G : MultilinearMap R
      (fun _ : TrialityLabel => Octonion R) R)
    (h : ∀ i : TrialityLabel → Fin 8,
      F (coordinateTriple R i) = G (coordinateTriple R i)) :
    F = G := by
  apply MultilinearMap.ext
  intro x
  let b := Pi.basisFun R (Fin 8)
  have hx : (fun l => ∑ i, x l i • b i) = x := by
    funext l
    simpa [b, Pi.basisFun_repr] using b.sum_repr (x l)
  rw [← hx, F.map_sum, G.map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [F.map_smul_univ, G.map_smul_univ]
  apply congrArg
  simp_rw [b, Pi.basisFun_apply]
  exact h i

/-- The finite triality test is equality of trilinear maps. -/
theorem coefficientRelated_iff_matrixTrialityMultilinear
    {R : Type u} [CommRing R] (g : MatrixTuple R) :
    CoefficientRelated g ↔
      matrixTrialityMultilinear g = trialityMultilinear R := by
  constructor
  · intro h
    apply multilinearMap_ext_coordinate
    intro i
    exact h i
  · intro h i
    exact MultilinearMap.congr_fun h (coordinateTriple R i)

/-- Finite triality coefficients are stable under scalar extension. -/
theorem coefficientRelated_map
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (g : MatrixTuple R) (h : CoefficientRelated g) :
    CoefficientRelated (matrixTupleMap f g) := by
  intro i
  change trialityEval S
      (fun l => matrixApply (Matrix.GeneralLinearGroup.map f (g l))
        (coordinateVector S (i l))) =
    trialityEval S (fun l => coordinateVector S (i l))
  have hi := h i
  change trialityEval R
      (fun l => matrixApply (g l) (coordinateVector R (i l))) =
    trialityEval R (fun l => coordinateVector R (i l)) at hi
  simpa only [map_trialityEval, map_matrixApply, map_coordinateVector] using
    congrArg f hi

/-- The finite triality test is equivalent to preservation after every scalar
extension. -/
theorem coefficientRelated_iff_universally
    {R : Type u} [CommRing R] (g : MatrixTuple R) :
    CoefficientRelated g ↔ UniversallyRelated g := by
  constructor
  · intro h S _ f x
    have hs := coefficientRelated_map f g h
    have heq :=
      (coefficientRelated_iff_matrixTrialityMultilinear
        (matrixTupleMap f g)).1 hs
    exact MultilinearMap.congr_fun heq x
  · intro h i
    have hi := h R (RingHom.id R) (coordinateTriple R i)
    rw [matrixTupleMap_id] at hi
    exact hi

/-- Indices for the eight quadratic and sixty-four polar coefficients. -/
abbrev NormCoefficientIndex := Sum (Fin 8) (Fin 8 × Fin 8)

/-- One finite index type for all norm and triality coefficients. -/
abbrev RelatedTripleCoefficientIndex :=
  Sum (TrialityLabel × NormCoefficientIndex)
    (TrialityLabel → Fin 8)

set_option maxRecDepth 5000 in
/-- The chosen finite presentation has 728 residuals. -/
theorem relatedTripleCoefficientIndex_card :
    Fintype.card RelatedTripleCoefficientIndex = 728 := by
  decide

/-- The indexed integral coefficient residual. -/
def relatedTripleCoefficientResidual
    {R : Type u} [CommRing R] (g : MatrixTuple R) :
    RelatedTripleCoefficientIndex → R
  | .inl (l, .inl i) =>
      norm R (matrixApply (g l) (coordinateVector R i)) -
        norm R (coordinateVector R i)
  | .inl (l, .inr (i, j)) =>
      normPolar R (matrixApply (g l) (coordinateVector R i))
          (matrixApply (g l) (coordinateVector R j)) -
        normPolar R (coordinateVector R i) (coordinateVector R j)
  | .inr i =>
      trialityEval R
          (fun l => matrixApply (g l) (coordinateVector R (i l))) -
        trialityEval R (coordinateTriple R i)

/-- Every coefficient residual is an integral polynomial expression: applying
a ring morphism to a residual is the residual of the base-changed matrices. -/
theorem map_relatedTripleCoefficientResidual
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (g : MatrixTuple R)
    (e : RelatedTripleCoefficientIndex) :
    f (relatedTripleCoefficientResidual g e) =
      relatedTripleCoefficientResidual (matrixTupleMap f g) e := by
  rcases e with ⟨⟨l, i⟩⟩ | i
  · rcases i with i | ⟨i, j⟩
    · simp only [relatedTripleCoefficientResidual, map_sub, matrixTupleMap,
        map_norm, map_matrixApply, map_coordinateVector]
    · simp only [relatedTripleCoefficientResidual, map_sub, matrixTupleMap,
        map_normPolar, map_matrixApply, map_coordinateVector]
  · simp only [relatedTripleCoefficientResidual, map_sub]
    rw [map_trialityEval, map_trialityEval]
    congr 1
    · apply congrArg (trialityEval S)
      funext l
      rw [map_matrixApply, map_coordinateVector]
      rfl
    · apply congrArg (trialityEval S)
      funext l
      rw [show coordinateTriple R i l = coordinateVector R (i l) from rfl,
        map_coordinateVector]
      rfl

/-- All 728 integral coefficient residuals vanish. -/
def SatisfiesRelatedTripleCoefficientEquations
    {R : Type u} [CommRing R] (g : MatrixTuple R) : Prop :=
  ∀ e, relatedTripleCoefficientResidual g e = 0

/-- The residual family is equivalent to the separate coefficient tests. -/
theorem satisfiesRelatedTripleCoefficientEquations_iff
    {R : Type u} [CommRing R] (g : MatrixTuple R) :
    SatisfiesRelatedTripleCoefficientEquations g ↔
      (∀ l, CoefficientNormPreserving (g l)) ∧ CoefficientRelated g := by
  constructor
  · intro h
    constructor
    · intro l
      constructor
      · intro i
        exact sub_eq_zero.mp (h (.inl (l, .inl i)))
      · intro i j
        exact sub_eq_zero.mp (h (.inl (l, .inr (i, j))))
    · intro i
      exact sub_eq_zero.mp (h (.inr i))
  · rintro ⟨hn, ht⟩ e
    rcases e with ⟨⟨l, i⟩⟩ | i
    · rcases i with i | ⟨i, j⟩
      · exact sub_eq_zero.mpr ((hn l).1 i)
      · exact sub_eq_zero.mpr ((hn l).2 i j)
    · exact sub_eq_zero.mpr (ht i)

/-- Vanishing of the residual family is preserved by scalar extension. -/
theorem satisfiesRelatedTripleCoefficientEquations_map
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (g : MatrixTuple R)
    (h : SatisfiesRelatedTripleCoefficientEquations g) :
    SatisfiesRelatedTripleCoefficientEquations (matrixTupleMap f g) := by
  rw [satisfiesRelatedTripleCoefficientEquations_iff] at h ⊢
  exact ⟨fun l => coefficientNormPreserving_map f (g l) (h.1 l),
    coefficientRelated_map f g h.2⟩

/-- The finite residual family vanishes exactly on the universal subgroup. -/
theorem satisfiesRelatedTripleCoefficientEquations_iff_mem_universal
    {R : Type u} [CommRing R] (g : MatrixTuple R) :
    SatisfiesRelatedTripleCoefficientEquations g ↔
      g ∈ universalRelatedTripleGroup R := by
  rw [satisfiesRelatedTripleCoefficientEquations_iff]
  change
    ((∀ l, CoefficientNormPreserving (g l)) ∧ CoefficientRelated g) ↔
      (∀ l, UniversallyNormPreserving (g l)) ∧ UniversallyRelated g
  constructor
  · rintro ⟨hn, ht⟩
    exact ⟨fun l =>
      (coefficientNormPreserving_iff_universally (g l)).1 (hn l),
      (coefficientRelated_iff_universally g).1 ht⟩
  · rintro ⟨hn, ht⟩
    exact ⟨fun l =>
      (coefficientNormPreserving_iff_universally (g l)).2 (hn l),
      (coefficientRelated_iff_universally g).2 ht⟩
/-- The related-triples group defined by the finite coefficient equations. -/
def coefficientRelatedTripleGroup (R : Type u) [CommRing R] :
    Subgroup (MatrixTuple R) where
  carrier := {g | SatisfiesRelatedTripleCoefficientEquations g}
  one_mem' :=
    (satisfiesRelatedTripleCoefficientEquations_iff_mem_universal 1).2
      (universalRelatedTripleGroup R).one_mem
  mul_mem' := by
    intro g h hg hh
    change SatisfiesRelatedTripleCoefficientEquations (g * h)
    change SatisfiesRelatedTripleCoefficientEquations g at hg
    change SatisfiesRelatedTripleCoefficientEquations h at hh
    rw [satisfiesRelatedTripleCoefficientEquations_iff_mem_universal]
    exact (universalRelatedTripleGroup R).mul_mem
      ((satisfiesRelatedTripleCoefficientEquations_iff_mem_universal g).1 hg)
      ((satisfiesRelatedTripleCoefficientEquations_iff_mem_universal h).1 hh)
  inv_mem' := by
    intro g hg
    change SatisfiesRelatedTripleCoefficientEquations g⁻¹
    change SatisfiesRelatedTripleCoefficientEquations g at hg
    rw [satisfiesRelatedTripleCoefficientEquations_iff_mem_universal]
    exact (universalRelatedTripleGroup R).inv_mem
      ((satisfiesRelatedTripleCoefficientEquations_iff_mem_universal g).1 hg)

@[simp] theorem mem_coefficientRelatedTripleGroup
    {R : Type u} [CommRing R] (g : MatrixTuple R) :
    g ∈ coefficientRelatedTripleGroup R ↔
      SatisfiesRelatedTripleCoefficientEquations g :=
  Iff.rfl

/-- The finite-equation and universal groups are the same subgroup of
`GL(8)^3`. -/
theorem coefficientRelatedTripleGroup_eq_universal
    (R : Type u) [CommRing R] :
    coefficientRelatedTripleGroup R = universalRelatedTripleGroup R := by
  ext g
  exact satisfiesRelatedTripleCoefficientEquations_iff_mem_universal g

/-- Identity-on-matrices equivalence between the finite and universal
models. -/
def coefficientRelatedTripleEquivUniversal
    (R : Type u) [CommRing R] :
    coefficientRelatedTripleGroup R ≃* universalRelatedTripleGroup R where
  toFun g :=
    ⟨g.1,
      (satisfiesRelatedTripleCoefficientEquations_iff_mem_universal g.1).1
        g.2⟩
  invFun g :=
    ⟨g.1,
      (satisfiesRelatedTripleCoefficientEquations_iff_mem_universal g.1).2
        g.2⟩
  left_inv _g := rfl
  right_inv _g := rfl
  map_mul' _ _ := rfl

/-- Scalar extension on the finite-equation group. -/
def coefficientRelatedTripleBaseChange
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    coefficientRelatedTripleGroup R →*
      coefficientRelatedTripleGroup S where
  toFun g :=
    ⟨matrixTupleMap f g.1,
      satisfiesRelatedTripleCoefficientEquations_map f g.1 g.2⟩
  map_one' := by
    apply Subtype.ext
    exact matrixTupleMap_one f
  map_mul' g h := by
    apply Subtype.ext
    exact matrixTupleMap_mul f g.1 h.1

@[simp] theorem coefficientRelatedTripleBaseChange_apply
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (g : coefficientRelatedTripleGroup R) :
    (coefficientRelatedTripleBaseChange f g).1 =
      matrixTupleMap f g.1 :=
  rfl

theorem coefficientRelatedTripleBaseChange_id
    {R : Type u} [CommRing R] :
    coefficientRelatedTripleBaseChange (RingHom.id R) =
      MonoidHom.id (coefficientRelatedTripleGroup R) := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  exact matrixTupleMap_id g.1

theorem coefficientRelatedTripleBaseChange_comp
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (h : S →+* T) :
    coefficientRelatedTripleBaseChange (h.comp f) =
      (coefficientRelatedTripleBaseChange h).comp
        (coefficientRelatedTripleBaseChange f) := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  exact matrixTupleMap_comp f h g.1

/-- The corrected diagram action transported to the finite-equation model. -/
def coefficientRelatedTripleOuterAction
    (R : Type u) [CommRing R] :
    DiagramSymmetry →* MulAut (coefficientRelatedTripleGroup R) :=
  (MulAut.congr
    (coefficientRelatedTripleEquivUniversal R).symm).toMonoidHom.comp
    (universalRelatedTripleOuterAction R)

/-- The transported action is the same twisted relabeling on matrices. -/
@[simp] theorem coefficientRelatedTripleOuterAction_apply_coe
    (R : Type u) [CommRing R] (σ : DiagramSymmetry)
    (g : coefficientRelatedTripleGroup R) :
    (coefficientRelatedTripleOuterAction R σ g).1 =
      matrixTupleTwistedRelabel R σ g.1 :=
  rfl

/-- Scalar extension intertwines the diagram action on the finite model. -/
theorem coefficientRelatedTripleBaseChange_relabel
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (σ : DiagramSymmetry) (g : coefficientRelatedTripleGroup R) :
    coefficientRelatedTripleBaseChange f
        (coefficientRelatedTripleOuterAction R σ g) =
      coefficientRelatedTripleOuterAction S σ
        (coefficientRelatedTripleBaseChange f g) := by
  apply Subtype.ext
  exact matrixTupleMap_twistedRelabel f σ g.1

/-- The finite-equation related triples as a group-valued functor on
commutative rings. This is the honest finite closed-subfunctor interface;
representability by a coordinate algebra is a separate construction. -/
def coefficientRelatedTriplePointFunctor :
    CommRingCat.{u} ⥤ GrpCat.{u} where
  obj R := GrpCat.of (coefficientRelatedTripleGroup R)
  map f := GrpCat.ofHom (coefficientRelatedTripleBaseChange f.hom)
  map_id R := by
    apply GrpCat.hom_ext
    exact coefficientRelatedTripleBaseChange_id
  map_comp f h := by
    apply GrpCat.hom_ext
    exact coefficientRelatedTripleBaseChange_comp f.hom h.hom

end

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn
