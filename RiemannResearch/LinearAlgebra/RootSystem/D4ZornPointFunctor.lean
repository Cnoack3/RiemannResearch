/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.LinearAlgebra.RootSystem.D4ZornBaseChange
import RiemannResearch.LinearAlgebra.RootSystem.D4ZornRelatedTriples

/-!
# The universal split-Zorn related-triples point functor

The existing Zorn related-triples group uses equality of functions on
base-ring points. Over an arbitrary commutative ring, that predicate alone
cannot be transported through every ring morphism: equality of polynomial
functions on one ring need not be equality of their coefficients.

This module records the honest all-rings replacement. A point is a triple of
invertible eight-by-eight matrices whose norm and triality identities hold
after every scalar extension. This universal predicate is closed under
products and inverses and admits functorial base change. The integral Zorn
conjugation matrix also gives the corrected twisted diagram action, and the
action is proved natural under every scalar extension.

No representability or coordinate Hopf algebra is asserted here.
-/

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn

universe u

noncomputable section

/-- An invertible matrix acting on the eight Zorn coordinates. -/
abbrev MatrixAutomorphism (R : Type u) [CommRing R] :=
  Matrix.GeneralLinearGroup (Fin 8) R

/-- A matrix-valued vector/half-spin triple. -/
abbrev MatrixTuple (R : Type u) [CommRing R] :=
  TrialityLabel → MatrixAutomorphism R

/-- Matrix action on the eight Zorn coordinates. -/
def matrixApply {R : Type u} [CommRing R]
    (g : MatrixAutomorphism R) (x : Octonion R) : Octonion R :=
  g.1.mulVec x

@[simp] theorem matrixApply_one {R : Type u} [CommRing R]
    (x : Octonion R) :
    matrixApply (1 : MatrixAutomorphism R) x = x :=
  Matrix.one_mulVec x

@[simp] theorem matrixApply_mul {R : Type u} [CommRing R]
    (g h : MatrixAutomorphism R) (x : Octonion R) :
    matrixApply (g * h) x = matrixApply g (matrixApply h x) := by
  change ((g * h : MatrixAutomorphism R).1).mulVec x =
    g.1.mulVec (h.1.mulVec x)
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mulVec_mulVec]

@[simp] theorem matrixApply_apply_inv {R : Type u} [CommRing R]
    (g : MatrixAutomorphism R) (x : Octonion R) :
    matrixApply g (matrixApply g⁻¹ x) = x := by
  rw [← matrixApply_mul, mul_inv_cancel, matrixApply_one]

@[simp] theorem matrixApply_inv_apply {R : Type u} [CommRing R]
    (g : MatrixAutomorphism R) (x : Octonion R) :
    matrixApply g⁻¹ (matrixApply g x) = x := by
  rw [← matrixApply_mul, inv_mul_cancel, matrixApply_one]

/-- Coordinatewise scalar extension of a matrix tuple. -/
def matrixTupleMap {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (g : MatrixTuple R) : MatrixTuple S :=
  fun l => Matrix.GeneralLinearGroup.map f (g l)

@[simp] theorem matrixTupleMap_one
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    matrixTupleMap f (1 : MatrixTuple R) = 1 := by
  funext l
  simp [matrixTupleMap]

@[simp] theorem matrixTupleMap_mul
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (g h : MatrixTuple R) :
    matrixTupleMap f (g * h) =
      matrixTupleMap f g * matrixTupleMap f h := by
  funext l
  simp [matrixTupleMap]

@[simp] theorem matrixTupleMap_inv
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (g : MatrixTuple R) :
    matrixTupleMap f g⁻¹ = (matrixTupleMap f g)⁻¹ := by
  funext l
  simp [matrixTupleMap]

theorem matrixTupleMap_id {R : Type u} [CommRing R]
    (g : MatrixTuple R) :
    matrixTupleMap (RingHom.id R) g = g := by
  funext l
  exact DFunLike.congr_fun Matrix.GeneralLinearGroup.map_id (g l)

theorem matrixTupleMap_comp
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (h : S →+* T) (g : MatrixTuple R) :
    matrixTupleMap (h.comp f) g =
      matrixTupleMap h (matrixTupleMap f g) := by
  funext l
  exact DFunLike.congr_fun
    (Matrix.GeneralLinearGroup.map_comp f h) (g l)

/-- Norm preservation after every scalar extension. The universal
quantification is what makes this condition functorial over arbitrary
commutative rings. -/
def UniversallyNormPreserving {R : Type u} [CommRing R]
    (g : MatrixAutomorphism R) : Prop :=
  ∀ (S : Type u) [CommRing S] (f : R →+* S) (x : Octonion S),
    norm S (matrixApply (Matrix.GeneralLinearGroup.map f g) x) =
      norm S x

/-- Triality-tensor preservation after every scalar extension. -/
def UniversallyRelated {R : Type u} [CommRing R]
    (g : MatrixTuple R) : Prop :=
  ∀ (S : Type u) [CommRing S] (f : R →+* S)
      (x : TrialityLabel → Octonion S),
    trialityEval S
        (fun l => matrixApply (matrixTupleMap f g l) (x l)) =
      trialityEval S x

/-- Triples of invertible matrices preserving the split-Zorn norm in every
component and the triality tensor, universally under scalar extension. -/
def universalRelatedTripleGroup (R : Type u) [CommRing R] :
    Subgroup (MatrixTuple R) where
  carrier := {g |
    (∀ l, UniversallyNormPreserving (g l)) ∧ UniversallyRelated g}
  one_mem' := by
    constructor
    · intro l S _ f x
      simp [matrixApply]
    · intro S _ f x
      simp [trialityEval, matrixTupleMap, matrixApply]
  mul_mem' := by
    intro g h hg hh
    constructor
    · intro l S _ f x
      change norm S
          (matrixApply
            (Matrix.GeneralLinearGroup.map f (g l * h l)) x) =
        norm S x
      rw [Matrix.GeneralLinearGroup.map_mul, matrixApply_mul,
        hg.1 l S f, hh.1 l S f]
    · intro S _ f x
      change trialityEval S
          (fun l => matrixApply
            (Matrix.GeneralLinearGroup.map f (g l * h l)) (x l)) =
        trialityEval S x
      rw [show
        (fun l => matrixApply
          (Matrix.GeneralLinearGroup.map f (g l * h l)) (x l)) =
            (fun l => matrixApply
              (matrixTupleMap f g l)
              (matrixApply (matrixTupleMap f h l) (x l))) by
          funext l
          simp [matrixTupleMap, Matrix.GeneralLinearGroup.map_mul,
            matrixApply_mul]]
      exact (hg.2 S f _).trans (hh.2 S f x)
  inv_mem' := by
    intro g hg
    constructor
    · intro l S _ f x
      change norm S
          (matrixApply
            (Matrix.GeneralLinearGroup.map f (g l)⁻¹) x) =
        norm S x
      rw [Matrix.GeneralLinearGroup.map_inv]
      have h := hg.1 l S f
        (matrixApply
          (Matrix.GeneralLinearGroup.map f (g l))⁻¹ x)
      rw [matrixApply_apply_inv] at h
      exact h.symm
    · intro S _ f x
      change trialityEval S
          (fun l => matrixApply
            (Matrix.GeneralLinearGroup.map f (g l)⁻¹) (x l)) =
        trialityEval S x
      simp only [Matrix.GeneralLinearGroup.map_inv]
      have h := hg.2 S f
        (fun l => matrixApply
          (matrixTupleMap f g l)⁻¹ (x l))
      simpa [matrixTupleMap] using h.symm
/-- Scalar extension of universal Zorn related triples along an arbitrary
commutative-ring morphism. -/
def universalRelatedTripleBaseChange
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    universalRelatedTripleGroup R →*
      universalRelatedTripleGroup S where
  toFun g := ⟨matrixTupleMap f g.1, by
    constructor
    · intro l T _ h x
      have hg := g.2.1 l T (h.comp f) x
      simpa [UniversallyNormPreserving, matrixTupleMap,
        Matrix.GeneralLinearGroup.map_comp] using hg
    · intro T _ h x
      have hg := g.2.2 T (h.comp f) x
      simpa [UniversallyRelated, matrixTupleMap,
        Matrix.GeneralLinearGroup.map_comp] using hg⟩
  map_one' := by
    apply Subtype.ext
    exact matrixTupleMap_one f
  map_mul' g h := by
    apply Subtype.ext
    exact matrixTupleMap_mul f g.1 h.1

@[simp] theorem universalRelatedTripleBaseChange_apply
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (g : universalRelatedTripleGroup R) :
    (universalRelatedTripleBaseChange f g).1 =
      matrixTupleMap f g.1 :=
  rfl

/-- Universal related-triple scalar extension is the identity on identity ring
morphisms. -/
theorem universalRelatedTripleBaseChange_id
    {R : Type u} [CommRing R] :
    universalRelatedTripleBaseChange (RingHom.id R) =
      MonoidHom.id (universalRelatedTripleGroup R) := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  exact matrixTupleMap_id g.1

/-- Universal related-triple scalar extension respects composition of ring
morphisms. -/
theorem universalRelatedTripleBaseChange_comp
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (h : S →+* T) :
    universalRelatedTripleBaseChange (h.comp f) =
      (universalRelatedTripleBaseChange h).comp
        (universalRelatedTripleBaseChange f) := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  exact matrixTupleMap_comp f h g.1
/-- The integral matrix of Zorn conjugation in the standard coordinate
basis. -/
def zornConjugationMatrix (R : Type u) [CommRing R] :
    Matrix (Fin 8) (Fin 8) R :=
  fun i j => conjugate R (Pi.single j 1) i

theorem zornConjugationMatrix_sq (R : Type u) [CommRing R] :
    zornConjugationMatrix R * zornConjugationMatrix R = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zornConjugationMatrix, Matrix.mul_apply, conjugate,
      Pi.single_apply]

/-- Zorn conjugation as an integral invertible eight-by-eight matrix. -/
def zornConjugationGL (R : Type u) [CommRing R] :
    MatrixAutomorphism R :=
  ⟨zornConjugationMatrix R, zornConjugationMatrix R,
    zornConjugationMatrix_sq R, zornConjugationMatrix_sq R⟩

@[simp] theorem zornConjugationGL_inv
    (R : Type u) [CommRing R] :
    (zornConjugationGL R)⁻¹ = zornConjugationGL R := by
  apply Units.ext
  rfl

@[simp] theorem zornConjugationGL_mul_self
    (R : Type u) [CommRing R] :
    zornConjugationGL R * zornConjugationGL R = 1 := by
  apply Units.ext
  exact zornConjugationMatrix_sq R

@[simp] theorem zornConjugationGL_mul_zornConjugationGL_mul
    (R : Type u) [CommRing R] (g : MatrixAutomorphism R) :
    zornConjugationGL R * (zornConjugationGL R * g) = g := by
  rw [← mul_assoc, zornConjugationGL_mul_self, one_mul]

@[simp] theorem mul_zornConjugationGL_mul_zornConjugationGL
    (R : Type u) [CommRing R] (g : MatrixAutomorphism R) :
    g * zornConjugationGL R * zornConjugationGL R = g := by
  rw [mul_assoc, zornConjugationGL_mul_self, mul_one]

@[simp] theorem zornConjugationGL_apply
    (R : Type u) [CommRing R] (x : Octonion R) :
    matrixApply (zornConjugationGL R) x = conjugate R x := by
  ext i
  fin_cases i <;>
    simp [matrixApply, zornConjugationGL, zornConjugationMatrix,
      Matrix.mulVec, dotProduct, conjugate, Pi.single_apply]

/-- The integral Zorn-conjugation matrix commutes with every scalar
extension. -/
theorem zornConjugationGL_map
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    Matrix.GeneralLinearGroup.map f (zornConjugationGL R) =
      zornConjugationGL S := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zornConjugationGL, zornConjugationMatrix,
      Matrix.GeneralLinearGroup.map_apply, conjugate]

def matrixTupleConjugation (R : Type u) [CommRing R] :
    MulAut (MatrixTuple R) where
  toFun g l :=
    zornConjugationGL R * g l * (zornConjugationGL R)⁻¹
  invFun g l :=
    (zornConjugationGL R)⁻¹ * g l * zornConjugationGL R
  left_inv g := by
    funext l
    simp [mul_assoc]
  right_inv g := by
    funext l
    simp [mul_assoc]
  map_mul' g h := by
    funext l
    simp [mul_assoc]

def matrixTuplePureRelabel (R : Type u) [CommRing R]
    (σ : DiagramSymmetry) : MulAut (MatrixTuple R) where
  toFun g l := g (σ⁻¹ l)
  invFun g l := g (σ l)
  left_inv g := by
    funext l
    simp
  right_inv g := by
    funext l
    simp
  map_mul' _ _ := rfl

/-- Even diagram symmetries relabel matrix components; odd symmetries also
conjugate every component by the integral Zorn-conjugation matrix. -/
def matrixTupleTwistedRelabel (R : Type u) [CommRing R]
    (σ : DiagramSymmetry) : MulAut (MatrixTuple R) :=
  if DiagramEven σ then matrixTuplePureRelabel R σ
  else matrixTupleConjugation R * matrixTuplePureRelabel R σ

def matrixTupleTwistedRelabelAction
    (R : Type u) [CommRing R] :
    DiagramSymmetry →* MulAut (MatrixTuple R) where
  toFun := matrixTupleTwistedRelabel R
  map_one' := by
    ext g l
    simp [matrixTupleTwistedRelabel, matrixTuplePureRelabel,
      DiagramEven]
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro g
    funext l
    by_cases hσ : DiagramEven σ <;> by_cases hτ : DiagramEven τ
    · have hm : DiagramEven (σ * τ) :=
        (diagramEven_mul_iff σ τ).2
          ⟨fun _ => hτ, fun _ => hσ⟩
      simp [matrixTupleTwistedRelabel, matrixTuplePureRelabel,
        hσ, hτ, hm]
    · have hm : ¬DiagramEven (σ * τ) := by
        intro h
        exact hτ ((diagramEven_mul_iff σ τ).1 h |>.mp hσ)
      simp [matrixTupleTwistedRelabel, matrixTuplePureRelabel,
        matrixTupleConjugation, hσ, hτ, hm]
    · have hm : ¬DiagramEven (σ * τ) := by
        intro h
        exact hσ ((diagramEven_mul_iff σ τ).1 h |>.mpr hτ)
      simp [matrixTupleTwistedRelabel, matrixTuplePureRelabel,
        matrixTupleConjugation, hσ, hτ, hm]
    · have hm : DiagramEven (σ * τ) :=
        (diagramEven_mul_iff σ τ).2
          ⟨fun hs => (hσ hs).elim,
            fun ht => (hτ ht).elim⟩
      simp [matrixTupleTwistedRelabel, matrixTuplePureRelabel,
        matrixTupleConjugation, hσ, hτ, hm, mul_assoc]

theorem matrixTupleTwistedRelabel_apply
    (R : Type u) [CommRing R] (σ : DiagramSymmetry)
    (g : MatrixTuple R) (x : TrialityLabel → Octonion R)
    (l : TrialityLabel) :
    matrixApply ((matrixTupleTwistedRelabel R σ g) l) (x l) =
      valueTwistedRelabel R σ
        (fun k => matrixApply (g k)
          (valueTwistedRelabel R σ⁻¹ x k)) l := by
  by_cases hσ : DiagramEven σ
  · have hi : DiagramEven σ⁻¹ := (diagramEven_inv_iff σ).2 hσ
    simp [matrixTupleTwistedRelabel, matrixTuplePureRelabel,
      valueTwistedRelabel, hσ, hi]
  · have hi : ¬DiagramEven σ⁻¹ := by
      intro h
      exact hσ ((diagramEven_inv_iff σ).1 h)
    simp [matrixTupleTwistedRelabel, matrixTuplePureRelabel,
      matrixTupleConjugation, valueTwistedRelabel, hσ, hi,
      matrixApply_mul]

/-- Twisted diagram relabeling commutes with every scalar extension on
ambient matrix tuples. -/
theorem matrixTupleMap_twistedRelabel
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (σ : DiagramSymmetry) (g : MatrixTuple R) :
    matrixTupleMap f (matrixTupleTwistedRelabel R σ g) =
      matrixTupleTwistedRelabel S σ (matrixTupleMap f g) := by
  by_cases hσ : DiagramEven σ
  · funext l
    simp [matrixTupleTwistedRelabel, matrixTuplePureRelabel,
      matrixTupleMap, hσ]
  · funext l
    simp [matrixTupleTwistedRelabel, matrixTuplePureRelabel,
      matrixTupleConjugation, matrixTupleMap, hσ,
      zornConjugationGL_map]

set_option linter.flexible false in
theorem matrixTupleTwistedRelabel_mem_universal
    (R : Type u) [CommRing R] (σ : DiagramSymmetry)
    (g : universalRelatedTripleGroup R) :
    matrixTupleTwistedRelabel R σ g.1 ∈
      universalRelatedTripleGroup R := by
  constructor
  · intro l S _ f x
    rw [show Matrix.GeneralLinearGroup.map f
        ((matrixTupleTwistedRelabel R σ g.1) l) =
        (matrixTupleTwistedRelabel S σ
          (matrixTupleMap f g.1)) l by
      exact congrFun (matrixTupleMap_twistedRelabel f σ g.1) l]
    by_cases hσ : DiagramEven σ
    · simp [matrixTupleTwistedRelabel, matrixTuplePureRelabel, hσ]
      exact g.2.1 (σ⁻¹ l) S f x
    · simp [matrixTupleTwistedRelabel, matrixTuplePureRelabel,
        matrixTupleConjugation, hσ, matrixApply_mul,
        norm_conjugate]
      calc
        norm S
            (matrixApply (matrixTupleMap f g.1 (σ⁻¹ l))
              (conjugate S x)) =
          norm S (conjugate S x) := by
            simpa [matrixTupleMap] using
              g.2.1 (σ⁻¹ l) S f (conjugate S x)
        _ = norm S x := norm_conjugate S x
  · intro S _ f x
    rw [show
      (fun l => matrixApply
        (matrixTupleMap f
          (matrixTupleTwistedRelabel R σ g.1) l) (x l)) =
        (fun l => valueTwistedRelabel S σ
          (fun k => matrixApply (matrixTupleMap f g.1 k)
            (valueTwistedRelabel S σ⁻¹ x k)) l) by
        funext l
        rw [matrixTupleMap_twistedRelabel]
        exact matrixTupleTwistedRelabel_apply S σ
          (matrixTupleMap f g.1) x l]
    rw [trialityEval_valueTwistedRelabel]
    rw [g.2.2 S f]
    exact trialityEval_valueTwistedRelabel S σ⁻¹ x

/-- The twisted diagram relabeling restricted to universal related
triples. -/
def universalRelatedTripleRelabel
    (R : Type u) [CommRing R] (σ : DiagramSymmetry) :
    MulAut (universalRelatedTripleGroup R) where
  toFun g :=
    ⟨matrixTupleTwistedRelabel R σ g.1,
      matrixTupleTwistedRelabel_mem_universal R σ g⟩
  invFun g :=
    ⟨matrixTupleTwistedRelabel R σ⁻¹ g.1,
      matrixTupleTwistedRelabel_mem_universal R σ⁻¹ g⟩
  left_inv g := by
    apply Subtype.ext
    have h := congrArg
      (fun a : MulAut (MatrixTuple R) => a g.1)
      ((matrixTupleTwistedRelabelAction R).map_mul σ⁻¹ σ)
    change matrixTupleTwistedRelabel R σ⁻¹
      (matrixTupleTwistedRelabel R σ g.1) = g.1
    calc
      _ = ((matrixTupleTwistedRelabelAction R σ⁻¹) *
          (matrixTupleTwistedRelabelAction R σ)) g.1 := rfl
      _ = matrixTupleTwistedRelabelAction R (σ⁻¹ * σ) g.1 :=
        h.symm
      _ = g.1 := by simp
  right_inv g := by
    apply Subtype.ext
    have h := congrArg
      (fun a : MulAut (MatrixTuple R) => a g.1)
      ((matrixTupleTwistedRelabelAction R).map_mul σ σ⁻¹)
    change matrixTupleTwistedRelabel R σ
      (matrixTupleTwistedRelabel R σ⁻¹ g.1) = g.1
    calc
      _ = ((matrixTupleTwistedRelabelAction R σ) *
          (matrixTupleTwistedRelabelAction R σ⁻¹)) g.1 := rfl
      _ = matrixTupleTwistedRelabelAction R (σ * σ⁻¹) g.1 :=
        h.symm
      _ = g.1 := by simp
  map_mul' g h := by
    apply Subtype.ext
    exact (matrixTupleTwistedRelabel R σ).map_mul g.1 h.1

/-- The natural twisted D4 diagram action on universal split-Zorn related
triples. -/
def universalRelatedTripleOuterAction
    (R : Type u) [CommRing R] :
    DiagramSymmetry →* MulAut (universalRelatedTripleGroup R) where
  toFun := universalRelatedTripleRelabel R
  map_one' := by
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    exact DFunLike.congr_fun
      (matrixTupleTwistedRelabelAction R).map_one g.1
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    exact DFunLike.congr_fun
      ((matrixTupleTwistedRelabelAction R).map_mul σ τ) g.1

/-- Scalar extension intertwines the twisted diagram action on universal
related triples. -/
theorem universalRelatedTripleBaseChange_relabel
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (σ : DiagramSymmetry) (g : universalRelatedTripleGroup R) :
    universalRelatedTripleBaseChange f
        (universalRelatedTripleOuterAction R σ g) =
      universalRelatedTripleOuterAction S σ
        (universalRelatedTripleBaseChange f g) := by
  apply Subtype.ext
  exact matrixTupleMap_twistedRelabel f σ g.1

end

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn
