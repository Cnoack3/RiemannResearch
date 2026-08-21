/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.AlgebraicGeometry.AlgebraicGroupGaloisContinuity
import RiemannResearch.GaloisCohomology.ContinuousNonabelianH1Refinement
import RiemannResearch.GaloisCohomology.GaloisAffineCechCoordinates

/-!
# Transport of finite-stage cocycles to finite Galois extensions

This module transports an action-compatible finite quotient cocycle for the
absolute Galois group across the quotient/fixed-field Galois-group
equivalence and the fixed-geometric-point/fixed-field-point equivalence.

Source for the finite-stage interpretation: J.-P. Serre,
*Galois Cohomology*, Chapter I, §5.  The formal construction combines the
infinite Galois correspondence with the affine coordinate comparison proved
in `AlgebraicGroupGaloisContinuity`.
-/

namespace RiemannResearch.AlgebraicGeometry

open RiemannResearch.GaloisCohomology

universe u

noncomputable section

namespace AbsoluteGaloisOpenNormalSubgroup

variable (K : Type u) [Field K] [PerfectField K]
variable (H : OpenNormalSubgroup (Field.absoluteGaloisGroup K))

local instance : IsGalois K (fixedField K H) :=
  fixedField_isGalois K H

/-- On a quotient class represented by an absolute-Galois element, the
quotient/fixed-field equivalence is restriction to the fixed field. -/
@[simp] theorem quotientEquivGaloisGroup_mk
    (σ : Field.absoluteGaloisGroup K) :
    quotientEquivGaloisGroup K H (QuotientGroup.mk σ) =
      AlgEquiv.restrictNormalHom (fixedField K H) σ := by
  rfl

end AbsoluteGaloisOpenNormalSubgroup

namespace GaloisH1

open ContinuousNonabelianCocycle
open ContinuousNonabelianCocycle.ActionCompatibleFiniteQuotientFactorization
open AbsoluteGaloisOpenNormalSubgroup

variable (K A : Type u) [Field K] [PerfectField K]
variable [CommRing A] [HopfAlgebra K A]
variable
  {a : ContinuousNonabelianCocycle
    (Field.absoluteGaloisGroup K) (AlgebraicGroupGeometricPoints K A)}

local instance (H : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) :
    IsGalois K (fixedField K H) :=
  fixedField_isGalois K H

/-- The coefficient equivalence attached to an action-compatible finite
stage. -/
def finiteStageCoefficientEquiv
    (D : ActionCompatibleFiniteQuotientFactorization a) :
    D.FixedCoefficientGroup ≃*
      AffineGaloisPoint K (fixedField K D.subgroup) A :=
  fixedGeometricPointMulEquivFixedFieldPoint K D.subgroup A

namespace Refinement

variable {D E F : ActionCompatibleFiniteQuotientFactorization a}

/-- Refining an open normal kernel enlarges its finite Galois fixed field. -/
theorem fixedField_le (r : Refinement D E) :
    fixedField K E.subgroup ≤ fixedField K D.subgroup := by
  intro x hx
  rw [IntermediateField.mem_fixedField_iff
    (D.subgroup : Subgroup (Field.absoluteGaloisGroup K))]
  intro σ hσ
  have hx' :=
    (IntermediateField.mem_fixedField_iff
      (E.subgroup : Subgroup (Field.absoluteGaloisGroup K)) x).mp hx
  exact hx' σ (r.subgroup_le hσ)

/-- The field embedding induced contravariantly by a refinement. -/
def fixedFieldEmbedding (r : Refinement D E) :
    fixedField K E.subgroup →ₐ[K] fixedField K D.subgroup :=
  IntermediateField.inclusion (fixedField_le K A r)

/-- The refinement fixed-field embedding is the identity after coercion to
the algebraic closure. -/
@[simp] theorem coe_fixedFieldEmbedding
    (r : Refinement D E) (x : fixedField K E.subgroup) :
    ((fixedFieldEmbedding K A r x : fixedField K D.subgroup) :
      AlgebraicClosure K) = x := by
  exact IntermediateField.coe_inclusion (fixedField_le K A r) x

/-- The identity refinement induces the identity fixed-field embedding. -/
@[simp] theorem fixedFieldEmbedding_refl
    (D : ActionCompatibleFiniteQuotientFactorization a)
    (x : fixedField K D.subgroup) :
    fixedFieldEmbedding K A (Refinement.refl D) x = x := by
  apply Subtype.ext
  rfl

/-- Fixed-field embeddings compose contravariantly with refinements. -/
@[simp] theorem fixedFieldEmbedding_trans
    (r : Refinement D E) (s : Refinement E F)
    (x : fixedField K F.subgroup) :
    fixedFieldEmbedding K A (r.trans s) x =
      fixedFieldEmbedding K A r (fixedFieldEmbedding K A s x) := by
  apply Subtype.ext
  rfl

/-- Under the quotient/fixed-field Galois equivalences, the quotient
transition map is restriction along the refinement fixed-field embedding. -/
theorem fixedFieldEmbedding_equivariant
    (r : Refinement D E)
    (q : Field.absoluteGaloisGroup K ⧸
      (D.subgroup : Subgroup (Field.absoluteGaloisGroup K)))
    (x : fixedField K E.subgroup) :
    fixedFieldEmbedding K A r
        (quotientEquivGaloisGroup K E.subgroup (r.quotientMap q) x) =
      quotientEquivGaloisGroup K D.subgroup q
        (fixedFieldEmbedding K A r x) := by
  refine Quotient.inductionOn' q ?_
  intro σ
  apply Subtype.ext
  change
    (fixedField K E.subgroup).val
        (quotientEquivGaloisGroup K E.subgroup
          (QuotientGroup.mk σ) x) =
      (fixedField K D.subgroup).val
        (quotientEquivGaloisGroup K D.subgroup
          (QuotientGroup.mk σ) (fixedFieldEmbedding K A r x))
  rw [quotientEquivGaloisGroup_mk, quotientEquivGaloisGroup_mk]
  change (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) at σ
  calc
    (fixedField K E.subgroup).val
        ((AlgEquiv.restrictNormalHom (fixedField K E.subgroup)) σ x) =
      σ ((fixedField K E.subgroup).val x) :=
        AlgEquiv.restrictNormalHom_apply (fixedField K E.subgroup) σ x
    _ = σ ((fixedField K D.subgroup).val (fixedFieldEmbedding K A r x)) :=
      congrArg σ (coe_fixedFieldEmbedding K A r x).symm
    _ = (fixedField K D.subgroup).val
        ((AlgEquiv.restrictNormalHom (fixedField K D.subgroup)) σ
          (fixedFieldEmbedding K A r x)) :=
      (AlgEquiv.restrictNormalHom_apply (fixedField K D.subgroup) σ
        (fixedFieldEmbedding K A r x)).symm

/-- Extend affine-group points along the fixed-field embedding attached to a
refinement. -/
def affinePointMap (r : Refinement D E) :
    AffineGaloisPoint K (fixedField K E.subgroup) A →*
      AffineGaloisPoint K (fixedField K D.subgroup) A where
  toFun f := WithConv.toConv ((fixedFieldEmbedding K A r).comp f.ofConv)
  map_one' := by
    apply WithConv.ofConv_injective
    rfl
  map_mul' f g := by
    apply WithConv.ofConv_injective
    exact AlgHom.comp_convMul_distrib (fixedFieldEmbedding K A r) f g

/-- The identity refinement induces the identity affine-point map. -/
@[simp] theorem affinePointMap_refl
    (D : ActionCompatibleFiniteQuotientFactorization a)
    (f : AffineGaloisPoint K (fixedField K D.subgroup) A) :
    affinePointMap K A (Refinement.refl D) f = f := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro y
  apply Subtype.ext
  rfl

/-- Affine-point extension maps compose with refinements. -/
@[simp] theorem affinePointMap_trans
    (r : Refinement D E) (s : Refinement E F)
    (f : AffineGaloisPoint K (fixedField K F.subgroup) A) :
    affinePointMap K A (r.trans s) f =
      affinePointMap K A r (affinePointMap K A s f) := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro y
  apply Subtype.ext
  rfl

/-- Affine-point extension is equivariant for the Galois restriction map
corresponding to a refinement. -/
theorem affinePointMap_smul
    (r : Refinement D E)
    (q : Field.absoluteGaloisGroup K ⧸
      (D.subgroup : Subgroup (Field.absoluteGaloisGroup K)))
    (f : AffineGaloisPoint K (fixedField K E.subgroup) A) :
    affinePointMap K A r
        (quotientEquivGaloisGroup K E.subgroup (r.quotientMap q) • f) =
      quotientEquivGaloisGroup K D.subgroup q •
        affinePointMap K A r f := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro y
  exact fixedFieldEmbedding_equivariant K A r q (f.ofConv y)

/-- Refinement of fixed geometric coefficients agrees with extension of the
corresponding affine points along the inclusion of fixed fields. -/
theorem finiteStageCoefficientEquiv_fixedCoefficientMap
    (r : Refinement D E) (x : E.FixedCoefficientGroup) :
    finiteStageCoefficientEquiv K A D (r.fixedCoefficientMap x) =
      affinePointMap K A r (finiteStageCoefficientEquiv K A E x) := by
  apply (fixedFieldPointMulEquivFixedGeometricPoint K D.subgroup A).injective
  change
    fixedFieldPointMulEquivFixedGeometricPoint K D.subgroup A
        ((fixedFieldPointMulEquivFixedGeometricPoint K D.subgroup A).symm
          (r.fixedCoefficientMap x)) =
      fixedFieldPointMulEquivFixedGeometricPoint K D.subgroup A
        (affinePointMap K A r
          (finiteStageCoefficientEquiv K A E x))
  rw [(fixedFieldPointMulEquivFixedGeometricPoint K D.subgroup A).apply_symm_apply]
  apply Subtype.ext
  have hE := congrArg Subtype.val
    ((fixedFieldPointMulEquivFixedGeometricPoint K E.subgroup A).apply_symm_apply x)
  change x.1 = _
  rw [← hE]
  apply (geometricPointCoordinateMulEquiv K A).injective
  change
    geometricPointCoordinateMulEquiv K A
        (fixedFieldPointToGeometricPoint K E.subgroup A
          (finiteStageCoefficientEquiv K A E x)) =
      geometricPointCoordinateMulEquiv K A
        (fixedFieldPointToGeometricPoint K D.subgroup A
          (affinePointMap K A r (finiteStageCoefficientEquiv K A E x)))
  rw [geometricPointCoordinateMulEquiv_fixedFieldPointToGeometricPoint,
    geometricPointCoordinateMulEquiv_fixedFieldPointToGeometricPoint]
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro y
  exact (coe_fixedFieldEmbedding K A r
    ((finiteStageCoefficientEquiv K A E x).ofConv y)).symm

end Refinement

/-- The forward fixed-field point inclusion intertwines the finite Galois
action with the quotient action on kernel-fixed geometric points. -/
theorem fixedFieldPointToFixedGeometricPoint_smul
    (D : ActionCompatibleFiniteQuotientFactorization a)
    (q : Field.absoluteGaloisGroup K ⧸
      (D.subgroup : Subgroup (Field.absoluteGaloisGroup K)))
    (f : AffineGaloisPoint K (fixedField K D.subgroup) A) :
    fixedFieldPointToFixedGeometricPoint K D.subgroup A
        (quotientEquivGaloisGroup K D.subgroup q • f) =
      q • fixedFieldPointToFixedGeometricPoint K D.subgroup A f := by
  refine Quotient.inductionOn' q ?_
  intro σ
  apply Subtype.ext
  apply (geometricPointCoordinateEquiv K A).injective
  change
    geometricPointToCoordinate K A
        (fixedFieldPointToGeometricPoint K D.subgroup A
          (quotientEquivGaloisGroup K D.subgroup
            (QuotientGroup.mk σ) • f)) =
      geometricPointToCoordinate K A
        (σ • fixedFieldPointToGeometricPoint K D.subgroup A f)
  rw [geometricPointToCoordinate_smul,
    geometricPointToCoordinate_fixedFieldPointToGeometricPoint,
    geometricPointToCoordinate_fixedFieldPointToGeometricPoint]
  apply AlgHom.ext
  intro x
  change
    (fixedField K D.subgroup).val
        ((quotientEquivGaloisGroup K D.subgroup
          (QuotientGroup.mk σ)) (f.ofConv x)) =
      σ.toAlgHom ((fixedField K D.subgroup).val (f.ofConv x))
  rw [AbsoluteGaloisOpenNormalSubgroup.quotientEquivGaloisGroup_mk]
  exact AlgEquiv.restrictNormalHom_apply
    (fixedField K D.subgroup) σ (f.ofConv x)

/-- The inverse coefficient equivalence is equivariant for the quotient and
finite-Galois actions. -/
theorem finiteStageCoefficientEquiv_smul
    (D : ActionCompatibleFiniteQuotientFactorization a)
    (q : Field.absoluteGaloisGroup K ⧸
      (D.subgroup : Subgroup (Field.absoluteGaloisGroup K)))
    (x : D.FixedCoefficientGroup) :
    finiteStageCoefficientEquiv K A D (q • x) =
      quotientEquivGaloisGroup K D.subgroup q •
        finiteStageCoefficientEquiv K A D x := by
  apply (fixedFieldPointMulEquivFixedGeometricPoint
    K D.subgroup A).injective
  change
    fixedFieldPointMulEquivFixedGeometricPoint K D.subgroup A
        ((fixedFieldPointMulEquivFixedGeometricPoint K D.subgroup A).symm
          (q • x)) =
      fixedFieldPointMulEquivFixedGeometricPoint K D.subgroup A
        (quotientEquivGaloisGroup K D.subgroup q •
          (fixedFieldPointMulEquivFixedGeometricPoint K D.subgroup A).symm x)
  rw [(fixedFieldPointMulEquivFixedGeometricPoint
      K D.subgroup A).apply_symm_apply]
  change
    q • x =
      fixedFieldPointToFixedGeometricPoint K D.subgroup A
        (quotientEquivGaloisGroup K D.subgroup q •
          (fixedFieldPointMulEquivFixedGeometricPoint K D.subgroup A).symm x)
  rw [fixedFieldPointToFixedGeometricPoint_smul,
    show
      fixedFieldPointToFixedGeometricPoint K D.subgroup A
          ((fixedFieldPointMulEquivFixedGeometricPoint K D.subgroup A).symm x) =
        x by
      exact (fixedFieldPointMulEquivFixedGeometricPoint
        K D.subgroup A).apply_symm_apply x]

/-- The genuine finite-Galois cocycle obtained from a continuous
absolute-Galois cocycle and one action-compatible finite stage. -/
def finiteStageDescendedCocycle
    (D : ActionCompatibleFiniteQuotientFactorization a) :
    NonabelianCocycle
      ((fixedField K D.subgroup) ≃ₐ[K] (fixedField K D.subgroup))
      (AffineGaloisPoint K (fixedField K D.subgroup) A) where
  toFun := fun τ =>
    finiteStageCoefficientEquiv K A D
      (D.descendedCocycle
        ((quotientEquivGaloisGroup K D.subgroup).symm τ))
  map_mul' := by
    intro σ τ
    let eQ := quotientEquivGaloisGroup K D.subgroup
    let eG := finiteStageCoefficientEquiv K A D
    calc
      eG (D.descendedCocycle (eQ.symm (σ * τ))) =
          eG (D.descendedCocycle (eQ.symm σ * eQ.symm τ)) := by
            rw [map_mul]
      _ = eG
          (D.descendedCocycle (eQ.symm σ) *
            eQ.symm σ • D.descendedCocycle (eQ.symm τ)) := by
            rw [D.descendedCocycle.map_mul']
      _ = eG (D.descendedCocycle (eQ.symm σ)) *
          eG (eQ.symm σ • D.descendedCocycle (eQ.symm τ)) := by
            rw [map_mul]
      _ = eG (D.descendedCocycle (eQ.symm σ)) *
          eQ (eQ.symm σ) • eG (D.descendedCocycle (eQ.symm τ)) := by
            rw [finiteStageCoefficientEquiv_smul]
      _ = eG (D.descendedCocycle (eQ.symm σ)) *
          σ • eG (D.descendedCocycle (eQ.symm τ)) := by
            rw [eQ.apply_symm_apply]

/-- Evaluation formula for the transported finite-stage cocycle. -/
@[simp] theorem finiteStageDescendedCocycle_apply
    (D : ActionCompatibleFiniteQuotientFactorization a)
    (τ : (fixedField K D.subgroup) ≃ₐ[K] (fixedField K D.subgroup)) :
    finiteStageDescendedCocycle K A D τ =
      finiteStageCoefficientEquiv K A D
        (D.descendedCocycle
          ((quotientEquivGaloisGroup K D.subgroup).symm τ)) := by
  rfl

namespace Refinement

variable {D E : ActionCompatibleFiniteQuotientFactorization a}

/-- The transported finite-Galois cocycles agree pointwise under the Galois
restriction and affine-point extension maps induced by a refinement. -/
@[simp] theorem affinePointMap_finiteStageDescendedCocycle
    (r : Refinement D E)
    (q : Field.absoluteGaloisGroup K ⧸
      (D.subgroup : Subgroup (Field.absoluteGaloisGroup K))) :
    Refinement.affinePointMap K A r
        (finiteStageDescendedCocycle K A E
          (quotientEquivGaloisGroup K E.subgroup
            (r.quotientMap q))) =
      finiteStageDescendedCocycle K A D
        (quotientEquivGaloisGroup K D.subgroup q) := by
  rw [finiteStageDescendedCocycle_apply,
    finiteStageDescendedCocycle_apply,
    (quotientEquivGaloisGroup K E.subgroup).symm_apply_apply,
    (quotientEquivGaloisGroup K D.subgroup).symm_apply_apply,
    ← Refinement.finiteStageCoefficientEquiv_fixedCoefficientMap K A r,
    r.fixedCoefficientMap_descendedCocycle]

end Refinement

/-- Pulling the transported finite-Galois cocycle back to the absolute
Galois group and including its fixed-field values recovers the original
continuous cocycle pointwise. -/
theorem finiteStageDescendedCocycle_pullback
    (D : ActionCompatibleFiniteQuotientFactorization a)
    (σ : Field.absoluteGaloisGroup K) :
    ((fixedFieldPointMulEquivFixedGeometricPoint K D.subgroup A
        (finiteStageDescendedCocycle K A D
          (quotientEquivGaloisGroup K D.subgroup
            (QuotientGroup.mk σ))) :
      FixedGeometricPointGroup K D.subgroup A) :
        AlgebraicGroupGeometricPoints K A) = a σ := by
  rw [finiteStageDescendedCocycle_apply,
    (quotientEquivGaloisGroup K D.subgroup).symm_apply_apply]
  calc
    ((fixedFieldPointMulEquivFixedGeometricPoint K D.subgroup A
        (finiteStageCoefficientEquiv K A D
          (D.descendedCocycle (QuotientGroup.mk σ))) :
      FixedGeometricPointGroup K D.subgroup A) :
        AlgebraicGroupGeometricPoints K A) =
      ((D.descendedCocycle (QuotientGroup.mk σ) :
        D.FixedCoefficientGroup) : AlgebraicGroupGeometricPoints K A) := by
          exact congrArg Subtype.val
            ((fixedFieldPointMulEquivFixedGeometricPoint K D.subgroup A).apply_symm_apply
              (D.descendedCocycle (QuotientGroup.mk σ)))
    _ = a σ := D.coe_descendedCocycle_mk σ

end GaloisH1

end

end RiemannResearch.AlgebraicGeometry
