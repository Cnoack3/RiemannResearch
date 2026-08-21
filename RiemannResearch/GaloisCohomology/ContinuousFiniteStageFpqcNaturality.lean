/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.GaloisCohomology.ContinuousFiniteStageFpqcRefinement

/-!
# Naturality of continuous finite-stage fpqc cocycles

This module proves that the explicit singleton fixed-field Čech cocycle is
natural under refinement of an action-compatible finite quotient
factorization. Consequently its fixed-cover and global fpqc `H¹` classes are
independent of the chosen finite factorization.

Source for the finite-stage interpretation: J.-P. Serre,
*Galois Cohomology*, Chapter I, §5. The proof is the explicit affine tensor
calculation for restriction between finite Galois fixed fields.
-/

namespace RiemannResearch.GaloisCohomology

open CategoryTheory
open CategoryTheory.Limits
open RiemannResearch.AlgebraicGeometry
open ContinuousNonabelianCocycle
open ContinuousNonabelianCocycle.ActionCompatibleFiniteQuotientFactorization
open scoped TensorProduct

universe u

noncomputable section

variable (K A : Type u) [Field K] [PerfectField K]
variable [CommRing A] [HopfAlgebra K A]
variable
  {a : ContinuousNonabelianCocycle
    (Field.absoluteGaloisGroup K) (AlgebraicGroupGeometricPoints K A)}

local instance (H : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) :
    FiniteDimensional K (AbsoluteGaloisOpenNormalSubgroup.fixedField K H) :=
  AbsoluteGaloisOpenNormalSubgroup.fixedField_finiteDimensional K H

local instance (H : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) :
    IsGalois K (AbsoluteGaloisOpenNormalSubgroup.fixedField K H) :=
  AbsoluteGaloisOpenNormalSubgroup.fixedField_isGalois K H

namespace Refinement

variable {D E : ActionCompatibleFiniteQuotientFactorization a}

-- The represented-overlap normalization is elaboration-intensive.
set_option maxHeartbeats 1000000 in
/-- Pullback along the double-overlap refinement is postcomposition of the
tensor coordinate with the tensor square of the fixed-field embedding. -/
theorem finiteStageDoubleOverlapSection_naturality
    (r : Refinement D E)
    (s : (finiteGaloisAffineGroupPresheaf K A).obj
      (Opposite.op
        (finiteGaloisCoverObject K
            (AbsoluteGaloisOpenNormalSubgroup.fixedField K E.subgroup) ⨯
          finiteGaloisCoverObject K
            (AbsoluteGaloisOpenNormalSubgroup.fixedField K E.subgroup)))) :
    finiteGaloisDoubleOverlapSectionMulEquiv K
        (AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup) A
        ((finiteGaloisAffineGroupPresheaf K A).map
          (prod.map (finiteStageFixedCoverHom K A r)
            (finiteStageFixedCoverHom K A r)).op s) =
      pullAffinePointAlong K A (finiteStageDoubleTensorHom K A r)
        (finiteGaloisDoubleOverlapSectionMulEquiv K
          (AbsoluteGaloisOpenNormalSubgroup.fixedField K E.subgroup) A s) := by
  apply (finiteGaloisTensorPointMulEquiv K
    (AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup) A).injective
  simp only [finiteGaloisDoubleOverlapSectionMulEquiv,
    MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  change
    ((finiteGaloisDoubleOverlapIso K
        (AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup)).inv ≫
      prod.map (finiteStageFixedCoverHom K A r)
        (finiteStageFixedCoverHom K A r)) ≫ s =
      _root_.AlgebraicGeometry.Spec.mapMulEquiv
        (pullAffinePointAlong K A (finiteStageDoubleTensorHom K A r)
          (finiteGaloisDoubleOverlapSectionMulEquiv K
            (AbsoluteGaloisOpenNormalSubgroup.fixedField K E.subgroup) A s))
  rw [mapMulEquiv_pullAffinePointAlong,
    finiteStageDoubleOverlapIso_naturality]
  calc
    (finiteStageDoubleOverlapHom K A r ≫
        (finiteGaloisDoubleOverlapIso K
          (AbsoluteGaloisOpenNormalSubgroup.fixedField K E.subgroup)).inv) ≫ s =
      finiteStageDoubleOverlapHom K A r ≫
        ((finiteGaloisDoubleOverlapIso K
          (AbsoluteGaloisOpenNormalSubgroup.fixedField K E.subgroup)).inv ≫
            s) := Category.assoc _ _ _
    _ = finiteStageDoubleOverlapHom K A r ≫
        _root_.AlgebraicGeometry.Spec.mapMulEquiv
          (finiteGaloisDoubleOverlapSectionMulEquiv K
            (AbsoluteGaloisOpenNormalSubgroup.fixedField K E.subgroup) A s) := by
              rw [finiteGaloisDoubleOverlapSectionMulEquiv_specMap]
    _ = _ := rfl

/-- The finite-Galois tensor decomposition is natural for the tensor square
of a refinement fixed-field embedding. -/
theorem finiteStageGaloisTensor_naturality
    (r : Refinement D E)
    (z : AbsoluteGaloisOpenNormalSubgroup.fixedField K E.subgroup ⊗[K]
      AbsoluteGaloisOpenNormalSubgroup.fixedField K E.subgroup)
    (q : Field.absoluteGaloisGroup K ⧸
      (D.subgroup : Subgroup (Field.absoluteGaloisGroup K))) :
    galoisTensorEquiv K
        (AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup)
        (finiteStageDoubleTensorHom K A r z)
        (AbsoluteGaloisOpenNormalSubgroup.quotientEquivGaloisGroup
          K D.subgroup q) =
      AlgebraicGeometry.GaloisH1.Refinement.fixedFieldEmbedding K A r
        (galoisTensorEquiv K
          (AbsoluteGaloisOpenNormalSubgroup.fixedField K E.subgroup) z
          (AbsoluteGaloisOpenNormalSubgroup.quotientEquivGaloisGroup
            K E.subgroup (r.quotientMap q))) := by
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro x y
    simp only [finiteStageDoubleTensorHom, Algebra.TensorProduct.map_tmul,
      galoisTensorEquiv_tmul_apply, map_mul]
    rw [AlgebraicGeometry.GaloisH1.Refinement.fixedFieldEmbedding_equivariant]
  · intro x y hx hy
    simp only [map_add, Pi.add_apply, hx, hy]

/-- Galois evaluation of a pulled-back double-overlap section agrees with
restriction of Galois automorphisms and extension of affine points. -/
theorem finiteStageDoubleOverlapGalois_naturality
    (r : Refinement D E)
    (s : (finiteGaloisAffineGroupPresheaf K A).obj
      (Opposite.op
        (finiteGaloisCoverObject K
            (AbsoluteGaloisOpenNormalSubgroup.fixedField K E.subgroup) ⨯
          finiteGaloisCoverObject K
            (AbsoluteGaloisOpenNormalSubgroup.fixedField K E.subgroup))))
    (q : Field.absoluteGaloisGroup K ⧸
      (D.subgroup : Subgroup (Field.absoluteGaloisGroup K))) :
    finiteGaloisDoubleOverlapGaloisMulEquiv K
        (AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup) A
        ((finiteGaloisAffineGroupPresheaf K A).map
          (prod.map (finiteStageFixedCoverHom K A r)
            (finiteStageFixedCoverHom K A r)).op s)
        (AbsoluteGaloisOpenNormalSubgroup.quotientEquivGaloisGroup
          K D.subgroup q) =
      AlgebraicGeometry.GaloisH1.Refinement.affinePointMap K A r
        (finiteGaloisDoubleOverlapGaloisMulEquiv K
          (AbsoluteGaloisOpenNormalSubgroup.fixedField K E.subgroup) A s
          (AbsoluteGaloisOpenNormalSubgroup.quotientEquivGaloisGroup
            K E.subgroup (r.quotientMap q))) := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro x
  rw [finiteGaloisDoubleOverlapGaloisMulEquiv_apply_apply]
  change _ =
    AlgebraicGeometry.GaloisH1.Refinement.fixedFieldEmbedding K A r
      ((finiteGaloisDoubleOverlapGaloisMulEquiv K
        (AbsoluteGaloisOpenNormalSubgroup.fixedField K E.subgroup) A s
        (AbsoluteGaloisOpenNormalSubgroup.quotientEquivGaloisGroup
          K E.subgroup (r.quotientMap q))).ofConv x)
  rw [finiteGaloisDoubleOverlapGaloisMulEquiv_apply_apply,
    finiteStageDoubleOverlapSection_naturality]
  exact finiteStageGaloisTensor_naturality K A r _ q

end Refinement

/-- Galois evaluation of the explicit fixed-cover representative is the
transported finite-stage cocycle itself. -/
theorem finiteStageFixedCoverCocycle_galois_apply
    (D : ActionCompatibleFiniteQuotientFactorization a)
    (τ : (AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup) ≃ₐ[K]
      (AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup)) :
    finiteGaloisDoubleOverlapGaloisMulEquiv K
        (AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup) A
        (singletonOneCochainSection (finiteGaloisAffineGroupPresheaf K A)
          (finiteGaloisCoverObject K
            (AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup))
          (finiteStageFixedCoverCocycle K A D).toOneCochain) τ =
      AlgebraicGeometry.GaloisH1.finiteStageDescendedCocycle K A D τ := by
  change
    (finiteGaloisFpqcGaloisCechComparison K
      (AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup) A).cocycleEquiv
        (finiteStageFixedCoverCocycle K A D) τ = _
  rw [finiteStageFixedCoverCocycle_cocycleEquiv,
    galoisCechCocycleEquiv_symm_apply]

namespace Refinement

variable {D E : ActionCompatibleFiniteQuotientFactorization a}

/-- Čech pullback along a finite-stage refinement sends the coarser explicit
fixed-cover cocycle to the finer explicit fixed-cover cocycle. -/
theorem finiteStageFpqcRefinement_pullbackOneCocycle
    (r : Refinement D E) :
    (finiteStageFpqcRefinement K A r).pullbackOneCocycle
        (finiteStageFixedCoverCocycle K A E) =
      finiteStageFixedCoverCocycle K A D := by
  apply (finiteGaloisFixedCoverCocycleEquiv K
    (AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup) A).injective
  apply GaloisCechCocycle.ext
  intro τ
  rw [finiteGaloisFixedCoverCocycleEquiv_apply,
    singletonSection_pullbackOneCocycle,
    finiteGaloisFixedCoverCocycleEquiv_apply]
  let q :=
    (AbsoluteGaloisOpenNormalSubgroup.quotientEquivGaloisGroup
      K D.subgroup).symm τ
  rw [show
    τ = AbsoluteGaloisOpenNormalSubgroup.quotientEquivGaloisGroup
        K D.subgroup q by
      exact
        ((AbsoluteGaloisOpenNormalSubgroup.quotientEquivGaloisGroup
          K D.subgroup).apply_symm_apply τ).symm]
  rw [finiteStageDoubleOverlapGalois_naturality,
    finiteStageFixedCoverCocycle_galois_apply,
    finiteStageFixedCoverCocycle_galois_apply]
  exact
    AlgebraicGeometry.GaloisH1.Refinement.affinePointMap_finiteStageDescendedCocycle
      K A r q

/-- The map on fixed-cover nonabelian `H¹` induced by a finite-stage
refinement sends the coarser explicit class to the finer explicit class. -/
theorem finiteStageFpqcRefinement_pullbackH1
    (r : Refinement D E) :
    (finiteStageFpqcRefinement K A r).pullbackH1
        (finiteStageFixedCoverCocycle K A E).class =
      (finiteStageFixedCoverCocycle K A D).class := by
  rw [FpqcCover.Refinement.pullbackH1_class,
    finiteStageFpqcRefinement_pullbackOneCocycle]

/-- The global fpqc class attached to a finite stage is unchanged when that
stage is refined. -/
theorem finiteStageGlobalFpqcH1_eq_of_refinement
    (r : Refinement D E) :
    finiteStageGlobalFpqcH1 K A E =
      finiteStageGlobalFpqcH1 K A D := by
  unfold finiteStageGlobalFpqcH1
  calc
    FpqcH1.classOf (CommRingCat.of K) (CommRingCat.of A)
        (finiteGaloisFpqcCover K
          (AbsoluteGaloisOpenNormalSubgroup.fixedField K E.subgroup))
        (finiteStageFixedCoverCocycle K A E).class =
      FpqcH1.classOf (CommRingCat.of K) (CommRingCat.of A)
        (finiteGaloisFpqcCover K
          (AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup))
        ((finiteStageFpqcRefinement K A r).pullbackH1
          (finiteStageFixedCoverCocycle K A E).class) :=
      FpqcH1.classOf_pullback (CommRingCat.of K) (CommRingCat.of A)
        (finiteStageFpqcRefinement K A r)
        (finiteStageFixedCoverCocycle K A E).class
    _ = _ := by rw [finiteStageFpqcRefinement_pullbackH1]

end Refinement

/-- The global fpqc class attached to a continuous cocycle is independent of
the chosen action-compatible finite quotient factorization. -/
theorem finiteStageGlobalFpqcH1_independent
    (D E : ActionCompatibleFiniteQuotientFactorization a) :
    finiteStageGlobalFpqcH1 K A D =
      finiteStageGlobalFpqcH1 K A E := by
  calc
    finiteStageGlobalFpqcH1 K A D =
        finiteStageGlobalFpqcH1 K A (D.commonRefinement E) :=
      Refinement.finiteStageGlobalFpqcH1_eq_of_refinement K A
        (commonRefinementLeft D E)
    _ = finiteStageGlobalFpqcH1 K A E :=
      (Refinement.finiteStageGlobalFpqcH1_eq_of_refinement K A
        (commonRefinementRight D E)).symm

end

end RiemannResearch.GaloisCohomology
