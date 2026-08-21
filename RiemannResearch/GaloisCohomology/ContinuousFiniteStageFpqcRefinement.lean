/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.GaloisCohomology.ContinuousFiniteStageFpqc

/-!
# Refinement naturality for continuous finite-stage fpqc cocycles

This module transports refinements of action-compatible finite quotient
factorizations to refinements of their singleton finite-Galois fpqc covers.
It records the induced tensor-square overlap map and the resulting pullback
formula for the universal Čech section.

Source for the finite-stage interpretation: J.-P. Serre,
*Galois Cohomology*, Chapter I, §5. The overlap naturality calculation is the
affine-spectrum form of functoriality of the tensor square.
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

/-- The morphism of singleton fixed-field covering objects induced by a
refinement of continuous finite stages. -/
def finiteStageFixedCoverHom (r : Refinement D E) :
    finiteGaloisCoverObject K
        (AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup) ⟶
      finiteGaloisCoverObject K
        (AbsoluteGaloisOpenNormalSubgroup.fixedField K E.subgroup) :=
  Over.homMk
    (_root_.AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom
        (AlgebraicGeometry.GaloisH1.Refinement.fixedFieldEmbedding
          K A r).toRingHom))
    (by
      change
        _root_.AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom
              (AlgebraicGeometry.GaloisH1.Refinement.fixedFieldEmbedding
                K A r).toRingHom) ≫
          _root_.AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom
              (algebraMap K
                (AbsoluteGaloisOpenNormalSubgroup.fixedField
                  K E.subgroup))) =
        _root_.AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom
            (algebraMap K
              (AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup)))
      rw [← _root_.AlgebraicGeometry.Spec.map_comp]
      apply congrArg _root_.AlgebraicGeometry.Spec.map
      ext x
      rfl)

/-- Refining the open normal kernel gives a refinement of the corresponding
singleton finite-Galois fpqc covers. -/
def finiteStageFpqcRefinement (r : Refinement D E) :
    (finiteGaloisFpqcCover K
      (AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup)).Refinement
    (finiteGaloisFpqcCover K
      (AbsoluteGaloisOpenNormalSubgroup.fixedField K E.subgroup)) where
  index := fun _ => PUnit.unit
  hom := fun _ => finiteStageFixedCoverHom K A r

/-- The tensor-square algebra map induced by the fixed-field embedding of a
finite-stage refinement. -/
def finiteStageDoubleTensorHom (r : Refinement D E) :
    (AbsoluteGaloisOpenNormalSubgroup.fixedField K E.subgroup ⊗[K]
        AbsoluteGaloisOpenNormalSubgroup.fixedField K E.subgroup) →ₐ[K]
      (AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup ⊗[K]
        AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup) :=
  Algebra.TensorProduct.map
    (AlgebraicGeometry.GaloisH1.Refinement.fixedFieldEmbedding K A r)
    (AlgebraicGeometry.GaloisH1.Refinement.fixedFieldEmbedding K A r)

/-- The affine-spectrum morphism attached to the tensor-square map of a
finite-stage refinement. -/
def finiteStageDoubleOverlapHom (r : Refinement D E) :
    (_root_.AlgebraicGeometry.Spec
      (CommRingCat.of
        (AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup ⊗[K]
          AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup))).asOver
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of K)) ⟶
    (_root_.AlgebraicGeometry.Spec
      (CommRingCat.of
        (AbsoluteGaloisOpenNormalSubgroup.fixedField K E.subgroup ⊗[K]
          AbsoluteGaloisOpenNormalSubgroup.fixedField K E.subgroup))).asOver
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of K)) :=
  _root_.AlgebraicGeometry.Scheme.Hom.asOver
    (_root_.AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom
        (finiteStageDoubleTensorHom K A r).toRingHom))
    (_root_.AlgebraicGeometry.Spec (CommRingCat.of K))

/-- The refinement map on double overlaps agrees with the tensor square of
the fixed-field embedding under the canonical affine overlap isomorphisms. -/
theorem finiteStageDoubleOverlapIso_naturality (r : Refinement D E) :
    (finiteGaloisDoubleOverlapIso K
      (AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup)).inv ≫
        prod.map (finiteStageFixedCoverHom K A r)
          (finiteStageFixedCoverHom K A r) =
      finiteStageDoubleOverlapHom K A r ≫
        (finiteGaloisDoubleOverlapIso K
          (AbsoluteGaloisOpenNormalSubgroup.fixedField K E.subgroup)).inv := by
  apply prod.hom_ext
  · rw [Category.assoc, prod.map_fst, ← Category.assoc,
      finiteGaloisDoubleOverlapIso_inv_fst, Category.assoc,
      finiteGaloisDoubleOverlapIso_inv_fst]
    ext
    change
      _root_.AlgebraicGeometry.Spec.map _ ≫
          _root_.AlgebraicGeometry.Spec.map _ =
        _root_.AlgebraicGeometry.Spec.map _ ≫
          _root_.AlgebraicGeometry.Spec.map _
    rw [← _root_.AlgebraicGeometry.Spec.map_comp,
      ← _root_.AlgebraicGeometry.Spec.map_comp]
    apply congrArg _root_.AlgebraicGeometry.Spec.map
    ext x
    rfl
  · rw [Category.assoc, prod.map_snd, ← Category.assoc,
      finiteGaloisDoubleOverlapIso_inv_snd, Category.assoc,
      finiteGaloisDoubleOverlapIso_inv_snd]
    ext
    change
      _root_.AlgebraicGeometry.Spec.map _ ≫
          _root_.AlgebraicGeometry.Spec.map _ =
        _root_.AlgebraicGeometry.Spec.map _ ≫
          _root_.AlgebraicGeometry.Spec.map _
    rw [← _root_.AlgebraicGeometry.Spec.map_comp,
      ← _root_.AlgebraicGeometry.Spec.map_comp]
    apply congrArg _root_.AlgebraicGeometry.Spec.map
    ext x
    rfl

/-- On the universal double-overlap section, Čech pullback along the
finite-stage cover refinement is the presheaf map induced by the product of
the two fixed-cover morphisms. -/
theorem singletonSection_pullbackOneCocycle
    (r : Refinement D E)
    (γ : PresheafOfGroups.OneCocycle
      (finiteGaloisAffineGroupPresheaf K A)
      (fun _ : PUnit.{1} =>
        finiteGaloisCoverObject K
          (AbsoluteGaloisOpenNormalSubgroup.fixedField K E.subgroup))) :
    singletonOneCochainSection (finiteGaloisAffineGroupPresheaf K A)
        (finiteGaloisCoverObject K
          (AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup))
        ((finiteStageFpqcRefinement K A r).pullbackOneCocycle
          γ).toOneCochain =
      (finiteGaloisAffineGroupPresheaf K A).map
        (prod.map (finiteStageFixedCoverHom K A r)
          (finiteStageFixedCoverHom K A r)).op
        (singletonOneCochainSection
          (finiteGaloisAffineGroupPresheaf K A)
          (finiteGaloisCoverObject K
            (AbsoluteGaloisOpenNormalSubgroup.fixedField K E.subgroup))
          γ.toOneCochain) := by
  symm
  rw [show
    prod.map (finiteStageFixedCoverHom K A r)
        (finiteStageFixedCoverHom K A r) =
      prod.lift
        (prod.fst ≫ finiteStageFixedCoverHom K A r)
        (prod.snd ≫ finiteStageFixedCoverHom K A r) by
      apply prod.hom_ext
      · rw [prod.map_fst, prod.lift_fst]
      · rw [prod.map_snd, prod.lift_snd],
    map_singletonOneCochainSection]
  rfl

end Refinement

end

end RiemannResearch.GaloisCohomology
