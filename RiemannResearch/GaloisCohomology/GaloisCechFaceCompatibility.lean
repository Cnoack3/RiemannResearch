/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.GaloisCohomology.GaloisCechSchemeBridge
import RiemannResearch.GaloisCohomology.SingletonCechH1

/-!
# Finite Galois–Čech face compatibility

This module proves that the three Čech face morphisms on the singleton
finite-Galois cover correspond to the three tensor-coordinate face maps.
These are the scheme-level compatibility squares needed to transport the
Čech cocycle equation into the usual nonabelian Galois cocycle equation.

The degree-zero projection formulas needed for the gauge relation are also
proved here. `FiniteGaloisCechComparison` packages these results into the
canonical fixed-cover comparison datum.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace RiemannResearch.GaloisCohomology

universe u v u' v'

/-- The inverse chosen-product comparison followed by the first projection
is the image of the cartesian first projection. -/
lemma chosenProductComparison_inv_fst
    {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    {D : Type u'} [Category.{v'} D] [CartesianMonoidalCategory D]
    (F : C ⥤ D) (X Y : C) [PreservesLimit (pair X Y) F] :
    (((chosenProductTensorIso (F.obj X) (F.obj Y)).trans
      (CartesianMonoidalCategory.prodComparisonIso F X Y).symm).inv ≫
      (Limits.prod.fst : F.obj X ⨯ F.obj Y ⟶ F.obj X)) =
      F.map (SemiCartesianMonoidalCategory.fst X Y) := by
  rw [Iso.trans_inv, Category.assoc]
  have h :
      (chosenProductTensorIso (F.obj X) (F.obj Y)).inv ≫
        (Limits.prod.fst : F.obj X ⨯ F.obj Y ⟶ F.obj X) =
      SemiCartesianMonoidalCategory.fst (F.obj X) (F.obj Y) := by
    simpa [chosenProductTensorIso] using
      (limit.isoLimitCone_inv_π
        (⟨BinaryFan.mk
          (SemiCartesianMonoidalCategory.fst (F.obj X) (F.obj Y))
          (SemiCartesianMonoidalCategory.snd (F.obj X) (F.obj Y)),
          CartesianMonoidalCategory.tensorProductIsBinaryProduct
            (F.obj X) (F.obj Y)⟩ :
          LimitCone (pair (F.obj X) (F.obj Y)))
        (Discrete.mk WalkingPair.left))
  rw [h]
  exact CartesianMonoidalCategory.prodComparison_fst F X Y

/-- The inverse chosen-product comparison followed by the second projection
is the image of the cartesian second projection. -/
lemma chosenProductComparison_inv_snd
    {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    {D : Type u'} [Category.{v'} D] [CartesianMonoidalCategory D]
    (F : C ⥤ D) (X Y : C) [PreservesLimit (pair X Y) F] :
    (((chosenProductTensorIso (F.obj X) (F.obj Y)).trans
      (CartesianMonoidalCategory.prodComparisonIso F X Y).symm).inv ≫
      (Limits.prod.snd : F.obj X ⨯ F.obj Y ⟶ F.obj Y)) =
      F.map (SemiCartesianMonoidalCategory.snd X Y) := by
  rw [Iso.trans_inv, Category.assoc]
  have h :
      (chosenProductTensorIso (F.obj X) (F.obj Y)).inv ≫
        (Limits.prod.snd : F.obj X ⨯ F.obj Y ⟶ F.obj Y) =
      SemiCartesianMonoidalCategory.snd (F.obj X) (F.obj Y) := by
    simpa [chosenProductTensorIso] using
      (limit.isoLimitCone_inv_π
        (⟨BinaryFan.mk
          (SemiCartesianMonoidalCategory.fst (F.obj X) (F.obj Y))
          (SemiCartesianMonoidalCategory.snd (F.obj X) (F.obj Y)),
          CartesianMonoidalCategory.tensorProductIsBinaryProduct
            (F.obj X) (F.obj Y)⟩ :
          LimitCone (pair (F.obj X) (F.obj Y)))
        (Discrete.mk WalkingPair.right))
  rw [h]
  exact CartesianMonoidalCategory.prodComparison_snd F X Y

private abbrev X (K L : Type u) [CommRing K] [CommRing L] [Algebra K L] :
    (CommAlgCat K)ᵒᵖ :=
  Opposite.op (CommAlgCat.of K L)

private abbrev F (K : Type u) [CommRing K] :=
  AlgebraicGeometry.algSpec (CommRingCat.of K)

private def coreD
    (K L : Type u) [CommRing K] [CommRing L] [Algebra K L] :
    ((F K).obj (X K L) ⨯ (F K).obj (X K L)) ≅
      (F K).obj ((X K L) ⊗ (X K L)) := by
  let _ := AlgebraicGeometry.preservesLimitsOfSize_algSpec
    (R := CommRingCat.of K)
  exact
    (chosenProductTensorIso
      ((F K).obj (X K L)) ((F K).obj (X K L))).trans
      (CartesianMonoidalCategory.prodComparisonIso
        (F K) (X K L) (X K L)).symm

private def coreT
    (K L : Type u) [CommRing K] [CommRing L] [Algebra K L] :
    ((F K).obj (X K L) ⨯
      ((F K).obj (X K L) ⨯ (F K).obj (X K L))) ≅
      (F K).obj ((X K L) ⊗ ((X K L) ⊗ (X K L))) := by
  let _ := AlgebraicGeometry.preservesLimitsOfSize_algSpec
    (R := CommRingCat.of K)
  exact
    (Limits.prod.mapIso (Iso.refl _) (coreD K L)).trans
      ((chosenProductTensorIso
        ((F K).obj (X K L))
        ((F K).obj ((X K L) ⊗ (X K L)))).trans
      (CartesianMonoidalCategory.prodComparisonIso
        (F K) (X K L) ((X K L) ⊗ (X K L))).symm)

private def specOverMap (K : Type u) [CommRing K]
    {B C : Type u} [CommRing B] [CommRing C]
    [Algebra K B] [Algebra K C] (h : B →ₐ[K] C) :
    (AlgebraicGeometry.Spec (CommRingCat.of C)).asOver
        (AlgebraicGeometry.Spec (CommRingCat.of K)) ⟶
      (AlgebraicGeometry.Spec (CommRingCat.of B)).asOver
        (AlgebraicGeometry.Spec (CommRingCat.of K)) :=
  AlgebraicGeometry.Scheme.Hom.asOver
    (AlgebraicGeometry.Spec.map (CommRingCat.ofHom h.toRingHom))
    (AlgebraicGeometry.Spec (CommRingCat.of K))

private abbrev dLeft
    (K L : Type u) [CommRing K] [CommRing L] [Algebra K L] :
    L →ₐ[K] L ⊗[K] L :=
  Algebra.TensorProduct.includeLeft

private abbrev dRight
    (K L : Type u) [CommRing K] [CommRing L] [Algebra K L] :
    L →ₐ[K] L ⊗[K] L :=
  Algebra.TensorProduct.includeRight

private abbrev tZero
    (K L : Type u) [CommRing K] [CommRing L] [Algebra K L] :
    L →ₐ[K] L ⊗[K] (L ⊗[K] L) :=
  Algebra.TensorProduct.includeLeft

private abbrev tOne
    (K L : Type u) [CommRing K] [CommRing L] [Algebra K L] :
    L →ₐ[K] L ⊗[K] (L ⊗[K] L) :=
  (Algebra.TensorProduct.includeRight :
      (L ⊗[K] L) →ₐ[K] L ⊗[K] (L ⊗[K] L)).comp
    (Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] L)

private abbrev tTwo
    (K L : Type u) [CommRing K] [CommRing L] [Algebra K L] :
    L →ₐ[K] L ⊗[K] (L ⊗[K] L) :=
  (Algebra.TensorProduct.includeRight :
      (L ⊗[K] L) →ₐ[K] L ⊗[K] (L ⊗[K] L)).comp
    (Algebra.TensorProduct.includeRight : L →ₐ[K] L ⊗[K] L)

private abbrev U
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :=
  finiteGaloisCoverObject K L

section Projections

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L] [IsGalois K L]

lemma finiteGaloisDoubleOverlapIso_inv_fst :
    (finiteGaloisDoubleOverlapIso K L).inv ≫
        (Limits.prod.fst : U K L ⨯ U K L ⟶ U K L) =
      specOverMap K (dLeft K L) := by
  let _ := AlgebraicGeometry.preservesLimitsOfSize_algSpec
    (R := CommRingCat.of K)
  change
    (coreD K L).inv ≫
      (Limits.prod.fst :
        ((F K).obj (X K L) ⨯ (F K).obj (X K L)) ⟶
          (F K).obj (X K L)) = _
  rw [coreD, chosenProductComparison_inv_fst]
  rfl

lemma finiteGaloisDoubleOverlapIso_inv_snd :
    (finiteGaloisDoubleOverlapIso K L).inv ≫
        (Limits.prod.snd : U K L ⨯ U K L ⟶ U K L) =
      specOverMap K (dRight K L) := by
  let _ := AlgebraicGeometry.preservesLimitsOfSize_algSpec
    (R := CommRingCat.of K)
  change
    (coreD K L).inv ≫
      (Limits.prod.snd :
        ((F K).obj (X K L) ⨯ (F K).obj (X K L)) ⟶
          (F K).obj (X K L)) = _
  rw [coreD, chosenProductComparison_inv_snd]
  rfl

lemma finiteGaloisTripleOverlapIso_inv_zero :
    (finiteGaloisTripleOverlapIso K L).inv ≫
        (Limits.prod.fst : U K L ⨯ (U K L ⨯ U K L) ⟶ U K L) =
      specOverMap K (tZero K L) := by
  let _ := AlgebraicGeometry.preservesLimitsOfSize_algSpec
    (R := CommRingCat.of K)
  change
    (coreT K L).inv ≫
      (Limits.prod.fst :
        ((F K).obj (X K L) ⨯
          ((F K).obj (X K L) ⨯ (F K).obj (X K L))) ⟶
        (F K).obj (X K L)) = _
  rw [coreT, Iso.trans_inv, Category.assoc]
  simp only [Limits.prod.mapIso_inv, Limits.prod.map_fst,
    Iso.refl_inv, Category.comp_id]
  rw [chosenProductComparison_inv_fst]
  rfl

lemma finiteGaloisTripleOverlapIso_inv_one :
    (finiteGaloisTripleOverlapIso K L).inv ≫
        ((Limits.prod.snd :
          U K L ⨯ (U K L ⨯ U K L) ⟶ U K L ⨯ U K L) ≫
          (Limits.prod.fst : U K L ⨯ U K L ⟶ U K L)) =
      specOverMap K (tOne K L) := by
  let _ := AlgebraicGeometry.preservesLimitsOfSize_algSpec
    (R := CommRingCat.of K)
  change
    (coreT K L).inv ≫
      ((Limits.prod.snd :
        ((F K).obj (X K L) ⨯
          ((F K).obj (X K L) ⨯ (F K).obj (X K L))) ⟶
        ((F K).obj (X K L) ⨯ (F K).obj (X K L))) ≫
       (Limits.prod.fst :
        ((F K).obj (X K L) ⨯ (F K).obj (X K L)) ⟶
        (F K).obj (X K L))) = _
  calc
    _ = (F K).map
      (SemiCartesianMonoidalCategory.snd
        (X K L) ((X K L) ⊗ (X K L)) ≫
       SemiCartesianMonoidalCategory.fst
        (X K L) (X K L)) := by
      rw [coreT, Iso.trans_inv]
      simp only [Limits.prod.mapIso_inv, Category.assoc,
        Limits.prod.map_snd_assoc]
      rw [coreD, chosenProductComparison_inv_fst]
      rw [← Category.assoc, chosenProductComparison_inv_snd]
      rw [← (F K).map_comp]
    _ = _ := rfl

lemma finiteGaloisTripleOverlapIso_inv_two :
    (finiteGaloisTripleOverlapIso K L).inv ≫
        ((Limits.prod.snd :
          U K L ⨯ (U K L ⨯ U K L) ⟶ U K L ⨯ U K L) ≫
          (Limits.prod.snd : U K L ⨯ U K L ⟶ U K L)) =
      specOverMap K (tTwo K L) := by
  let _ := AlgebraicGeometry.preservesLimitsOfSize_algSpec
    (R := CommRingCat.of K)
  change
    (coreT K L).inv ≫
      ((Limits.prod.snd :
        ((F K).obj (X K L) ⨯
          ((F K).obj (X K L) ⨯ (F K).obj (X K L))) ⟶
        ((F K).obj (X K L) ⨯ (F K).obj (X K L))) ≫
       (Limits.prod.snd :
        ((F K).obj (X K L) ⨯ (F K).obj (X K L)) ⟶
        (F K).obj (X K L))) = _
  calc
    _ = (F K).map
      (SemiCartesianMonoidalCategory.snd
        (X K L) ((X K L) ⊗ (X K L)) ≫
       SemiCartesianMonoidalCategory.snd
        (X K L) (X K L)) := by
      rw [coreT, Iso.trans_inv]
      simp only [Limits.prod.mapIso_inv, Category.assoc,
        Limits.prod.map_snd_assoc]
      rw [coreD, chosenProductComparison_inv_snd]
      rw [← Category.assoc, chosenProductComparison_inv_snd]
      rw [← (F K).map_comp]
    _ = _ := rfl

end Projections

section FaceSquares

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L] [IsGalois K L]

/-- The coordinate face `01` as a morphism of affine schemes over `Spec K`. -/
def finiteGaloisFace01OverHom :
    (AlgebraicGeometry.Spec
      (CommRingCat.of (L ⊗[K] (L ⊗[K] L)))).asOver
        (AlgebraicGeometry.Spec (CommRingCat.of K)) ⟶
      (AlgebraicGeometry.Spec
        (CommRingCat.of (L ⊗[K] L))).asOver
          (AlgebraicGeometry.Spec (CommRingCat.of K)) :=
  specOverMap K (galoisCechFace01 K L)

/-- The coordinate face `02` as a morphism of affine schemes over `Spec K`. -/
def finiteGaloisFace02OverHom :
    (AlgebraicGeometry.Spec
      (CommRingCat.of (L ⊗[K] (L ⊗[K] L)))).asOver
        (AlgebraicGeometry.Spec (CommRingCat.of K)) ⟶
      (AlgebraicGeometry.Spec
        (CommRingCat.of (L ⊗[K] L))).asOver
          (AlgebraicGeometry.Spec (CommRingCat.of K)) :=
  specOverMap K (galoisCechFace02 K L)

/-- The coordinate face `12` as a morphism of affine schemes over `Spec K`. -/
def finiteGaloisFace12OverHom :
    (AlgebraicGeometry.Spec
      (CommRingCat.of (L ⊗[K] (L ⊗[K] L)))).asOver
        (AlgebraicGeometry.Spec (CommRingCat.of K)) ⟶
      (AlgebraicGeometry.Spec
        (CommRingCat.of (L ⊗[K] L))).asOver
          (AlgebraicGeometry.Spec (CommRingCat.of K)) :=
  specOverMap K (galoisCechFace12 K L)

/-- Compatibility of the `01` scheme face with tensor coordinates. -/
lemma finiteGaloisTripleFace01_compatibility :
    (finiteGaloisTripleOverlapIso K L).inv ≫
        singletonRightTripleFace01 (U K L) =
      finiteGaloisFace01OverHom K L ≫
        (finiteGaloisDoubleOverlapIso K L).inv := by
  apply Limits.prod.hom_ext
  · simp only [Category.assoc, singletonRightTripleFace01,
      singletonRightTripleProj0, singletonRightTripleProj1,
      Limits.prod.lift_fst]
    rw [finiteGaloisTripleOverlapIso_inv_zero,
      finiteGaloisDoubleOverlapIso_inv_fst]
    ext
    change
      AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (tZero K L).toRingHom) =
        AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (galoisCechFace01 K L).toRingHom) ≫
          AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (dLeft K L).toRingHom)
    rw [← AlgebraicGeometry.Spec.map_comp]
    rfl
  · simp only [Category.assoc, singletonRightTripleFace01,
      singletonRightTripleProj0, singletonRightTripleProj1,
      Limits.prod.lift_snd]
    rw [finiteGaloisTripleOverlapIso_inv_one,
      finiteGaloisDoubleOverlapIso_inv_snd]
    ext
    change
      AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (tOne K L).toRingHom) =
        AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (galoisCechFace01 K L).toRingHom) ≫
          AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (dRight K L).toRingHom)
    rw [← AlgebraicGeometry.Spec.map_comp]
    rfl

/-- Compatibility of the `02` scheme face with tensor coordinates. -/
lemma finiteGaloisTripleFace02_compatibility :
    (finiteGaloisTripleOverlapIso K L).inv ≫
        singletonRightTripleFace02 (U K L) =
      finiteGaloisFace02OverHom K L ≫
        (finiteGaloisDoubleOverlapIso K L).inv := by
  apply Limits.prod.hom_ext
  · simp only [Category.assoc, singletonRightTripleFace02,
      singletonRightTripleProj0, singletonRightTripleProj2,
      Limits.prod.lift_fst]
    rw [finiteGaloisTripleOverlapIso_inv_zero,
      finiteGaloisDoubleOverlapIso_inv_fst]
    ext
    change
      AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (tZero K L).toRingHom) =
        AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (galoisCechFace02 K L).toRingHom) ≫
          AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (dLeft K L).toRingHom)
    rw [← AlgebraicGeometry.Spec.map_comp]
    rfl
  · simp only [Category.assoc, singletonRightTripleFace02,
      singletonRightTripleProj0, singletonRightTripleProj2,
      Limits.prod.lift_snd]
    rw [finiteGaloisTripleOverlapIso_inv_two,
      finiteGaloisDoubleOverlapIso_inv_snd]
    ext
    change
      AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (tTwo K L).toRingHom) =
        AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (galoisCechFace02 K L).toRingHom) ≫
          AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (dRight K L).toRingHom)
    rw [← AlgebraicGeometry.Spec.map_comp]
    rfl

/-- Compatibility of the `12` scheme face with tensor coordinates. -/
lemma finiteGaloisTripleFace12_compatibility :
    (finiteGaloisTripleOverlapIso K L).inv ≫
        singletonRightTripleFace12 (U K L) =
      finiteGaloisFace12OverHom K L ≫
        (finiteGaloisDoubleOverlapIso K L).inv := by
  apply Limits.prod.hom_ext
  · simp only [Category.assoc, singletonRightTripleFace12,
      singletonRightTripleProj1, singletonRightTripleProj2,
      Limits.prod.lift_fst]
    rw [finiteGaloisTripleOverlapIso_inv_one,
      finiteGaloisDoubleOverlapIso_inv_fst]
    ext
    change
      AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (tOne K L).toRingHom) =
        AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (galoisCechFace12 K L).toRingHom) ≫
          AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (dLeft K L).toRingHom)
    rw [← AlgebraicGeometry.Spec.map_comp]
    rfl
  · simp only [Category.assoc, singletonRightTripleFace12,
      singletonRightTripleProj1, singletonRightTripleProj2,
      Limits.prod.lift_snd]
    rw [finiteGaloisTripleOverlapIso_inv_two,
      finiteGaloisDoubleOverlapIso_inv_snd]
    ext
    change
      AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (tTwo K L).toRingHom) =
        AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (galoisCechFace12 K L).toRingHom) ≫
          AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (dRight K L).toRingHom)
    rw [← AlgebraicGeometry.Spec.map_comp]
    rfl

end FaceSquares

section SectionFaces

variable (K L A : Type u)
variable [Field K] [Field L] [Algebra K L]
variable [CommRing A] [HopfAlgebra K A]
variable [FiniteDimensional K L] [IsGalois K L]

private abbrev P (K A : Type u)
    [Field K] [CommRing A] [HopfAlgebra K A] :=
  finiteGaloisAffineGroupPresheaf K A

/-- Pulling an affine point along an algebra map is precomposition by the
corresponding morphism of affine schemes. -/
lemma mapMulEquiv_pullAffinePointAlong
    {B C : Type u} [CommRing B] [CommRing C]
    [Algebra K B] [Algebra K C]
    (h : B →ₐ[K] C) (f : WithConv (A →ₐ[K] B)) :
    AlgebraicGeometry.Spec.mapMulEquiv
      (pullAffinePointAlong K A h f) =
    AlgebraicGeometry.Scheme.Hom.asOver
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom h.toRingHom))
      (AlgebraicGeometry.Spec (CommRingCat.of K)) ≫
      AlgebraicGeometry.Spec.mapMulEquiv f := by
  ext
  change
    AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (h.comp f.ofConv).toRingHom) =
    AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom h.toRingHom) ≫
    AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom f.ofConv.toRingHom)
  rw [← AlgebraicGeometry.Spec.map_comp]
  rfl

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp] lemma finiteGaloisTensorPointMulEquiv_symm_apply
    (s : (P K A).obj
      (Opposite.op
        ((AlgebraicGeometry.Spec
          (CommRingCat.of (L ⊗[K] L))).asOver
            (AlgebraicGeometry.Spec (CommRingCat.of K))))) :
    AlgebraicGeometry.Spec.mapMulEquiv
      ((finiteGaloisTensorPointMulEquiv K L A).symm s) = s :=
  (finiteGaloisTensorPointMulEquiv K L A).apply_symm_apply s

/-- The represented section transport sends the categorical 01 face to
the tensor-coordinate 01 face. -/
lemma finiteGaloisTripleFace01_section_compatibility
    (s : (P K A).obj (Opposite.op (U K L ⨯ U K L))) :
    finiteGaloisTripleOverlapSectionMulEquiv K L A
        ((P K A).map (singletonRightTripleFace01 (U K L)).op s) =
      pullAffinePointAlong K A (galoisCechFace01 K L)
        (finiteGaloisDoubleOverlapSectionMulEquiv K L A s) := by
  apply (finiteGaloisTripleTensorPointMulEquiv K L A).injective
  simp only [finiteGaloisTripleOverlapSectionMulEquiv, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply]
  change
    ((finiteGaloisTripleOverlapIso K L).inv ≫
      singletonRightTripleFace01 (U K L)) ≫ s =
    AlgebraicGeometry.Spec.mapMulEquiv
      (pullAffinePointAlong K A (galoisCechFace01 K L)
        (finiteGaloisDoubleOverlapSectionMulEquiv K L A s))
  rw [mapMulEquiv_pullAffinePointAlong,
    finiteGaloisTripleFace01_compatibility]
  simp only [finiteGaloisDoubleOverlapSectionMulEquiv, MulEquiv.trans_apply,
    finiteGaloisTensorPointMulEquiv_symm_apply]
  rfl

/-- The represented section transport sends the categorical 02 face to
the tensor-coordinate 02 face. -/
lemma finiteGaloisTripleFace02_section_compatibility
    (s : (P K A).obj (Opposite.op (U K L ⨯ U K L))) :
    finiteGaloisTripleOverlapSectionMulEquiv K L A
        ((P K A).map (singletonRightTripleFace02 (U K L)).op s) =
      pullAffinePointAlong K A (galoisCechFace02 K L)
        (finiteGaloisDoubleOverlapSectionMulEquiv K L A s) := by
  apply (finiteGaloisTripleTensorPointMulEquiv K L A).injective
  simp only [finiteGaloisTripleOverlapSectionMulEquiv, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply]
  change
    ((finiteGaloisTripleOverlapIso K L).inv ≫
      singletonRightTripleFace02 (U K L)) ≫ s =
    AlgebraicGeometry.Spec.mapMulEquiv
      (pullAffinePointAlong K A (galoisCechFace02 K L)
        (finiteGaloisDoubleOverlapSectionMulEquiv K L A s))
  rw [mapMulEquiv_pullAffinePointAlong,
    finiteGaloisTripleFace02_compatibility]
  simp only [finiteGaloisDoubleOverlapSectionMulEquiv, MulEquiv.trans_apply,
    finiteGaloisTensorPointMulEquiv_symm_apply]
  rfl

/-- The represented section transport sends the categorical 12 face to
the tensor-coordinate 12 face. -/
lemma finiteGaloisTripleFace12_section_compatibility
    (s : (P K A).obj (Opposite.op (U K L ⨯ U K L))) :
    finiteGaloisTripleOverlapSectionMulEquiv K L A
        ((P K A).map (singletonRightTripleFace12 (U K L)).op s) =
      pullAffinePointAlong K A (galoisCechFace12 K L)
        (finiteGaloisDoubleOverlapSectionMulEquiv K L A s) := by
  apply (finiteGaloisTripleTensorPointMulEquiv K L A).injective
  simp only [finiteGaloisTripleOverlapSectionMulEquiv, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply]
  change
    ((finiteGaloisTripleOverlapIso K L).inv ≫
      singletonRightTripleFace12 (U K L)) ≫ s =
    AlgebraicGeometry.Spec.mapMulEquiv
      (pullAffinePointAlong K A (galoisCechFace12 K L)
        (finiteGaloisDoubleOverlapSectionMulEquiv K L A s))
  rw [mapMulEquiv_pullAffinePointAlong,
    finiteGaloisTripleFace12_compatibility]
  simp only [finiteGaloisDoubleOverlapSectionMulEquiv, MulEquiv.trans_apply,
    finiteGaloisTensorPointMulEquiv_symm_apply]
  rfl

end SectionFaces

section GaugeProjections

open RiemannResearch.AlgebraicGeometry

variable (K L A : Type u)
variable [Field K] [Field L] [Algebra K L]
variable [CommRing A] [HopfAlgebra K A]
variable [FiniteDimensional K L] [IsGalois K L]

private abbrev U0 := finiteGaloisCoverObject K L
private abbrev P0 := finiteGaloisAffineGroupPresheaf K A

local instance finiteGaloisCoverHomGroup : Group
    (((AlgebraicGeometry.Spec (CommRingCat.of L)).asOver
        (AlgebraicGeometry.Spec (CommRingCat.of K))) ⟶
      ((AlgebraicGeometry.Spec (CommRingCat.of A)).asOver
        (AlgebraicGeometry.Spec (CommRingCat.of K)))) :=
  ((P0 K A).obj (Opposite.op (U0 K L))).str

/-- Sections on the finite-Galois cover are the affine L-points of the
represented group. -/
def finiteGaloisCoverSectionMulEquiv :
    (P0 K A).obj (Opposite.op (U0 K L)) ≃*
      AffineGaloisPoint K L A := by
  change
    (((AlgebraicGeometry.Spec (CommRingCat.of L)).asOver
        (AlgebraicGeometry.Spec (CommRingCat.of K))) ⟶
      ((AlgebraicGeometry.Spec (CommRingCat.of A)).asOver
        (AlgebraicGeometry.Spec (CommRingCat.of K)))) ≃*
      WithConv (A →ₐ[K] L)
  exact AlgebraicGeometry.Spec.mapMulEquiv.symm

@[simp] lemma mapMulEquiv_finiteGaloisCoverSectionMulEquiv_apply
    (g : (P0 K A).obj (Opposite.op (U0 K L))) :
    AlgebraicGeometry.Spec.mapMulEquiv
        (finiteGaloisCoverSectionMulEquiv K L A g) = g :=
  AlgebraicGeometry.Spec.mapMulEquiv.apply_symm_apply g

/-- Pullback of a cover section along the first overlap projection is
precomposition with the left tensor inclusion. -/
lemma finiteGaloisDoubleOverlap_fst_section_compatibility
    (g : (P0 K A).obj (Opposite.op (U0 K L))) :
    finiteGaloisDoubleOverlapSectionMulEquiv K L A
        ((P0 K A).map
          (Limits.prod.fst : U0 K L ⨯ U0 K L ⟶ U0 K L).op g) =
      pullAffinePointAlong K A
        (Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] L)
        (finiteGaloisCoverSectionMulEquiv K L A g) := by
  apply (finiteGaloisTensorPointMulEquiv K L A).injective
  simp only [finiteGaloisDoubleOverlapSectionMulEquiv, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply]
  change
    ((finiteGaloisDoubleOverlapIso K L).inv ≫
      (Limits.prod.fst : U0 K L ⨯ U0 K L ⟶ U0 K L)) ≫ g =
    AlgebraicGeometry.Spec.mapMulEquiv
      (pullAffinePointAlong K A
        (Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] L)
        (finiteGaloisCoverSectionMulEquiv K L A g))
  rw [mapMulEquiv_pullAffinePointAlong,
    finiteGaloisDoubleOverlapIso_inv_fst,
    mapMulEquiv_finiteGaloisCoverSectionMulEquiv_apply]
  rfl

/-- Pullback of a cover section along the second overlap projection is
precomposition with the right tensor inclusion. -/
lemma finiteGaloisDoubleOverlap_snd_section_compatibility
    (g : (P0 K A).obj (Opposite.op (U0 K L))) :
    finiteGaloisDoubleOverlapSectionMulEquiv K L A
        ((P0 K A).map
          (Limits.prod.snd : U0 K L ⨯ U0 K L ⟶ U0 K L).op g) =
      pullAffinePointAlong K A
        (Algebra.TensorProduct.includeRight : L →ₐ[K] L ⊗[K] L)
        (finiteGaloisCoverSectionMulEquiv K L A g) := by
  apply (finiteGaloisTensorPointMulEquiv K L A).injective
  simp only [finiteGaloisDoubleOverlapSectionMulEquiv, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply]
  change
    ((finiteGaloisDoubleOverlapIso K L).inv ≫
      (Limits.prod.snd : U0 K L ⨯ U0 K L ⟶ U0 K L)) ≫ g =
    AlgebraicGeometry.Spec.mapMulEquiv
      (pullAffinePointAlong K A
        (Algebra.TensorProduct.includeRight : L →ₐ[K] L ⊗[K] L)
        (finiteGaloisCoverSectionMulEquiv K L A g))
  rw [mapMulEquiv_pullAffinePointAlong,
    finiteGaloisDoubleOverlapIso_inv_snd,
    mapMulEquiv_finiteGaloisCoverSectionMulEquiv_apply]
  rfl

/-- In Galois coordinates, the left tensor inclusion is the constant point. -/
lemma galoisDoubleOverlap_includeLeft_point
    (g : AffineGaloisPoint K L A) (σ : L ≃ₐ[K] L) :
    galoisDoubleOverlapPointMulEquiv K L A
        (pullAffinePointAlong K A
          (Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] L) g) σ =
      g := by
  ext x
  simp [galoisDoubleOverlapPointMulEquiv_apply, pullAffinePointAlong,
    galoisTensorEquiv_tmul_apply]

/-- In Galois coordinates, the right tensor inclusion is the Galois translate
of the point. -/
lemma galoisDoubleOverlap_includeRight_point
    (g : AffineGaloisPoint K L A) (σ : L ≃ₐ[K] L) :
    galoisDoubleOverlapPointMulEquiv K L A
        (pullAffinePointAlong K A
          (Algebra.TensorProduct.includeRight : L →ₐ[K] L ⊗[K] L) g) σ =
      σ • g := by
  ext x
  simp [galoisDoubleOverlapPointMulEquiv_apply, pullAffinePointAlong,
    galoisTensorEquiv_tmul_apply]
  change σ (g.ofConv x) = σ (g.ofConv x)
  rfl

end GaugeProjections

end RiemannResearch.GaloisCohomology

end
