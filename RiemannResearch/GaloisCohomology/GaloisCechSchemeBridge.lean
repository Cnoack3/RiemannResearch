/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.GaloisCohomology.GaloisAffineCechCoordinates
import RiemannResearch.GaloisCohomology.SingletonCechH1

/-!
# Scheme-level finite-Galois Čech coordinates

This file transports sections of the represented affine-group presheaf on the
chosen categorical double overlap of `Spec L → Spec K` to algebra maps into
`L ⊗[K] L`. It uses Mathlib's cartesian comparison for `algSpec`; the
underlying scheme isomorphism is the canonical `pullbackSpecIso`.
-/

namespace RiemannResearch.GaloisCohomology

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open RiemannResearch.AlgebraicGeometry

universe u v

noncomputable section

/-- A group-object isomorphism induces a multiplicative equivalence on
underlying groups. -/
def grpIsoToMulEquiv {X Y : GrpCat} (e : X ≅ Y) : X ≃* Y where
  toFun := e.hom.hom
  invFun := e.inv.hom
  left_inv := e.hom_inv_id_apply
  right_inv := e.inv_hom_id_apply
  map_mul' := e.hom.hom.map_mul

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- The chosen categorical product is canonically isomorphic to the tensor
object of a cartesian monoidal category. -/
def chosenProductTensorIso (X Y : C) : (X ⨯ Y) ≅ (X ⊗ Y) :=
  limit.isoLimitCone
    ⟨BinaryFan.mk (SemiCartesianMonoidalCategory.fst X Y)
        (SemiCartesianMonoidalCategory.snd X Y),
      CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y⟩

variable (K L A : Type u)
variable [Field K] [Field L] [Algebra K L]
variable [CommRing A] [HopfAlgebra K A]
variable [FiniteDimensional K L] [IsGalois K L]

/-- The finite-Galois covering object `Spec L` over `Spec K`, with the
singleton index universe pinned. -/
abbrev finiteGaloisCoverObject
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    Over (AlgebraicGeometry.Spec (CommRingCat.of K)) :=
  ((finiteGaloisFpqcCover K L :
    FpqcCover (CommRingCat.of K) PUnit.{1}).obj PUnit.unit)

/-- The represented affine-group presheaf over `Spec K`. -/
abbrev finiteGaloisAffineGroupPresheaf :
    (Over (AlgebraicGeometry.Spec (CommRingCat.of K)))ᵒᵖ ⥤ GrpCat :=
  affineGroupPresheaf (CommRingCat.of K) (CommRingCat.of A)

private abbrev finiteGaloisCommAlgObject :
    (CommAlgCat K)ᵒᵖ :=
  Opposite.op (CommAlgCat.of K L)

private abbrev finiteGaloisAlgSpec :=
  AlgebraicGeometry.algSpec (CommRingCat.of K)

/-- The chosen product of two copies of the finite-Galois covering object is
canonically the affine spectrum of `L ⊗[K] L`.

Mathlib's theorem `prodComparisonIso_algSpec_inv_left` identifies the
underlying scheme map of the cartesian comparison with
`pullbackSpecIso K L L`. -/
def finiteGaloisDoubleOverlapIso :
    ((finiteGaloisCoverObject K L) ⨯
      (finiteGaloisCoverObject K L)) ≅
    (AlgebraicGeometry.Spec
      (CommRingCat.of (TensorProduct K L L))).asOver
        (AlgebraicGeometry.Spec (CommRingCat.of K)) := by
  letI := AlgebraicGeometry.preservesLimitsOfSize_algSpec
    (R := CommRingCat.of K)
  change
    (((finiteGaloisAlgSpec K).obj (finiteGaloisCommAlgObject K L)) ⨯
      ((finiteGaloisAlgSpec K).obj (finiteGaloisCommAlgObject K L))) ≅
      (finiteGaloisAlgSpec K).obj
        ((finiteGaloisCommAlgObject K L) ⊗
          (finiteGaloisCommAlgObject K L))
  exact
    (chosenProductTensorIso
      ((finiteGaloisAlgSpec K).obj (finiteGaloisCommAlgObject K L))
      ((finiteGaloisAlgSpec K).obj
        (finiteGaloisCommAlgObject K L))).trans
      (CartesianMonoidalCategory.prodComparisonIso
        (finiteGaloisAlgSpec K)
        (finiteGaloisCommAlgObject K L)
        (finiteGaloisCommAlgObject K L)).symm

/-- The value of the represented affine-group presheaf on the explicit
tensor-square affine overlap is multiplicatively equivalent to algebra maps
from `A` into `L ⊗[K] L`. -/
def finiteGaloisTensorPointMulEquiv :
    WithConv (A →ₐ[K] TensorProduct K L L) ≃*
      (finiteGaloisAffineGroupPresheaf K A).obj
        (Opposite.op
          ((AlgebraicGeometry.Spec
            (CommRingCat.of (TensorProduct K L L))).asOver
              (AlgebraicGeometry.Spec (CommRingCat.of K)))) := by
  letI : Group
      (((AlgebraicGeometry.Spec
        (CommRingCat.of (TensorProduct K L L))).asOver
          (AlgebraicGeometry.Spec (CommRingCat.of K))) ⟶
        ((AlgebraicGeometry.Spec (CommRingCat.of A)).asOver
          (AlgebraicGeometry.Spec (CommRingCat.of K)))) :=
    ((finiteGaloisAffineGroupPresheaf K A).obj
      (Opposite.op
        ((AlgebraicGeometry.Spec
          (CommRingCat.of (TensorProduct K L L))).asOver
            (AlgebraicGeometry.Spec (CommRingCat.of K))))).str
  change
    WithConv (A →ₐ[K] TensorProduct K L L) ≃*
      (((AlgebraicGeometry.Spec
        (CommRingCat.of (TensorProduct K L L))).asOver
          (AlgebraicGeometry.Spec (CommRingCat.of K))) ⟶
        ((AlgebraicGeometry.Spec (CommRingCat.of A)).asOver
          (AlgebraicGeometry.Spec (CommRingCat.of K))))
  exact AlgebraicGeometry.Spec.mapMulEquiv

/-- Sections of the represented affine-group presheaf on the chosen double
overlap are multiplicatively equivalent to algebra maps into
`L ⊗[K] L`. -/
def finiteGaloisDoubleOverlapSectionMulEquiv :
    (finiteGaloisAffineGroupPresheaf K A).obj
        (Opposite.op
          ((finiteGaloisCoverObject K L) ⨯
            (finiteGaloisCoverObject K L))) ≃*
      WithConv (A →ₐ[K] TensorProduct K L L) :=
  (grpIsoToMulEquiv
      ((finiteGaloisAffineGroupPresheaf K A).mapIso
        (finiteGaloisDoubleOverlapIso K L).symm.op)).trans
    (finiteGaloisTensorPointMulEquiv K L A).symm

/-- The chosen right-associated triple product of the finite-Galois covering
object is canonically the affine spectrum of
`L ⊗[K] (L ⊗[K] L)`. -/
def finiteGaloisTripleOverlapIso :
    ((finiteGaloisCoverObject K L) ⨯
      ((finiteGaloisCoverObject K L) ⨯
        (finiteGaloisCoverObject K L))) ≅
    (AlgebraicGeometry.Spec
      (CommRingCat.of
        (TensorProduct K L (TensorProduct K L L)))).asOver
      (AlgebraicGeometry.Spec (CommRingCat.of K)) := by
  letI := AlgebraicGeometry.preservesLimitsOfSize_algSpec
    (R := CommRingCat.of K)
  change
    (((finiteGaloisAlgSpec K).obj (finiteGaloisCommAlgObject K L)) ⨯
      (((finiteGaloisAlgSpec K).obj (finiteGaloisCommAlgObject K L)) ⨯
        ((finiteGaloisAlgSpec K).obj (finiteGaloisCommAlgObject K L)))) ≅
      (finiteGaloisAlgSpec K).obj
        (Opposite.op
          (CommAlgCat.of K
            (TensorProduct K L (TensorProduct K L L))))
  exact
    (CategoryTheory.Limits.prod.mapIso
      (Iso.refl _)
      (finiteGaloisDoubleOverlapIso K L)).trans
    ((chosenProductTensorIso
      ((finiteGaloisAlgSpec K).obj (finiteGaloisCommAlgObject K L))
      ((finiteGaloisAlgSpec K).obj
        (Opposite.op
          (CommAlgCat.of K (TensorProduct K L L))))).trans
      (CartesianMonoidalCategory.prodComparisonIso
        (finiteGaloisAlgSpec K)
        (finiteGaloisCommAlgObject K L)
        (Opposite.op
          (CommAlgCat.of K (TensorProduct K L L)))).symm)

/-- The value of the represented affine-group presheaf on the explicit
right-associated tensor-cube overlap is multiplicatively equivalent to
algebra maps from `A` into `L ⊗[K] (L ⊗[K] L)`. -/
def finiteGaloisTripleTensorPointMulEquiv :
    WithConv
        (A →ₐ[K] TensorProduct K L (TensorProduct K L L)) ≃*
      (finiteGaloisAffineGroupPresheaf K A).obj
        (Opposite.op
          ((AlgebraicGeometry.Spec
            (CommRingCat.of
              (TensorProduct K L (TensorProduct K L L)))).asOver
            (AlgebraicGeometry.Spec (CommRingCat.of K)))) := by
  letI : Group
      (((AlgebraicGeometry.Spec
        (CommRingCat.of
          (TensorProduct K L (TensorProduct K L L)))).asOver
        (AlgebraicGeometry.Spec (CommRingCat.of K))) ⟶
      ((AlgebraicGeometry.Spec (CommRingCat.of A)).asOver
        (AlgebraicGeometry.Spec (CommRingCat.of K)))) :=
    ((finiteGaloisAffineGroupPresheaf K A).obj
      (Opposite.op
        ((AlgebraicGeometry.Spec
          (CommRingCat.of
            (TensorProduct K L (TensorProduct K L L)))).asOver
          (AlgebraicGeometry.Spec (CommRingCat.of K))))).str
  change
    WithConv
        (A →ₐ[K] TensorProduct K L (TensorProduct K L L)) ≃*
      (((AlgebraicGeometry.Spec
        (CommRingCat.of
          (TensorProduct K L (TensorProduct K L L)))).asOver
        (AlgebraicGeometry.Spec (CommRingCat.of K))) ⟶
      ((AlgebraicGeometry.Spec (CommRingCat.of A)).asOver
        (AlgebraicGeometry.Spec (CommRingCat.of K))))
  exact AlgebraicGeometry.Spec.mapMulEquiv

/-- Sections on the chosen right-associated triple overlap are
multiplicatively equivalent to algebra maps into the tensor cube. -/
def finiteGaloisTripleOverlapSectionMulEquiv :
    (finiteGaloisAffineGroupPresheaf K A).obj
      (Opposite.op
        ((finiteGaloisCoverObject K L) ⨯
          ((finiteGaloisCoverObject K L) ⨯
            (finiteGaloisCoverObject K L)))) ≃*
      WithConv
        (A →ₐ[K] TensorProduct K L (TensorProduct K L L)) :=
  (grpIsoToMulEquiv
      ((finiteGaloisAffineGroupPresheaf K A).mapIso
        (finiteGaloisTripleOverlapIso K L).symm.op)).trans
    (finiteGaloisTripleTensorPointMulEquiv K L A).symm

/-- Sections on the chosen double overlap, directly expressed as
Galois-indexed affine-group points. -/
def finiteGaloisDoubleOverlapGaloisMulEquiv :
    (finiteGaloisAffineGroupPresheaf K A).obj
        (Opposite.op
          ((finiteGaloisCoverObject K L) ⨯
            (finiteGaloisCoverObject K L))) ≃*
      ((L ≃ₐ[K] L) → AffineGaloisPoint K L A) :=
  (finiteGaloisDoubleOverlapSectionMulEquiv K L A).trans
    (galoisDoubleOverlapPointMulEquiv K L A)

/-- Sections on the chosen right-associated triple overlap, directly
expressed as two-variable Galois-indexed affine-group points. -/
def finiteGaloisTripleOverlapGaloisMulEquiv :
    (finiteGaloisAffineGroupPresheaf K A).obj
      (Opposite.op
        ((finiteGaloisCoverObject K L) ⨯
          ((finiteGaloisCoverObject K L) ⨯
            (finiteGaloisCoverObject K L)))) ≃*
      ((L ≃ₐ[K] L) → (L ≃ₐ[K] L) →
        AffineGaloisPoint K L A) :=
  (finiteGaloisTripleOverlapSectionMulEquiv K L A).trans
    (galoisTripleOverlapPointMulEquiv K L A)

end

end RiemannResearch.GaloisCohomology
