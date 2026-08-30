/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E7.QuaternionAzumayaMatrix

/-!
# Nondegenerate uniform quaternion algebras are Azumaya

`QuaternionAzumayaMatrix` constructs and verifies a two-sided inverse for
the matrix of Mathlib's canonical left-right action on
`QuaternionAlgebra k c₁ c₂ c₃`. This file transports that coordinate
certificate back through all basis equivalences and packages the result as
a genuine `IsAzumaya` theorem.

The nondegeneracy hypotheses are exactly

* `c₃ ≠ 0`, and
* `4 c₁ + c₂² ≠ 0`.

No centrality, simplicity, or Azumaya hypothesis is assumed.
-/

open RiemannResearch.E7.QuaternionHermitian.QuaternionAzumayaMatrix

namespace RiemannResearch.E7.QuaternionHermitian
namespace QuaternionAzumaya

universe u

variable {k : Type u} [Field k]

/-- Reindex pair-valued coordinates in row-major order. -/
noncomputable def pairToFlat : (Pair4 → k) ≃ₗ[k] (Fin 16 → k) where
  toFun f i := f (pair4EquivFin16.symm i)
  invFun g p := g (pair4EquivFin16 p)
  left_inv f := by
    funext p
    simp
  right_inv g := by
    funext i
    simp
  map_add' f g := rfl
  map_smul' a f := rfl

@[simp] theorem pairToFlat_apply (f : Pair4 → k) (i : Fin 16) :
    pairToFlat f i = f (pair4EquivFin16.symm i) := rfl

@[simp] theorem pairToFlat_symm_apply (g : Fin 16 → k) (p : Pair4) :
    pairToFlat.symm g p = g (pair4EquivFin16 p) := rfl

@[simp] theorem pairToFlat_symm_single (j : Fin 16) :
    pairToFlat.symm (Pi.single j (1 : k)) =
      Pi.single (pair4EquivFin16.symm j) 1 := by
  ext p
  by_cases h : p = pair4EquivFin16.symm j
  · subst p
    simp
  · have h' : pair4EquivFin16 p ≠ j := by
      intro hp
      apply h
      simpa using congrArg pair4EquivFin16.symm hp
    simp [h, h']

/-- Conjugate the pair-indexed canonical coordinate map to flat coordinates. -/
noncomputable def canonicalFlatVectorMap (p : QuaternionParameters k) :
    (Fin 16 → k) →ₗ[k] (Fin 16 → k) :=
  pairToFlat.toLinearMap.comp <|
    (canonicalVectorMap p).comp pairToFlat.symm.toLinearMap

/-- The standard matrix of the conjugated coordinate map is exactly the
verified row-major canonical matrix. -/
theorem toMatrix'_canonicalFlatVectorMap (p : QuaternionParameters k) :
    LinearMap.toMatrix' (canonicalFlatVectorMap p) =
      canonicalFlatMatrix p := by
  ext i j
  rw [LinearMap.toMatrix'_apply]
  simp [canonicalFlatVectorMap, canonicalFlatMatrix, Matrix.reindex_apply,
    canonicalPairMatrix_apply]

/-- The flat canonical coordinate map is bijective under the expected
nondegeneracy hypotheses. -/
theorem canonicalFlatVectorMap_bijective
    (p : QuaternionParameters k)
    (hc : p.c₃ ≠ 0) (hdisc : 4 * p.c₁ + p.c₂ ^ 2 ≠ 0) :
    Function.Bijective (canonicalFlatVectorMap p) := by
  have h := canonicalFlatMatrix_mulVec_bijective p hc hdisc
  rw [← toMatrix'_canonicalFlatVectorMap p] at h
  have heq :
      Matrix.mulVec (LinearMap.toMatrix' (canonicalFlatVectorMap p)) =
        (canonicalFlatVectorMap p : (Fin 16 → k) → (Fin 16 → k)) := by
    funext x
    exact LinearMap.toMatrix'_mulVec (canonicalFlatVectorMap p) x
  rw [← heq]
  exact h

/-- Undoing the row-major reindexing preserves bijectivity. -/
theorem canonicalVectorMap_bijective
    (p : QuaternionParameters k)
    (hc : p.c₃ ≠ 0) (hdisc : 4 * p.c₁ + p.c₂ ^ 2 ≠ 0) :
    Function.Bijective (canonicalVectorMap p) := by
  have hflat := canonicalFlatVectorMap_bijective p hc hdisc
  have heq :
      (canonicalVectorMap p : (Pair4 → k) → (Pair4 → k)) =
        fun x => pairToFlat.symm (canonicalFlatVectorMap p (pairToFlat x)) := by
    funext x
    simp [canonicalFlatVectorMap, LinearMap.comp_apply]
  rw [heq]
  exact pairToFlat.symm.bijective.comp
    (hflat.comp pairToFlat.bijective)

/-- Coordinates on the endomorphism algebra obtained from the quaternion
basis and row-major matrix flattening. -/
noncomputable def endomorphismCoordinates (p : QuaternionParameters k) :
    Module.End k (PresentedQuaternion p) ≃ₗ[k] (Pair4 → k) :=
  (LinearMap.toMatrix (quaternionBasis p) (quaternionBasis p)).trans
    matrixUncurry

/-- Transport coordinate bijectivity back to Mathlib's actual canonical
left-right algebra homomorphism. -/
theorem mulLeftRight_bijective_of_coordinate_bijective
    (p : QuaternionParameters k)
    (hcoord : Function.Bijective (canonicalVectorMap p)) :
    Function.Bijective (AlgHom.mulLeftRight k (PresentedQuaternion p)) := by
  have heq :
      (AlgHom.mulLeftRight k (PresentedQuaternion p)).toLinearMap =
        (endomorphismCoordinates p).symm.toLinearMap.comp
          ((canonicalVectorMap p).comp
            (quaternionTensorBasis p).equivFun.toLinearMap) := by
    apply LinearMap.ext
    intro z
    apply (endomorphismCoordinates p).injective
    simp [endomorphismCoordinates, canonicalVectorMap, LinearMap.comp_apply]
  have hb : Function.Bijective
      (AlgHom.mulLeftRight k (PresentedQuaternion p)).toLinearMap := by
    rw [heq]
    exact (endomorphismCoordinates p).symm.bijective.comp
      (hcoord.comp (quaternionTensorBasis p).equivFun.bijective)
  exact hb

/-- The canonical left-right action of a nondegenerate uniform quaternion
algebra is bijective. -/
theorem mulLeftRight_bijective_of_nondegenerate
    (p : QuaternionParameters k)
    (hc : p.c₃ ≠ 0) (hdisc : 4 * p.c₁ + p.c₂ ^ 2 ≠ 0) :
    Function.Bijective (AlgHom.mulLeftRight k (PresentedQuaternion p)) :=
  mulLeftRight_bijective_of_coordinate_bijective p
    (canonicalVectorMap_bijective p hc hdisc)

/-- A nondegenerate uniform quaternion algebra is Azumaya over its base
field. This supplies centrality and, via `AzumayaFieldSimple`, simplicity. -/
theorem isAzumaya_of_nondegenerate
    (p : QuaternionParameters k)
    (hc : p.c₃ ≠ 0) (hdisc : 4 * p.c₁ + p.c₂ ^ 2 ≠ 0) :
    IsAzumaya k (PresentedQuaternion p) :=
  IsAzumaya.mk (mulLeftRight_bijective_of_nondegenerate p hc hdisc)

end QuaternionAzumaya
end RiemannResearch.E7.QuaternionHermitian
