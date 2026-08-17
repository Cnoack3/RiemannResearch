/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import RiemannResearch.GaloisCohomology.ContinuousNonabelianH1

/-!
# Pointed Galois cohomology of an algebraic group

For a field `K` and a Hopf algebra `A` presenting an algebraic group `G`, this
module constructs the canonical action of `Gal(K̄/K)` on `G(K̄)` and defines
`GaloisH1 K A` as continuous nonabelian first cohomology. The coefficient
group carries the discrete topology, as in the usual definition of Galois
cohomology of an algebraic group.

Source for the mathematical construction and terminology: J.-P. Serre,
*Galois Cohomology*, Chapter I, §5.
-/

namespace RiemannResearch.AlgebraicGeometry

open CategoryTheory
open scoped CategoryTheory.MonObj

universe u

noncomputable section

/-- The group-valued functor represented by the Hopf algebra `A`. -/
abbrev algebraicGroupPresheaf
    (K A : Type u) [Field K] [CommRing A] [HopfAlgebra K A] :
    (Over (_root_.AlgebraicGeometry.Spec (CommRingCat.of K)))ᵒᵖ ⥤ GrpCat :=
  yonedaGrpObj
    ((_root_.AlgebraicGeometry.Spec (CommRingCat.of A)).asOver
      (_root_.AlgebraicGeometry.Spec (CommRingCat.of K)))

/-- `Spec K̄` as an object over `Spec K`. -/
def geometricPointObject
    (K : Type u) [Field K] :
    Over (_root_.AlgebraicGeometry.Spec (CommRingCat.of K)) :=
  Over.mk
    (_root_.AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))

/-- The endomorphism of `Spec K̄` over `Spec K` induced by an element of the
absolute Galois group. -/
def absoluteGaloisPointEndomorphism
    (K : Type u) [Field K]
    (σ : Field.absoluteGaloisGroup K) :
    geometricPointObject K ⟶ geometricPointObject K := by
  change (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) at σ
  refine Over.homMk
    (_root_.AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom σ.toAlgHom.toRingHom)) ?_
  change
    _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫
      _root_.AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) =
      _root_.AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  rw [← _root_.AlgebraicGeometry.Spec.map_comp]
  congr 1
  ext x
  exact σ.commutes x

/-- The geometric point group `G(K̄)`. -/
abbrev AlgebraicGroupGeometricPoints
    (K A : Type u) [Field K] [CommRing A] [HopfAlgebra K A] : Type u :=
  ((algebraicGroupPresheaf K A).obj
    (Opposite.op (geometricPointObject K)))

variable (K A : Type u) [Field K] [CommRing A] [HopfAlgebra K A]

theorem absoluteGaloisPointEndomorphism_one :
    absoluteGaloisPointEndomorphism K
      (1 : Field.absoluteGaloisGroup K) = 𝟙 _ := by
  ext
  change
    _root_.AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom
          ((1 : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K).toAlgHom.toRingHom)) =
      𝟙 _
  rw [← _root_.AlgebraicGeometry.Spec.map_id]
  congr 1

theorem absoluteGaloisPointEndomorphism_mul
    (σ τ : Field.absoluteGaloisGroup K) :
    absoluteGaloisPointEndomorphism K (σ * τ) =
      absoluteGaloisPointEndomorphism K σ ≫
        absoluteGaloisPointEndomorphism K τ := by
  change (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) at σ τ
  ext
  change
    _root_.AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom ((σ * τ).toAlgHom.toRingHom)) =
      _root_.AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫
        _root_.AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom τ.toAlgHom.toRingHom)
  rw [← _root_.AlgebraicGeometry.Spec.map_comp]
  congr 1

/-- The natural absolute-Galois action on `G(K̄)`. -/
def absoluteGaloisSmul
    (σ : Field.absoluteGaloisGroup K)
    (x : AlgebraicGroupGeometricPoints K A) :
    AlgebraicGroupGeometricPoints K A :=
  ((algebraicGroupPresheaf K A).map
    (absoluteGaloisPointEndomorphism K σ).op).hom x

instance : SMul (Field.absoluteGaloisGroup K)
    (AlgebraicGroupGeometricPoints K A) :=
  ⟨absoluteGaloisSmul K A⟩

instance : MulDistribMulAction (Field.absoluteGaloisGroup K)
    (AlgebraicGroupGeometricPoints K A) where
  one_smul x := by
    change absoluteGaloisSmul K A 1 x = x
    unfold absoluteGaloisSmul
    rw [absoluteGaloisPointEndomorphism_one]
    change
      ((algebraicGroupPresheaf K A).map
        (𝟙 (Opposite.op (geometricPointObject K)))).hom x = x
    rw [(algebraicGroupPresheaf K A).map_id]
    rfl
  mul_smul σ τ x := by
    change absoluteGaloisSmul K A (σ * τ) x =
      absoluteGaloisSmul K A σ (absoluteGaloisSmul K A τ x)
    unfold absoluteGaloisSmul
    rw [absoluteGaloisPointEndomorphism_mul]
    rw [CategoryTheory.op_comp]
    rw [(algebraicGroupPresheaf K A).map_comp]
    rw [GrpCat.comp_apply]
  smul_one σ := by
    change
      ((algebraicGroupPresheaf K A).map
        (absoluteGaloisPointEndomorphism K σ).op).hom 1 = 1
    exact map_one _
  smul_mul σ x y := by
    change
      ((algebraicGroupPresheaf K A).map
        (absoluteGaloisPointEndomorphism K σ).op).hom (x * y) =
      ((algebraicGroupPresheaf K A).map
        (absoluteGaloisPointEndomorphism K σ).op).hom x *
      ((algebraicGroupPresheaf K A).map
        (absoluteGaloisPointEndomorphism K σ).op).hom y
    exact map_mul _ _ _

/-- Algebraic-group points over `K̄` carry the discrete coefficient topology
used in continuous Galois cohomology. -/
instance : TopologicalSpace (AlgebraicGroupGeometricPoints K A) :=
  ⊥

/-- Pointed continuous Galois cohomology `H¹(K,G)`. -/
abbrev GaloisH1 : Type u :=
  RiemannResearch.GaloisCohomology.ContinuousNonabelianH1
    (Field.absoluteGaloisGroup K) (AlgebraicGroupGeometricPoints K A)

namespace GaloisH1

/-- The class of the trivial continuous cocycle. -/
def neutral : GaloisH1 K A :=
  RiemannResearch.GaloisCohomology.ContinuousNonabelianH1.neutral

end GaloisH1

end

end RiemannResearch.AlgebraicGeometry
