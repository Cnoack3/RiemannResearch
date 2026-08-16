/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.FpqcCocycleTorsorDescentData
import RiemannResearch.AlgebraicGeometry.FpqcH1CanonicalScalarExtension
import RiemannResearch.AlgebraicGeometry.FpqcTorsor
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Regular-module transitions from an fpqc Čech cocycle

This module realizes the generalized-point translations from
`FpqcCocycleTorsorDescentData` as actual equivariant automorphisms of the
regular internal module for the group pulled back to a test scheme.

For a represented group `G` over `X`, a point `a : T ⟶ G` is transported
through the pullback adjunction to a global point of `T.hom ^* G`. Right
translation by that point is an automorphism of the regular module. The
identity, inverse, and composition laws are proved in `CategoryTheory.Mod`,
with composition ordered by `γᵢⱼ * γⱼₖ = γᵢₖ`.

This is the last objectwise step before effective descent. It does not supply
a torsor-valued pseudofunctor, an fpqc `IsStack` instance, a descended global
scheme, or an `FpqcH1TorsorClassifier`.
-/

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.ModObj

universe u v w

namespace CategoryTheory.ModObj

noncomputable section

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory.{v} D]

/-- The regular action of an internal group is simply transitive. -/
theorem regularLeftSMulIsIso
    (K : D) [GrpObj K] :
    let _ : ModObj K K := ModObj.regular K
    IsIso (ModObj.leftSMul K K) := by
  let _ : ModObj K K := ModObj.regular K
  rw [ModObj.isIso_leftSMul_iff]
  intro Z x y
  refine ⟨y * x⁻¹, ?_, ?_⟩
  · change (y * x⁻¹) * x = y
    exact inv_mul_cancel_right y x
  · intro m hm
    change m * x = y at hm
    calc
      m = (m * x) * x⁻¹ := (mul_inv_cancel_right m x).symm
      _ = y * x⁻¹ := congrArg (fun q => q * x⁻¹) hm

/-- The orbit map for the unit point of a regular module is the identity. -/
theorem regularOrbitMap_one
    (K : D) [GrpObj K] :
    let _ : ModObj K K := ModObj.regular K
    ModObj.orbitMap (G := K) (1 : 𝟙_ D ⟶ K) = 𝟙 K := by
  let _ : ModObj K K := ModObj.regular K
  apply (yoneda (C := D)).map_injective
  ext Z z
  let z' : Z.unop ⟶ K := z
  change z' ≫ ModObj.orbitMap (G := K) (1 : 𝟙_ D ⟶ K) = z' ≫ 𝟙 K
  rw [ModObj.comp_orbitMap (G := K)]
  change z' * (toUnit Z.unop ≫ (1 : 𝟙_ D ⟶ K)) = z' ≫ 𝟙 K
  simp

/-- Orbit maps for regular modules compose in multiplication order. -/
theorem regularOrbitMap_comp
    (K : D) [GrpObj K] (p q : 𝟙_ D ⟶ K) :
    let _ : ModObj K K := ModObj.regular K
    ModObj.orbitMap (G := K) p ≫ ModObj.orbitMap (G := K) q =
      ModObj.orbitMap (G := K) (p * q) := by
  let _ : ModObj K K := ModObj.regular K
  apply (yoneda (C := D)).map_injective
  ext Z z
  let z' : Z.unop ⟶ K := z
  change z' ≫
      (ModObj.orbitMap (G := K) p ≫ ModObj.orbitMap (G := K) q) =
    z' ≫ ModObj.orbitMap (G := K) (p * q)
  rw [← Category.assoc]
  rw [ModObj.comp_orbitMap (G := K) p z']
  rw [ModObj.comp_orbitMap (G := K) q]
  rw [ModObj.comp_orbitMap (G := K) (p * q) z']
  change (z' * (toUnit Z.unop ≫ p)) * (toUnit Z.unop ≫ q) =
    z' * (toUnit Z.unop ≫ (p * q))
  rw [mul_assoc]
  congr 1
  simp only [Hom.mul_def]
  exact (comp_lift_assoc (toUnit Z.unop) p q μ[K]).symm

/-- Equivariant right translation of the regular module by a global point. -/
noncomputable def regularTranslation
    (K : D) [GrpObj K] (p : 𝟙_ D ⟶ K) :
    Mod.regular K ≅ Mod.regular K := by
  let _ : ModObj K K := ModObj.regular K
  exact ModObj.orbitModIso
    (G := K) (P := K) (regularLeftSMulIsIso K) p

/-- Translation by the unit point is the identity module isomorphism. -/
@[simp] theorem regularTranslation_one
    (K : D) [GrpObj K] :
    regularTranslation K (1 : 𝟙_ D ⟶ K) =
      Iso.refl (Mod.regular K) := by
  apply Iso.ext
  apply Mod.hom_ext
  let _ : ModObj K K := ModObj.regular K
  change ModObj.orbitMap (G := K) (1 : 𝟙_ D ⟶ K) = 𝟙 K
  exact regularOrbitMap_one K

/-- Successive regular translations multiply their translating points. -/
@[simp] theorem regularTranslation_trans
    (K : D) [GrpObj K] (p q : 𝟙_ D ⟶ K) :
    (regularTranslation K p).trans (regularTranslation K q) =
      regularTranslation K (p * q) := by
  apply Iso.ext
  apply Mod.hom_ext
  let _ : ModObj K K := ModObj.regular K
  change ModObj.orbitMap (G := K) p ≫ ModObj.orbitMap (G := K) q =
    ModObj.orbitMap (G := K) (p * q)
  exact regularOrbitMap_comp K p q

/-- The inverse of a regular translation translates by the inverse point. -/
@[simp] theorem regularTranslation_symm
    (K : D) [GrpObj K] (p : 𝟙_ D ⟶ K) :
    (regularTranslation K p).symm = regularTranslation K p⁻¹ := by
  apply Iso.ext
  rw [← cancel_epi (regularTranslation K p).hom]
  change
    (regularTranslation K p).hom ≫ (regularTranslation K p).inv =
      (regularTranslation K p).hom ≫
        (regularTranslation K p⁻¹).hom
  rw [(regularTranslation K p).hom_inv_id]
  rw [← Iso.trans_hom]
  rw [regularTranslation_trans, mul_inv_cancel, regularTranslation_one]
  rfl

end

end CategoryTheory.ModObj

namespace RiemannResearch.AlgebraicGeometry

open CategoryTheory.Limits CategoryTheory.Over Opposite

noncomputable section

/-- The canonical comparison from the mapped terminal object to `T`. -/
def overMapUnitIsoTo
    {X : _root_.AlgebraicGeometry.Scheme} (T : Over X) :
    (Over.map T.hom).obj (𝟙_ (Over T.left)) ≅ T :=
  Over.isoMk (Iso.refl _) (by simp)

/-- Transport a represented point to a global point of the pulled-back
group over its source scheme. -/
def pullbackGrpPoint
    {X : _root_.AlgebraicGeometry.Scheme} (G : Grp (Over X))
    (T : Over X) (a : T ⟶ G.X) :
    𝟙_ (Over T.left) ⟶ ((Over.pullback T.hom).mapGrp.obj G).X :=
  (overMapYonedaGrpIso T.hom G).hom.app
    (op (𝟙_ (Over T.left))) ((overMapUnitIsoTo T).hom ≫ a)

/-- Transport of represented points preserves multiplication. -/
theorem pullbackGrpPoint_mul
    {X : _root_.AlgebraicGeometry.Scheme} (G : Grp (Over X))
    (T : Over X) (a b : T ⟶ G.X) :
    pullbackGrpPoint G T (a * b) =
      pullbackGrpPoint G T a * pullbackGrpPoint G T b := by
  have hcomp :
      (overMapUnitIsoTo T).hom ≫ (a * b) =
        ((overMapUnitIsoTo T).hom ≫ a) *
          ((overMapUnitIsoTo T).hom ≫ b) := by
    rw [Hom.mul_def, Hom.mul_def]
    exact comp_lift_assoc (overMapUnitIsoTo T).hom a b μ[G.X]
  unfold pullbackGrpPoint
  rw [hcomp]
  exact map_mul _ _ _

/-- Transport of represented points preserves the unit. -/
theorem pullbackGrpPoint_one
    {X : _root_.AlgebraicGeometry.Scheme} (G : Grp (Over X))
    (T : Over X) :
    pullbackGrpPoint G T 1 = 1 := by
  have hcomp :
      (overMapUnitIsoTo T).hom ≫ (1 : T ⟶ G.X) =
        (1 : (Over.map T.hom).obj (𝟙_ (Over T.left)) ⟶ G.X) := by
    rw [Hom.one_def, Hom.one_def, ← Category.assoc, comp_toUnit]
  unfold pullbackGrpPoint
  rw [hcomp]
  exact map_one _

/-- Transport of represented points preserves inverses. -/
theorem pullbackGrpPoint_inv
    {X : _root_.AlgebraicGeometry.Scheme} (G : Grp (Over X))
    (T : Over X) (a : T ⟶ G.X) :
    pullbackGrpPoint G T a⁻¹ = (pullbackGrpPoint G T a)⁻¹ := by
  have hcomp :
      (overMapUnitIsoTo T).hom ≫ a⁻¹ =
        ((overMapUnitIsoTo T).hom ≫ a)⁻¹ := by
    simp only [Hom.inv_def, Category.assoc]
  unfold pullbackGrpPoint
  rw [hcomp]
  exact map_inv _ _

/-- The group object pulled back to the source of a test scheme. -/
abbrev pullbackGrp
    {X : _root_.AlgebraicGeometry.Scheme} (G : Grp (Over X))
    (T : Over X) : Grp (Over T.left) :=
  (Over.pullback T.hom).mapGrp.obj G

/-- The regular module for the group pulled back to a test scheme. -/
abbrev pullbackRegularMod
    {X : _root_.AlgebraicGeometry.Scheme} (G : Grp (Over X))
    (T : Over X) :
    let _ : GrpObj (pullbackGrp G T).X := (pullbackGrp G T).grp
    Mod (Over T.left) (pullbackGrp G T).X :=
  let _ : GrpObj (pullbackGrp G T).X := (pullbackGrp G T).grp
  Mod.regular (pullbackGrp G T).X

end

end RiemannResearch.AlgebraicGeometry

namespace CategoryTheory.PresheafOfGroups

open RiemannResearch.AlgebraicGeometry

noncomputable section

variable {X : _root_.AlgebraicGeometry.Scheme.{u}}
variable (G : Grp (Over X))
variable {I : Type w} (U : I → Over X)

/-- The actual regular-module transition on a generalized overlap. -/
def OneCocycle.regularModTransition
    (cocycle : OneCocycle (yonedaGrp.obj G) U)
    (i j : I) {T : Over X} (a : T ⟶ U i) (b : T ⟶ U j) :
    pullbackRegularMod G T ≅ pullbackRegularMod G T := by
  let _ : GrpObj (pullbackGrp G T).X := (pullbackGrp G T).grp
  exact ModObj.regularTranslation (pullbackGrp G T).X
    (pullbackGrpPoint G T
      (show T ⟶ G.X from cocycle.ev i j a b))

/-- The actual regular-module transition is the identity on the diagonal. -/
@[simp] theorem OneCocycle.regularModTransition_refl
    (cocycle : OneCocycle (yonedaGrp.obj G) U)
    (i : I) {T : Over X} (a : T ⟶ U i) :
    cocycle.regularModTransition G U i i a a =
      Iso.refl (pullbackRegularMod G T) := by
  have hev : (show T ⟶ G.X from cocycle.ev i i a a) = 1 :=
    OneCocycle.ev_refl (yonedaGrp.obj G) U cocycle i a
  have hp :
      pullbackGrpPoint G T
          (show T ⟶ G.X from cocycle.ev i i a a) = 1 := by
    rw [hev]
    exact pullbackGrpPoint_one G T
  unfold OneCocycle.regularModTransition
  rw [hp, ModObj.regularTranslation_one]

/-- Reversing an overlap inverts the actual module transition. -/
theorem OneCocycle.regularModTransition_symm
    (cocycle : OneCocycle (yonedaGrp.obj G) U)
    (i j : I) {T : Over X} (a : T ⟶ U i) (b : T ⟶ U j) :
    (cocycle.regularModTransition G U i j a b).symm =
      cocycle.regularModTransition G U j i b a := by
  have hev :
      (show T ⟶ G.X from cocycle.ev j i b a) =
        (show T ⟶ G.X from cocycle.ev i j a b)⁻¹ :=
    OneCocycle.ev_symm (yonedaGrp.obj G) U cocycle j i b a
  have hp :
      (pullbackGrpPoint G T
        (show T ⟶ G.X from cocycle.ev i j a b))⁻¹ =
      pullbackGrpPoint G T
        (show T ⟶ G.X from cocycle.ev j i b a) := by
    rw [hev, pullbackGrpPoint_inv]
  unfold OneCocycle.regularModTransition
  rw [ModObj.regularTranslation_symm, hp]

/-- Actual regular-module transitions compose in cocycle order. -/
theorem OneCocycle.regularModTransition_trans
    (cocycle : OneCocycle (yonedaGrp.obj G) U)
    (i j k : I) {T : Over X}
    (a : T ⟶ U i) (b : T ⟶ U j) (c : T ⟶ U k) :
    (cocycle.regularModTransition G U i j a b).trans
        (cocycle.regularModTransition G U j k b c) =
      cocycle.regularModTransition G U i k a c := by
  have hev :
      (show T ⟶ G.X from cocycle.ev i j a b) *
          (show T ⟶ G.X from cocycle.ev j k b c) =
        (show T ⟶ G.X from cocycle.ev i k a c) :=
    cocycle.ev_trans i j k a b c
  have hp :
      pullbackGrpPoint G T
          (show T ⟶ G.X from cocycle.ev i j a b) *
        pullbackGrpPoint G T
          (show T ⟶ G.X from cocycle.ev j k b c) =
      pullbackGrpPoint G T
        (show T ⟶ G.X from cocycle.ev i k a c) := by
    rw [← pullbackGrpPoint_mul, hev]
  unfold OneCocycle.regularModTransition
  rw [ModObj.regularTranslation_trans, hp]

end

end CategoryTheory.PresheafOfGroups
namespace RiemannResearch.AlgebraicGeometry

open CategoryTheory

noncomputable section

/-- An affine-group Čech cocycle gives an actual regular-module transition
for every generalized overlap. This remains objectwise over the test scheme. -/
noncomputable def affineGroupCocycleRegularModTransition
    (R A : Type u) [CommRing R] [CommRing A] [HopfAlgebra R A]
    {I : Type w} (U : FpqcCover (CommRingCat.of R) I)
    (cocycle : PresheafOfGroups.OneCocycle
      (affineGroupPresheaf (CommRingCat.of R) (CommRingCat.of A)) U.obj)
    (T : Over (_root_.AlgebraicGeometry.Spec (CommRingCat.of R)))
    (i j : I) (a : T ⟶ U.obj i) (b : T ⟶ U.obj j) :
    pullbackRegularMod (affineGroupSchemeGroup R A) T ≅
      pullbackRegularMod (affineGroupSchemeGroup R A) T :=
  cocycle.regularModTransition
    (affineGroupSchemeGroup R A) U.obj i j a b

end

end RiemannResearch.AlgebraicGeometry

namespace RiemannResearch.AlgebraicGeometry

open CategoryTheory

noncomputable section
/-- Affine-group regular-module transitions are trivial on the diagonal. -/
@[simp] theorem affineGroupCocycleRegularModTransition_refl
    (R A : Type u) [CommRing R] [CommRing A] [HopfAlgebra R A]
    {I : Type w} (U : FpqcCover (CommRingCat.of R) I)
    (cocycle : PresheafOfGroups.OneCocycle
      (affineGroupPresheaf (CommRingCat.of R) (CommRingCat.of A)) U.obj)
    (T : Over (_root_.AlgebraicGeometry.Spec (CommRingCat.of R)))
    (i : I) (a : T ⟶ U.obj i) :
    affineGroupCocycleRegularModTransition R A U cocycle T i i a a =
      Iso.refl _ :=
  cocycle.regularModTransition_refl
    (affineGroupSchemeGroup R A) U.obj i a

/-- Swapping affine-group overlap legs inverts the module transition. -/
theorem affineGroupCocycleRegularModTransition_symm
    (R A : Type u) [CommRing R] [CommRing A] [HopfAlgebra R A]
    {I : Type w} (U : FpqcCover (CommRingCat.of R) I)
    (cocycle : PresheafOfGroups.OneCocycle
      (affineGroupPresheaf (CommRingCat.of R) (CommRingCat.of A)) U.obj)
    (T : Over (_root_.AlgebraicGeometry.Spec (CommRingCat.of R)))
    (i j : I) (a : T ⟶ U.obj i) (b : T ⟶ U.obj j) :
    (affineGroupCocycleRegularModTransition
      R A U cocycle T i j a b).symm =
      affineGroupCocycleRegularModTransition
        R A U cocycle T j i b a :=
  cocycle.regularModTransition_symm
    (affineGroupSchemeGroup R A) U.obj i j a b

/-- Affine-group module transitions compose on triple overlaps. -/
theorem affineGroupCocycleRegularModTransition_trans
    (R A : Type u) [CommRing R] [CommRing A] [HopfAlgebra R A]
    {I : Type w} (U : FpqcCover (CommRingCat.of R) I)
    (cocycle : PresheafOfGroups.OneCocycle
      (affineGroupPresheaf (CommRingCat.of R) (CommRingCat.of A)) U.obj)
    (T : Over (_root_.AlgebraicGeometry.Spec (CommRingCat.of R)))
    (i j k : I)
    (a : T ⟶ U.obj i) (b : T ⟶ U.obj j) (c : T ⟶ U.obj k) :
    (affineGroupCocycleRegularModTransition
      R A U cocycle T i j a b).trans
        (affineGroupCocycleRegularModTransition
          R A U cocycle T j k b c) =
      affineGroupCocycleRegularModTransition
        R A U cocycle T i k a c :=
  cocycle.regularModTransition_trans
    (affineGroupSchemeGroup R A) U.obj i j k a b c

end

end RiemannResearch.AlgebraicGeometry
