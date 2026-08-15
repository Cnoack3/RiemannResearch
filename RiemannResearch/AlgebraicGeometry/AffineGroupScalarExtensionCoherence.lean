/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.AlgebraicGeometry.FpqcH1CanonicalScalarExtension
import RiemannResearch.AlgebraicGeometry.OverMapPullbackCoherence

/-!
# Affine-group scalar-extension coherence

This module identifies the tensor-unit and tensor-associativity comparisons
for affine group schemes with the corresponding pullback coherence maps.
-/

namespace RiemannResearch.AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits CategoryTheory.Over
open scoped TensorProduct

universe u v w

noncomputable section

@[simp] theorem scalarExtensionSpecMap_self
    (R : Type u) [CommRing R] :
    scalarExtensionSpecMap R R =
      𝟙 (_root_.AlgebraicGeometry.Spec (CommRingCat.of R)) := by
  simp [scalarExtensionSpecMap]

@[simp] theorem scalarExtensionSpecMap_comp
    (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] :
    scalarExtensionSpecMap S T ≫ scalarExtensionSpecMap R S =
      scalarExtensionSpecMap R T := by
  simp [scalarExtensionSpecMap, IsScalarTower.algebraMap_eq R S T]

/-- The affine tensor-unit comparison is the first projection from the
corresponding scheme pullback. -/
theorem pullbackSpecIso_scalarExtensionSelf_hom
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    (pullbackSymmetry
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of A) ↘
          _root_.AlgebraicGeometry.Spec (CommRingCat.of R))
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of R) ↘
          _root_.AlgebraicGeometry.Spec (CommRingCat.of R)) ≪≫
      _root_.AlgebraicGeometry.pullbackSpecIso' R R A).hom ≫
        _root_.AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight.toRingHom :
              A →+* TensorProduct R R A)) =
      pullback.fst
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of A) ↘
          _root_.AlgebraicGeometry.Spec (CommRingCat.of R))
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of R) ↘
          _root_.AlgebraicGeometry.Spec (CommRingCat.of R)) := by
  have hs :
      (_root_.AlgebraicGeometry.pullbackSpecIso' R R A).hom ≫
        _root_.AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight.toRingHom :
              A →+* TensorProduct R R A)) =
      pullback.snd
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of R) ↘
          _root_.AlgebraicGeometry.Spec (CommRingCat.of R))
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of A) ↘
          _root_.AlgebraicGeometry.Spec (CommRingCat.of R)) :=
    _root_.AlgebraicGeometry.pullbackSpecIso_hom_snd R R A
  rw [Iso.trans_hom, Category.assoc, hs,
    pullbackSymmetry_hom_comp_snd]

/-! ## Tensor-coordinate coherence -/

/-- A bialgebra equivalence as an isomorphism in commutative Hopf algebras. -/
def commHopfAlgIsoOfBialgEquiv
    {R A B : Type u}
    [CommRing R] [CommRing A] [CommRing B]
    [HopfAlgebra R A] [HopfAlgebra R B]
    (e : A ≃ₐc[R] B) :
    CommHopfAlgCat.of R A ≅ CommHopfAlgCat.of R B where
  hom := CommHopfAlgCat.ofHom e.toBialgHom
  inv := CommHopfAlgCat.ofHom e.symm.toBialgHom
  hom_inv_id := by
    ext x
    exact e.symm_apply_apply x
  inv_hom_id := by
    ext x
    exact e.apply_symm_apply x

/-- Tensor-unit comparison as an isomorphism of affine group schemes. -/
def affineGroupScalarExtensionSelfGroupIso
    (R A : Type u)
    [CommRing R] [CommRing A] [HopfAlgebra R A] :
    affineGroupScalarExtensionGroup R R A ≅
      affineGroupSchemeGroup R A :=
  ((_root_.AlgebraicGeometry.hopfSpec (CommRingCat.of R)).mapIso
    (commHopfAlgIsoOfBialgEquiv
      (Bialgebra.TensorProduct.lid R A)).op).symm

/-- The affine tensor-unit comparison agrees with the canonical identity
pullback isomorphism. -/
theorem affineGroupScalarExtensionSelfGroupIso_hom
    (R A : Type u)
    [CommRing R] [CommRing A] [HopfAlgebra R A] :
    (affineGroupBaseChangeGroupIso R R A ≪≫
        affineGroupScalarExtensionSelfGroupIso R A).hom.hom.hom =
      (overPullbackIdIsoOfEq (scalarExtensionSpecMap R R)
        (scalarExtensionSpecMap_self R)).hom.app
          (affineGroupSchemeGroup R A).X := by
  ext
  rw [show
    ((affineGroupBaseChangeGroupIso R R A ≪≫
      affineGroupScalarExtensionSelfGroupIso R A).hom.hom.hom).left =
        (pullbackSymmetry
          (_root_.AlgebraicGeometry.Spec (CommRingCat.of A) ↘
            _root_.AlgebraicGeometry.Spec (CommRingCat.of R))
          (_root_.AlgebraicGeometry.Spec (CommRingCat.of R) ↘
            _root_.AlgebraicGeometry.Spec (CommRingCat.of R)) ≪≫
         _root_.AlgebraicGeometry.pullbackSpecIso' R R A).hom ≫
        _root_.AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight.toRingHom :
              A →+* TensorProduct R R A)) from rfl]
  rw [overPullbackIdIsoOfEq_hom_app_left]
  exact pullbackSpecIso_scalarExtensionSelf_hom R A

/-- Associativity of scalar extension as a bialgebra equivalence. -/
def affineGroupScalarExtensionCompBialgEquiv
    (R S T A : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [HopfAlgebra R A] :
    TensorProduct S T (TensorProduct R S A) ≃ₐc[T]
      TensorProduct R T A := by
  apply BialgEquiv.ofAlgEquiv
    (Algebra.TensorProduct.cancelBaseChange R S T T A)
  · ext x
    simp [Bialgebra.TensorProduct.counitAlgHom_def]
    rw [TensorProduct.smul_tmul']
    rw [Algebra.TensorProduct.rid_tmul]
    simp
  · ext x
    simp [Bialgebra.TensorProduct.comulAlgHom_def]
    generalize hz :
      CoalgebraStruct.comul (R := R) (A := A) x = z
    clear hz
    induction z using TensorProduct.induction_on with
    | zero =>
        simp only [TensorProduct.tmul_zero, map_zero]
    | tmul a b =>
        simp only [
          Algebra.TensorProduct.tensorTensorTensorComm_tmul,
          Algebra.TensorProduct.map_tmul]
        have ha :
            ((Algebra.TensorProduct.cancelBaseChange R S T T A :
              TensorProduct S T (TensorProduct R S A) →ₐ[T]
                TensorProduct R T A)
              (1 ⊗ₜ[S] (1 ⊗ₜ[R] a))) =
                (1 ⊗ₜ[R] a) := by
          change
            (Algebra.TensorProduct.cancelBaseChange R S T T A)
              (1 ⊗ₜ[S] (1 ⊗ₜ[R] a)) = (1 ⊗ₜ[R] a)
          simpa only [one_smul] using
            (Algebra.TensorProduct.cancelBaseChange_tmul
              R S T T A (1 : T) (1 : S) a)
        have hb :
            ((Algebra.TensorProduct.cancelBaseChange R S T T A :
              TensorProduct S T (TensorProduct R S A) →ₐ[T]
                TensorProduct R T A)
              (1 ⊗ₜ[S] (1 ⊗ₜ[R] b))) =
                (1 ⊗ₜ[R] b) := by
          change
            (Algebra.TensorProduct.cancelBaseChange R S T T A)
              (1 ⊗ₜ[S] (1 ⊗ₜ[R] b)) = (1 ⊗ₜ[R] b)
          simpa only [one_smul] using
            (Algebra.TensorProduct.cancelBaseChange_tmul
              R S T T A (1 : T) (1 : S) b)
        rw [ha, hb]
    | add x y hx hy =>
        simp only [TensorProduct.tmul_add, map_add, hx, hy]

/-- The affine base-change comparison sends the first pullback projection
to the tensor-product inclusion of the original Hopf algebra. -/
@[reassoc] theorem affineGroupBaseChangeOverIso_inv_fst
    (R S A : Type u) [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [HopfAlgebra R A] :
    (affineGroupBaseChangeOverIso R S A).inv.left ≫
      pullback.fst
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of A) ↘
          _root_.AlgebraicGeometry.Spec (CommRingCat.of R))
        (scalarExtensionSpecMap R S) =
    _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight :
        A →ₐ[R] TensorProduct R S A).toRingHom) := by
  change ((_root_.AlgebraicGeometry.pullbackSpecIso' R S A).inv ≫
      (pullbackSymmetry
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of A) ↘
          _root_.AlgebraicGeometry.Spec (CommRingCat.of R))
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of S) ↘
          _root_.AlgebraicGeometry.Spec (CommRingCat.of R))).inv) ≫
    pullback.fst
      (_root_.AlgebraicGeometry.Spec (CommRingCat.of A) ↘
        _root_.AlgebraicGeometry.Spec (CommRingCat.of R))
      (_root_.AlgebraicGeometry.Spec (CommRingCat.of S) ↘
        _root_.AlgebraicGeometry.Spec (CommRingCat.of R)) = _
  rw [Category.assoc, pullbackSymmetry_inv_comp_fst]
  change (_root_.AlgebraicGeometry.pullbackSpecIso R S A).inv ≫
      pullback.snd
        (_root_.AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap R S)))
        (_root_.AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap R A))) = _
  rw [_root_.AlgebraicGeometry.pullbackSpecIso_inv_snd]
  apply congrArg _root_.AlgebraicGeometry.Spec.map
  ext x
  rfl

/-- The affine base-change comparison sends the second pullback projection
to the tensor-product inclusion of the new base ring. -/
@[reassoc] theorem affineGroupBaseChangeOverIso_inv_snd
    (R S A : Type u) [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [HopfAlgebra R A] :
    (affineGroupBaseChangeOverIso R S A).inv.left ≫
      pullback.snd
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of A) ↘
          _root_.AlgebraicGeometry.Spec (CommRingCat.of R))
        (scalarExtensionSpecMap R S) =
    _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom :
        S →+* TensorProduct R S A)) := by
  change ((_root_.AlgebraicGeometry.pullbackSpecIso' R S A).inv ≫
      (pullbackSymmetry
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of A) ↘
          _root_.AlgebraicGeometry.Spec (CommRingCat.of R))
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of S) ↘
          _root_.AlgebraicGeometry.Spec (CommRingCat.of R))).inv) ≫
    pullback.snd
      (_root_.AlgebraicGeometry.Spec (CommRingCat.of A) ↘
        _root_.AlgebraicGeometry.Spec (CommRingCat.of R))
      (_root_.AlgebraicGeometry.Spec (CommRingCat.of S) ↘
        _root_.AlgebraicGeometry.Spec (CommRingCat.of R)) = _
  rw [Category.assoc, pullbackSymmetry_inv_comp_snd]
  change (_root_.AlgebraicGeometry.pullbackSpecIso R S A).inv ≫
      pullback.fst
        (_root_.AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap R S)))
        (_root_.AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap R A))) = _
  rw [_root_.AlgebraicGeometry.pullbackSpecIso_inv_fst]

/-- Tensor associativity as an isomorphism of represented affine group
objects. -/
def affineGroupScalarExtensionCompGroupIso
    (R S T A : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [HopfAlgebra R A] :
    affineGroupScalarExtensionGroup S T (TensorProduct R S A) ≅
      affineGroupScalarExtensionGroup R T A :=
  (_root_.AlgebraicGeometry.hopfSpec (CommRingCat.of T)).mapIso
    (commHopfAlgIsoOfBialgEquiv
      (affineGroupScalarExtensionCompBialgEquiv R S T A)).symm.op

theorem cancelBaseChange_comp_includeRight_includeRight
    (R S T A : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra S T] [Algebra R T] [Algebra R A]
    [IsScalarTower R S T] :
    let c := Algebra.TensorProduct.cancelBaseChange R S T T A
    c.toAlgHom.toRingHom.comp
      ((Algebra.TensorProduct.includeRight :
          TensorProduct R S A →ₐ[S]
            TensorProduct S T (TensorProduct R S A)).toRingHom.comp
        (Algebra.TensorProduct.includeRight :
          A →ₐ[R] TensorProduct R S A).toRingHom) =
      (Algebra.TensorProduct.includeRight :
        A →ₐ[R] TensorProduct R T A).toRingHom := by
  dsimp
  ext a
  change (Algebra.TensorProduct.cancelBaseChange R S T T A)
      (1 ⊗ₜ[S] (1 ⊗ₜ[R] a)) = 1 ⊗ₜ[R] a
  simpa only [one_smul] using
    (Algebra.TensorProduct.cancelBaseChange_tmul
      R S T T A (1 : T) (1 : S) a)

theorem cancelBaseChange_comp_includeRight_includeLeft
    (R S T A : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra S T] [Algebra R T] [Algebra R A]
    [IsScalarTower R S T] :
    let c := Algebra.TensorProduct.cancelBaseChange R S T T A
    c.toAlgHom.toRingHom.comp
      ((Algebra.TensorProduct.includeRight :
          TensorProduct R S A →ₐ[S]
            TensorProduct S T (TensorProduct R S A)).toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom :
          S →+* TensorProduct R S A)) =
      (Algebra.TensorProduct.includeLeftRingHom :
        T →+* TensorProduct R T A).comp (algebraMap S T) := by
  dsimp
  ext s
  change (Algebra.TensorProduct.cancelBaseChange R S T T A)
      (1 ⊗ₜ[S] (s ⊗ₜ[R] 1)) =
    (algebraMap S T s) ⊗ₜ[R] 1
  simpa only [Algebra.smul_def, mul_one] using
    (Algebra.TensorProduct.cancelBaseChange_tmul
      R S T T A (1 : T) s (1 : A))

theorem cancelBaseChange_comp_includeLeft
    (R S T A : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra S T] [Algebra R T] [Algebra R A]
    [IsScalarTower R S T] :
    let c := Algebra.TensorProduct.cancelBaseChange R S T T A
    c.toAlgHom.toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom :
        T →+* TensorProduct S T (TensorProduct R S A)) =
      (Algebra.TensorProduct.includeLeftRingHom :
        T →+* TensorProduct R T A) := by
  dsimp
  ext t
  change (Algebra.TensorProduct.cancelBaseChange R S T T A)
      (t ⊗ₜ[S] 1) = t ⊗ₜ[R] 1
  rw [Algebra.TensorProduct.one_def]
  simpa only [one_smul] using
    (Algebra.TensorProduct.cancelBaseChange_tmul
      R S T T A t (1 : S) (1 : A))

set_option maxHeartbeats 800000 in
/-- Scheme-level form of associativity for affine scalar extension.
The expanded nested-pullback normalization requires the larger heartbeat
budget. -/
theorem affineGroupScalarExtensionCompOverIso
    (R S T A : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [HopfAlgebra R A] :
    (Over.pullback (scalarExtensionSpecMap S T)).mapIso
        (affineGroupBaseChangeOverIso R S A) ≪≫
      affineGroupBaseChangeOverIso S T (TensorProduct R S A) ≪≫
      (Grp.forget (Over (_root_.AlgebraicGeometry.Spec
        (CommRingCat.of T)))).mapIso
          (affineGroupScalarExtensionCompGroupIso R S T A) =
    (overPullbackCompIsoOfEq (scalarExtensionSpecMap S T)
        (scalarExtensionSpecMap R S) (scalarExtensionSpecMap R T)
        (scalarExtensionSpecMap_comp R S T)).symm.app
          ((_root_.AlgebraicGeometry.Spec
            (CommRingCat.of A)).asOver
              (_root_.AlgebraicGeometry.Spec (CommRingCat.of R))) ≪≫
      affineGroupBaseChangeOverIso R T A := by
  apply Iso.ext
  apply (Iso.inv_eq_inv _ _).mp
  ext
  let cSpec :
      ((_root_.AlgebraicGeometry.Spec
          (CommRingCat.of (TensorProduct R T A))).asOver
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of T))).left ⟶
      ((_root_.AlgebraicGeometry.Spec
          (CommRingCat.of
            (TensorProduct S T (TensorProduct R S A)))).asOver
        (_root_.AlgebraicGeometry.Spec (CommRingCat.of T))).left :=
    _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.cancelBaseChange R S T T A).toRingHom)
  change
    ((cSpec ≫
        (affineGroupBaseChangeOverIso S T (TensorProduct R S A)).inv.left) ≫
      ((Over.pullback (scalarExtensionSpecMap S T)).map
        (affineGroupBaseChangeOverIso R S A).inv).left) =
    (affineGroupBaseChangeOverIso R T A).inv.left ≫
      ((overPullbackCompIsoOfEq (scalarExtensionSpecMap S T)
        (scalarExtensionSpecMap R S) (scalarExtensionSpecMap R T)
        (scalarExtensionSpecMap_comp R S T)).hom.app
          ((_root_.AlgebraicGeometry.Spec
            (CommRingCat.of A)).asOver
              (_root_.AlgebraicGeometry.Spec
                (CommRingCat.of R)))).left
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · let innerRight :
          ((_root_.AlgebraicGeometry.Spec
              (CommRingCat.of (TensorProduct R S A))).asOver
            (_root_.AlgebraicGeometry.Spec (CommRingCat.of S))).left ⟶
          ((_root_.AlgebraicGeometry.Spec
              (CommRingCat.of A)).asOver
            (_root_.AlgebraicGeometry.Spec (CommRingCat.of R))).left :=
        _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight :
            A →ₐ[R] TensorProduct R S A).toRingHom)
      have hRSRight :
          (affineGroupBaseChangeOverIso R S A).inv.left ≫
            pullback.fst
              (_root_.AlgebraicGeometry.Spec (CommRingCat.of A) ↘
                _root_.AlgebraicGeometry.Spec (CommRingCat.of R))
              (scalarExtensionSpecMap R S) = innerRight := by
        change (affineGroupBaseChangeOverIso R S A).inv.left ≫
          pullback.fst _ _ = _root_.AlgebraicGeometry.Spec.map _
        exact affineGroupBaseChangeOverIso_inv_fst R S A
      let outerRight :
          ((_root_.AlgebraicGeometry.Spec
              (CommRingCat.of
                (TensorProduct S T (TensorProduct R S A)))).asOver
            (_root_.AlgebraicGeometry.Spec (CommRingCat.of T))).left ⟶
          ((_root_.AlgebraicGeometry.Spec
              (CommRingCat.of (TensorProduct R S A))).asOver
            (_root_.AlgebraicGeometry.Spec (CommRingCat.of S))).left :=
        _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight :
            TensorProduct R S A →ₐ[S]
              TensorProduct S T (TensorProduct R S A)).toRingHom)
      have hSTRight :
          (affineGroupBaseChangeOverIso S T
              (TensorProduct R S A)).inv.left ≫
            pullback.fst
              (_root_.AlgebraicGeometry.Spec
                  (CommRingCat.of (TensorProduct R S A)) ↘
                _root_.AlgebraicGeometry.Spec (CommRingCat.of S))
              (scalarExtensionSpecMap S T) = outerRight := by
        change (affineGroupBaseChangeOverIso S T
            (TensorProduct R S A)).inv.left ≫
          pullback.fst _ _ = _root_.AlgebraicGeometry.Spec.map _
        exact affineGroupBaseChangeOverIso_inv_fst
          S T (TensorProduct R S A)
      let directRight :
          ((_root_.AlgebraicGeometry.Spec
              (CommRingCat.of (TensorProduct R T A))).asOver
            (_root_.AlgebraicGeometry.Spec (CommRingCat.of T))).left ⟶
          ((_root_.AlgebraicGeometry.Spec
              (CommRingCat.of A)).asOver
            (_root_.AlgebraicGeometry.Spec (CommRingCat.of R))).left :=
        _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight :
            A →ₐ[R] TensorProduct R T A).toRingHom)
      have hRTRight :
          (affineGroupBaseChangeOverIso R T A).inv.left ≫
            pullback.fst
              (_root_.AlgebraicGeometry.Spec (CommRingCat.of A) ↘
                _root_.AlgebraicGeometry.Spec (CommRingCat.of R))
              (scalarExtensionSpecMap R T) = directRight := by
        change (affineGroupBaseChangeOverIso R T A).inv.left ≫
          pullback.fst _ _ = _root_.AlgebraicGeometry.Spec.map _
        exact affineGroupBaseChangeOverIso_inv_fst R T A
      slice_lhs 3 4 =>
        exact overPullback_map_fst (scalarExtensionSpecMap S T)
          (affineGroupBaseChangeOverIso R S A).inv
      slice_lhs 4 5 => exact hRSRight
      slice_lhs 2 3 => exact hSTRight
      slice_rhs 2 4 =>
        exact overPullbackCompIsoOfEq_hom_app_fst_fst
          (scalarExtensionSpecMap S T) (scalarExtensionSpecMap R S)
          (scalarExtensionSpecMap R T) (scalarExtensionSpecMap_comp R S T)
          ((_root_.AlgebraicGeometry.Spec
            (CommRingCat.of A)).asOver
              (_root_.AlgebraicGeometry.Spec (CommRingCat.of R)))
      slice_rhs 1 2 => exact hRTRight
      change
        _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.cancelBaseChange R S T T A).toRingHom) ≫
          _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight :
              TensorProduct R S A →ₐ[S]
                TensorProduct S T (TensorProduct R S A)).toRingHom) ≫
          _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight :
              A →ₐ[R] TensorProduct R S A).toRingHom) =
        _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight :
            A →ₐ[R] TensorProduct R T A).toRingHom)
      rw [← _root_.AlgebraicGeometry.Spec.map_comp,
        ← _root_.AlgebraicGeometry.Spec.map_comp]
      exact congrArg _root_.AlgebraicGeometry.Spec.map
        (congrArg CommRingCat.ofHom
          (cancelBaseChange_comp_includeRight_includeRight R S T A))
    · let innerLeft :
          ((_root_.AlgebraicGeometry.Spec
              (CommRingCat.of (TensorProduct R S A))).asOver
            (_root_.AlgebraicGeometry.Spec (CommRingCat.of S))).left ⟶
          _root_.AlgebraicGeometry.Spec (CommRingCat.of S) :=
        _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom :
            S →+* TensorProduct R S A))
      have hRSLeft :
          (affineGroupBaseChangeOverIso R S A).inv.left ≫
            pullback.snd
              (_root_.AlgebraicGeometry.Spec (CommRingCat.of A) ↘
                _root_.AlgebraicGeometry.Spec (CommRingCat.of R))
              (scalarExtensionSpecMap R S) = innerLeft := by
        change (affineGroupBaseChangeOverIso R S A).inv.left ≫
          pullback.snd _ _ = _root_.AlgebraicGeometry.Spec.map _
        exact affineGroupBaseChangeOverIso_inv_snd R S A
      let outerRight :
          ((_root_.AlgebraicGeometry.Spec
              (CommRingCat.of
                (TensorProduct S T (TensorProduct R S A)))).asOver
            (_root_.AlgebraicGeometry.Spec (CommRingCat.of T))).left ⟶
          ((_root_.AlgebraicGeometry.Spec
              (CommRingCat.of (TensorProduct R S A))).asOver
            (_root_.AlgebraicGeometry.Spec (CommRingCat.of S))).left :=
        _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight :
            TensorProduct R S A →ₐ[S]
              TensorProduct S T (TensorProduct R S A)).toRingHom)
      have hSTRight :
          (affineGroupBaseChangeOverIso S T
              (TensorProduct R S A)).inv.left ≫
            pullback.fst
              (_root_.AlgebraicGeometry.Spec
                  (CommRingCat.of (TensorProduct R S A)) ↘
                _root_.AlgebraicGeometry.Spec (CommRingCat.of S))
              (scalarExtensionSpecMap S T) = outerRight := by
        change (affineGroupBaseChangeOverIso S T
            (TensorProduct R S A)).inv.left ≫
          pullback.fst _ _ = _root_.AlgebraicGeometry.Spec.map _
        exact affineGroupBaseChangeOverIso_inv_fst
          S T (TensorProduct R S A)
      let directLeft :
          ((_root_.AlgebraicGeometry.Spec
              (CommRingCat.of (TensorProduct R T A))).asOver
            (_root_.AlgebraicGeometry.Spec (CommRingCat.of T))).left ⟶
          _root_.AlgebraicGeometry.Spec (CommRingCat.of T) :=
        _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom :
            T →+* TensorProduct R T A))
      have hRTLeft :
          (affineGroupBaseChangeOverIso R T A).inv.left ≫
            pullback.snd
              (_root_.AlgebraicGeometry.Spec (CommRingCat.of A) ↘
                _root_.AlgebraicGeometry.Spec (CommRingCat.of R))
              (scalarExtensionSpecMap R T) = directLeft := by
        change (affineGroupBaseChangeOverIso R T A).inv.left ≫
          pullback.snd _ _ = _root_.AlgebraicGeometry.Spec.map _
        exact affineGroupBaseChangeOverIso_inv_snd R T A
      slice_lhs 3 4 =>
        exact overPullback_map_fst (scalarExtensionSpecMap S T)
          (affineGroupBaseChangeOverIso R S A).inv
      slice_lhs 4 5 => exact hRSLeft
      slice_lhs 2 3 => exact hSTRight
      slice_rhs 2 4 =>
        exact overPullbackCompIsoOfEq_hom_app_fst_snd
          (scalarExtensionSpecMap S T) (scalarExtensionSpecMap R S)
          (scalarExtensionSpecMap R T) (scalarExtensionSpecMap_comp R S T)
          ((_root_.AlgebraicGeometry.Spec
            (CommRingCat.of A)).asOver
              (_root_.AlgebraicGeometry.Spec (CommRingCat.of R)))
      slice_rhs 1 2 => exact hRTLeft
      change
        _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.cancelBaseChange R S T T A).toRingHom) ≫
          _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight :
              TensorProduct R S A →ₐ[S]
                TensorProduct S T (TensorProduct R S A)).toRingHom) ≫
          _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeLeftRingHom :
              S →+* TensorProduct R S A)) =
        _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeLeftRingHom :
              T →+* TensorProduct R T A)) ≫
          _root_.AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (algebraMap S T))
      rw [← _root_.AlgebraicGeometry.Spec.map_comp,
        ← _root_.AlgebraicGeometry.Spec.map_comp,
        ← _root_.AlgebraicGeometry.Spec.map_comp]
      exact congrArg _root_.AlgebraicGeometry.Spec.map
        (congrArg CommRingCat.ofHom
          (cancelBaseChange_comp_includeRight_includeLeft R S T A))
  · let outerLeft :
        ((_root_.AlgebraicGeometry.Spec
            (CommRingCat.of
              (TensorProduct S T (TensorProduct R S A)))).asOver
          (_root_.AlgebraicGeometry.Spec (CommRingCat.of T))).left ⟶
        _root_.AlgebraicGeometry.Spec (CommRingCat.of T) :=
      _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom :
          T →+* TensorProduct S T (TensorProduct R S A)))
    have hSTLeft :
        (affineGroupBaseChangeOverIso S T
            (TensorProduct R S A)).inv.left ≫
          pullback.snd
            (_root_.AlgebraicGeometry.Spec
                (CommRingCat.of (TensorProduct R S A)) ↘
              _root_.AlgebraicGeometry.Spec (CommRingCat.of S))
            (scalarExtensionSpecMap S T) = outerLeft := by
      change (affineGroupBaseChangeOverIso S T
          (TensorProduct R S A)).inv.left ≫
        pullback.snd _ _ = _root_.AlgebraicGeometry.Spec.map _
      exact affineGroupBaseChangeOverIso_inv_snd
        S T (TensorProduct R S A)
    let directLeft :
        ((_root_.AlgebraicGeometry.Spec
            (CommRingCat.of (TensorProduct R T A))).asOver
          (_root_.AlgebraicGeometry.Spec (CommRingCat.of T))).left ⟶
        _root_.AlgebraicGeometry.Spec (CommRingCat.of T) :=
      _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom :
          T →+* TensorProduct R T A))
    have hRTLeft :
        (affineGroupBaseChangeOverIso R T A).inv.left ≫
          pullback.snd
            (_root_.AlgebraicGeometry.Spec (CommRingCat.of A) ↘
              _root_.AlgebraicGeometry.Spec (CommRingCat.of R))
            (scalarExtensionSpecMap R T) = directLeft := by
      change (affineGroupBaseChangeOverIso R T A).inv.left ≫
        pullback.snd _ _ = _root_.AlgebraicGeometry.Spec.map _
      exact affineGroupBaseChangeOverIso_inv_snd R T A
    slice_lhs 3 4 =>
      exact overPullback_map_snd (scalarExtensionSpecMap S T)
        (affineGroupBaseChangeOverIso R S A).inv
    slice_lhs 2 3 => exact hSTLeft
    slice_rhs 2 3 =>
      exact overPullbackCompIsoOfEq_hom_app_snd
        (scalarExtensionSpecMap S T) (scalarExtensionSpecMap R S)
        (scalarExtensionSpecMap R T) (scalarExtensionSpecMap_comp R S T)
        ((_root_.AlgebraicGeometry.Spec
          (CommRingCat.of A)).asOver
            (_root_.AlgebraicGeometry.Spec (CommRingCat.of R)))
    slice_rhs 1 2 => exact hRTLeft
    change
      _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.cancelBaseChange R S T T A).toRingHom) ≫
        _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom :
            T →+* TensorProduct S T (TensorProduct R S A))) =
      _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom :
          T →+* TensorProduct R T A))
    rw [← _root_.AlgebraicGeometry.Spec.map_comp]
    exact congrArg _root_.AlgebraicGeometry.Spec.map
      (congrArg CommRingCat.ofHom
        (cancelBaseChange_comp_includeLeft R S T A))

/-- The iterated affine base-change comparisons agree with the canonical
pullback-composition isomorphism and tensor associativity. -/
theorem affineGroupScalarExtensionCompGroupIso_hom
    (R S T A : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [HopfAlgebra R A] :
    (Over.pullback (scalarExtensionSpecMap S T)).map
        (affineGroupBaseChangeGroupIso R S A).hom.hom.hom ≫
      (affineGroupBaseChangeGroupIso S T
        (TensorProduct R S A)).hom.hom.hom ≫
      (affineGroupScalarExtensionCompGroupIso R S T A).hom.hom.hom =
    (overPullbackCompIsoOfEq (scalarExtensionSpecMap S T)
        (scalarExtensionSpecMap R S) (scalarExtensionSpecMap R T)
        (scalarExtensionSpecMap_comp R S T)).inv.app
          (affineGroupSchemeGroup R A).X ≫
      (affineGroupBaseChangeGroupIso R T A).hom.hom.hom := by
  exact congrArg Iso.hom
    (affineGroupScalarExtensionCompOverIso R S T A)

end

end RiemannResearch.AlgebraicGeometry
