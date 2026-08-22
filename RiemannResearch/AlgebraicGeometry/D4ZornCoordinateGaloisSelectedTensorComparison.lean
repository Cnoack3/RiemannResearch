/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.D4ZornCoordinateGaloisSelectedHopfDescent

/-!
# Selected tensor comparisons for finite-Galois D4 coordinate descent

This module begins the comparison of the tensor unit and tensor square selected
by effective affine Čech module descent with the canonical finite-Galois
semilinear Čech data used for the D4 related-triple coordinate Hopf maps.  It
records the scalar pure-generator coaction normalization, proves the
comparison-coalgebra tensor-unit coaction square, and constructs the selected
tensor-unit Čech isomorphism.  The tensor-square coaction square remains open.

Source: user-provided D4 Hopf-descent program.
-/

namespace RiemannResearch.AlgebraicGeometry

noncomputable section

open CategoryTheory
open RiemannResearch.GaloisCohomology
open RiemannResearch.LinearAlgebra.RootSystem.D4Triality
open RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn
open scoped TensorProduct

universe u

/-- For the scalar semilinear Galois action, the coaction of a scalar times a
base-field scalar is the corresponding pure tensor. This is the generator
normalization needed to compare the selected Čech tensor unit with canonical
finite-Galois scalar descent. -/
theorem galoisScalarSemilinearCoaction_mul_algebraMap
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (l : L) (k : K) :
    galoisSemilinearCoaction K L L
        ((galoisScalarSemilinearAlgebraAction K L).toModuleAction K L L)
        (l * algebraMap K L k) =
      l ⊗ₜ[K] algebraMap K L k := by
  apply (galoisSemilinearTensorEquiv K L L
    ((galoisScalarSemilinearAlgebraAction K L).toModuleAction K L L)).injective
  ext σ
  rw [galoisSemilinearTensorEquiv_coaction_apply,
    galoisSemilinearTensorEquiv_tmul_apply]
  simp

/-- Identity on the scalar extension ring, regarded as an equivalence to its
categorical restriction-of-scalars carrier. -/
noncomputable def relatedTripleCoordinateGaloisScalarRestrictLinearEquiv
    (K L : Type u) [Field K] [Field L] [Algebra K L] :
    L ≃ₗ[L] ((ModuleCat.restrictScalars (algebraMap K L)).obj
      (ModuleCat.of L L)) := {
  toFun := fun x => x
  invFun := fun x => x
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  map_add' := by intro x y; rfl
  map_smul' := by intro x y; rfl
}

/-- The comparison carrier of the selected tensor unit, normalized to the
cover field. -/
noncomputable def relatedTripleCoordinateGaloisComparisonTensorUnitLinearEquiv
    (K L : Type u) [Field K] [Field L] [Algebra K L] :
    let LK := (ModuleCat.restrictScalars (algebraMap K L)).obj (ModuleCat.of L L)
    letI : Module K LK := LK.isModule
    letI : IsScalarTower K L LK :=
      IsScalarTower.of_algebraMap_smul (by intro k x; rfl)
    TensorProduct K LK K ≃ₗ[L] L := by
  dsimp only
  let LK := (ModuleCat.restrictScalars (algebraMap K L)).obj (ModuleCat.of L L)
  letI : Module K LK := LK.isModule
  letI : IsScalarTower K L LK :=
    IsScalarTower.of_algebraMap_smul (by intro k x; rfl)
  exact
    (TensorProduct.AlgebraTensorModule.congr
        (relatedTripleCoordinateGaloisScalarRestrictLinearEquiv K L)
        (LinearEquiv.refl K K)).symm.trans
      (TensorProduct.AlgebraTensorModule.rid K L L)

/-- The canonical comparison-coalgebra tensor-unit carrier isomorphism. -/
noncomputable def relatedTripleCoordinateGaloisComparisonTensorUnitIso
    (K L : Type u) [Field K] [Field L] [Algebra K L] :
    ((comonadicModuleDescentComparison (algebraMap K L)).obj
      (ModuleCat.of K K)).A ≅ ModuleCat.of L L := by
  let LK := (ModuleCat.restrictScalars (algebraMap K L)).obj (ModuleCat.of L L)
  letI : Module K LK := LK.isModule
  letI : IsScalarTower K L LK :=
    IsScalarTower.of_algebraMap_smul (by intro k x; rfl)
  change ModuleCat.of L (TensorProduct K LK K) ≅ ModuleCat.of L L
  exact
    (relatedTripleCoordinateGaloisComparisonTensorUnitLinearEquiv K L).toModuleIso

set_option linter.style.haveILetI false in
/-- The comparison tensor-unit carrier isomorphism sends a pure tensor to
ordinary scalar multiplication. -/
theorem relatedTripleCoordinateGaloisComparisonTensorUnitLinearEquiv_tmul
    (K L : Type u) [Field K] [Field L] [Algebra K L] (l : L) (k : K) :
    let LK := (ModuleCat.restrictScalars (algebraMap K L)).obj (ModuleCat.of L L)
    letI : Module K LK := LK.isModule
    letI : IsScalarTower K L LK :=
      IsScalarTower.of_algebraMap_smul (by intro k x; rfl)
    relatedTripleCoordinateGaloisComparisonTensorUnitLinearEquiv K L
        ((relatedTripleCoordinateGaloisScalarRestrictLinearEquiv K L l) ⊗ₜ[K] k) =
      l * algebraMap K L k := by
  dsimp only
  let LK := (ModuleCat.restrictScalars (algebraMap K L)).obj (ModuleCat.of L L)
  letI : Module K LK := LK.isModule
  letI : IsScalarTower K L LK :=
    IsScalarTower.of_algebraMap_smul (by intro k x; rfl)
  let eT := TensorProduct.AlgebraTensorModule.congr
    (relatedTripleCoordinateGaloisScalarRestrictLinearEquiv K L)
    (LinearEquiv.refl K K)
  have hc :
      eT.symm
          ((relatedTripleCoordinateGaloisScalarRestrictLinearEquiv K L l) ⊗ₜ[K] k) =
        l ⊗ₜ[K] k := by
    apply eT.injective
    rw [eT.apply_symm_apply, TensorProduct.AlgebraTensorModule.congr_tmul]
    simp only [LinearEquiv.refl_apply]
  change
    (eT.symm.trans (TensorProduct.AlgebraTensorModule.rid K L L))
        ((relatedTripleCoordinateGaloisScalarRestrictLinearEquiv K L l) ⊗ₜ[K] k) =
      l * algebraMap K L k
  rw [LinearEquiv.trans_apply, hc,
    TensorProduct.AlgebraTensorModule.rid_tmul]
  simp only [Algebra.smul_def]
  exact mul_comm _ _

set_option linter.style.haveILetI false in
/-- The comparison-coalgebra tensor unit is compatible with the canonical
scalar Galois coaction. -/
theorem relatedTripleCoordinateGaloisComparisonTensorUnit_coaction
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    let N := ModuleCat.of K K
    let Q := galoisSemilinearComonadicDescentData K L L
      ((galoisScalarSemilinearAlgebraAction K L).toModuleAction K L L)
    let G := (ModuleCat.extendRestrictScalarsAdj (algebraMap K L)).toComonad
    let e := relatedTripleCoordinateGaloisComparisonTensorUnitIso K L
    ((comonadicModuleDescentComparison (algebraMap K L)).obj N).a ≫
        G.map e.hom = e.hom ≫ Q.a := by
  dsimp only
  let N : ModuleCat K := ModuleCat.of K K
  let Q := galoisSemilinearComonadicDescentData K L L
    ((galoisScalarSemilinearAlgebraAction K L).toModuleAction K L L)
  let G := (ModuleCat.extendRestrictScalarsAdj (algebraMap K L)).toComonad
  let e := relatedTripleCoordinateGaloisComparisonTensorUnitIso K L
  let LK := (ModuleCat.restrictScalars (algebraMap K L)).obj (ModuleCat.of L L)
  letI : Module K LK := LK.isModule
  letI : IsScalarTower K L LK :=
    IsScalarTower.of_algebraMap_smul (by intro k x; rfl)
  let T := TensorProduct K LK K
  let Y : ModuleCat L := G.obj Q.A
  let lhs : T →ₗ[L] Y := ModuleCat.Hom.hom
    (((comonadicModuleDescentComparison (algebraMap K L)).obj N).a ≫ G.map e.hom)
  let rhs : T →ₗ[L] Y := ModuleCat.Hom.hom (e.hom ≫ Q.a)
  apply ModuleCat.hom_ext
  change lhs = rhs
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul l k =>
      dsimp [lhs, rhs]
      change L at l
      have he : e.hom = ModuleCat.ofHom
          (relatedTripleCoordinateGaloisComparisonTensorUnitLinearEquiv
            K L).toLinearMap := by
        rfl
      rw [he]
      change
        ConcreteCategory.hom
            (G.map (ModuleCat.ofHom
              (relatedTripleCoordinateGaloisComparisonTensorUnitLinearEquiv
                K L).toLinearMap))
            (galoisSemilinearComonadicTensorEquiv K L T
              (l ⊗ₜ[K]
                ((relatedTripleCoordinateGaloisScalarRestrictLinearEquiv
                  K L (1 : L)) ⊗ₜ[K] k))) =
          galoisSemilinearComonadicTensorEquiv K L L
            (galoisSemilinearCoaction K L L
              ((galoisScalarSemilinearAlgebraAction K L).toModuleAction K L L)
              (relatedTripleCoordinateGaloisComparisonTensorUnitLinearEquiv
                K L
                ((relatedTripleCoordinateGaloisScalarRestrictLinearEquiv
                  K L l) ⊗ₜ[K] k)))
      rw [galoisSemilinearComonadicTensorMap, LinearMap.baseChange_tmul,
        relatedTripleCoordinateGaloisComparisonTensorUnitLinearEquiv_tmul]
      have hinner :
          ((relatedTripleCoordinateGaloisComparisonTensorUnitLinearEquiv
            K L).toLinearMap.restrictScalars K)
              ((relatedTripleCoordinateGaloisScalarRestrictLinearEquiv
                K L (1 : L)) ⊗ₜ[K] k) = algebraMap K L k := by
        change
          relatedTripleCoordinateGaloisComparisonTensorUnitLinearEquiv K L
              ((relatedTripleCoordinateGaloisScalarRestrictLinearEquiv
                K L (1 : L)) ⊗ₜ[K] k) = algebraMap K L k
        simpa only [one_mul] using
          relatedTripleCoordinateGaloisComparisonTensorUnitLinearEquiv_tmul
            K L 1 k
      rw [hinner]
      exact congrArg (galoisSemilinearComonadicTensorEquiv K L L)
        (galoisScalarSemilinearCoaction_mul_algebraMap K L l k).symm
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- The selected tensor-unit datum, transported through the canonical bridge,
is isomorphic to canonical scalar finite-Galois descent. -/
noncomputable def relatedTripleCoordinateGaloisSelectedTensorUnitComonadicIso
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    let f := CommRingCat.ofHom (algebraMap K L)
    let U := affineCechSelectedTensorUnitDescentData f
    let Q := galoisSemilinearComonadicDescentData K L L
      ((galoisScalarSemilinearAlgebraAction K L).toModuleAction K L L)
    let E := (affineCechComonadicBridge f).equivalence
    E.functor.obj U ≅ Q := by
  dsimp only
  let f := CommRingCat.ofHom (algebraMap K L)
  let N : ModuleCat K := ModuleCat.of K K
  let Q := galoisSemilinearComonadicDescentData K L L
    ((galoisScalarSemilinearAlgebraAction K L).toModuleAction K L L)
  let c := (affineCechComonadicBridge f).comparisonIso.app N
  let e := relatedTripleCoordinateGaloisComparisonTensorUnitIso K L
  let q : (comonadicModuleDescentComparison (algebraMap K L)).obj N ≅ Q :=
    Comonad.Coalgebra.isoMk e
      (relatedTripleCoordinateGaloisComparisonTensorUnit_coaction K L)
  exact c ≪≫ q

/-- The selected affine Čech tensor unit is isomorphic to the inverse-bridge
datum of canonical scalar finite-Galois descent. -/
noncomputable def relatedTripleCoordinateGaloisSelectedTensorUnitCechIso
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    let f := CommRingCat.ofHom (algebraMap K L)
    let U := affineCechSelectedTensorUnitDescentData f
    let Q := galoisSemilinearComonadicDescentData K L L
      ((galoisScalarSemilinearAlgebraAction K L).toModuleAction K L L)
    let E := (affineCechComonadicBridge f).equivalence
    U ≅ E.inverse.obj Q := by
  dsimp only
  let f := CommRingCat.ofHom (algebraMap K L)
  let U := affineCechSelectedTensorUnitDescentData f
  let Q := galoisSemilinearComonadicDescentData K L L
    ((galoisScalarSemilinearAlgebraAction K L).toModuleAction K L L)
  exact affineCechIsoOfComonadicIso f U Q
    (relatedTripleCoordinateGaloisSelectedTensorUnitComonadicIso K L)

end

end RiemannResearch.AlgebraicGeometry
