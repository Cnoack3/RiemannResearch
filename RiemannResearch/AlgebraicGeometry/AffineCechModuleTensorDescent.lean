/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.AffineModuleComonadicBridge
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Selected tensor products in affine Čech module descent

For a faithfully flat affine cover, this file uses effective module descent to
select a Čech descent datum whose descended module is the tensor product of two
selected descended modules.  It then identifies the cover object with the
tensor product of the two original cover objects via distributivity of scalar
extension over tensor products.

This supplies the tensor comparison needed before descending algebra and Hopf
structure maps, together with morphism-level functoriality and naturality.
It also constructs the selected associator, tensor unit, and symmetry, proves
exact cover-level formulas for the associator, both unitors, and symmetry, and
packages the unitors and symmetry as natural isomorphisms.  The associator is
natural, and the pentagon, triangle, hexagon, and symmetry-involutivity laws
are verified explicitly.  Monoidal typeclass packaging is not asserted here.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory

namespace RiemannResearch.AlgebraicGeometry

/-- The selected preimage of a comparison object is canonically isomorphic to
the original base module. -/
noncomputable def affineCechDescendedComparisonObjIso
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat) (M : ModuleCat R) :
    affineCechDescendedModule f hf
        ((affineCechModuleDescentComparison f).obj M) ≅ M := by
  let F := affineCechModuleDescentComparison f
  let _ : F.IsEquivalence :=
    affineCechModuleDescentComparison_isEquivalence f hf
  let e := affineCechDescendedModuleIso f hf (F.obj M)
  refine Iso.mk (F.preimage e.hom) (F.preimage e.inv) ?_ ?_
  · apply F.map_injective
    rw [F.map_comp, F.map_preimage, F.map_preimage, F.map_id]
    exact e.hom_inv_id
  · apply F.map_injective
    rw [F.map_comp, F.map_preimage, F.map_preimage, F.map_id]
    exact e.inv_hom_id

/-- The tensor product of the selected descended modules, regarded through
the comparison functor as a chosen Čech descent datum. -/
noncomputable def affineCechSelectedTensorDescentData
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D E : AffineCechModuleDescentData f) :
    AffineCechModuleDescentData f :=
  (affineCechModuleDescentComparison f).obj
    (ModuleCat.of R
      (TensorProduct R
        (affineCechDescendedModule f hf D)
        (affineCechDescendedModule f hf E)))

/-- Descending the selected tensor datum recovers the tensor product of the
two selected descended modules. -/
noncomputable def affineCechSelectedTensorDescendedIso
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D E : AffineCechModuleDescentData f) :
    affineCechDescendedModule f hf
        (affineCechSelectedTensorDescentData f hf D E) ≅
      ModuleCat.of R
        (TensorProduct R
          (affineCechDescendedModule f hf D)
          (affineCechDescendedModule f hf E)) :=
  affineCechDescendedComparisonObjIso f hf _

private noncomputable def affineCechScalarRestrictLinearEquiv
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    A ≃ₗ[A]
      ((ModuleCat.restrictScalars f.hom).obj (ModuleCat.of A A)) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Scalar extension of the tensor product of the selected descended modules
is the tensor product of the supplied cover modules. -/
noncomputable def affineCechDescendedTensorBaseChangeIso
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D E : AffineCechModuleDescentData f) :
    (ModuleCat.extendScalars f.hom).obj
        (ModuleCat.of R
          (TensorProduct R
            (affineCechDescendedModule f hf D)
            (affineCechDescendedModule f hf E))) ≅
      ModuleCat.of A
        (TensorProduct A
          ((AffineCechModuleDescentData.evaluation f).obj D)
          ((AffineCechModuleDescentData.evaluation f).obj E)) := by
  letI : Algebra R A := f.hom.toAlgebra
  let MD := affineCechDescendedModule f hf D
  let ME := affineCechDescendedModule f hf E
  let DA : ModuleCat A := (AffineCechModuleDescentData.evaluation f).obj D
  let EA : ModuleCat A := (AffineCechModuleDescentData.evaluation f).obj E
  let eD := affineCechDescendedModuleBaseChangeIso f hf D
  let eE := affineCechDescendedModuleBaseChangeIso f hf E
  let AR := (ModuleCat.restrictScalars f.hom).obj (ModuleCat.of A A)
  letI : Module R AR := AR.isModule
  letI : IsScalarTower R A AR :=
    IsScalarTower.of_algebraMap_smul (by intro r x; rfl)
  let eDRaw : TensorProduct R A MD ≃ₗ[A] DA :=
    (TensorProduct.AlgebraTensorModule.congr
      (affineCechScalarRestrictLinearEquiv f)
      (LinearEquiv.refl R MD)).trans eD.toLinearEquiv
  let eERaw : TensorProduct R A ME ≃ₗ[A] EA :=
    (TensorProduct.AlgebraTensorModule.congr
      (affineCechScalarRestrictLinearEquiv f)
      (LinearEquiv.refl R ME)).trans eE.toLinearEquiv
  change ModuleCat.of A (TensorProduct R AR (TensorProduct R MD ME)) ≅
    ModuleCat.of A
      (TensorProduct A DA EA)
  exact ((TensorProduct.AlgebraTensorModule.congr
      (affineCechScalarRestrictLinearEquiv f).symm
      (LinearEquiv.refl R (TensorProduct R MD ME))).trans
    ((TensorProduct.AlgebraTensorModule.distribBaseChange R A MD ME).trans
      (TensorProduct.congr eDRaw eERaw))).toModuleIso

set_option maxHeartbeats 800000 in
-- Unfolding the base-change equivalence on a pure tensor is elaboration-intensive.
set_option linter.style.haveILetI false in
/-- The tensor base-change comparison on a pure tensor generator. -/
@[simp] theorem affineCechDescendedTensorBaseChangeIso_hom_tmul
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D E : AffineCechModuleDescentData f)
    (a : A) (m : affineCechDescendedModule f hf D)
    (n : affineCechDescendedModule f hf E) :
    (affineCechDescendedTensorBaseChangeIso f hf D E).hom
        (a ⊗ₜ[R] (m ⊗ₜ[R] n)) =
      (show (AffineCechModuleDescentData.evaluation f).obj D from
        ModuleCat.Hom.hom
          (affineCechDescendedModuleBaseChangeIso f hf D).hom
          (a ⊗ₜ[R] m)) ⊗ₜ[A]
      (show (AffineCechModuleDescentData.evaluation f).obj E from
        ModuleCat.Hom.hom
          (affineCechDescendedModuleBaseChangeIso f hf E).hom
          ((1 : A) ⊗ₜ[R] n)) := by
  letI : Algebra R A := f.hom.toAlgebra
  let MD := affineCechDescendedModule f hf D
  let ME := affineCechDescendedModule f hf E
  let DA : ModuleCat A := (AffineCechModuleDescentData.evaluation f).obj D
  let EA : ModuleCat A := (AffineCechModuleDescentData.evaluation f).obj E
  let eD := affineCechDescendedModuleBaseChangeIso f hf D
  let eE := affineCechDescendedModuleBaseChangeIso f hf E
  let AR := (ModuleCat.restrictScalars f.hom).obj (ModuleCat.of A A)
  letI : Module R AR := AR.isModule
  letI : IsScalarTower R A AR :=
    IsScalarTower.of_algebraMap_smul (by intro r x; rfl)
  let eDRaw : TensorProduct R A MD ≃ₗ[A] DA :=
    (TensorProduct.AlgebraTensorModule.congr
      (affineCechScalarRestrictLinearEquiv f)
      (LinearEquiv.refl R MD)).trans eD.toLinearEquiv
  let eERaw : TensorProduct R A ME ≃ₗ[A] EA :=
    (TensorProduct.AlgebraTensorModule.congr
      (affineCechScalarRestrictLinearEquiv f)
      (LinearEquiv.refl R ME)).trans eE.toLinearEquiv
  change
    (((TensorProduct.AlgebraTensorModule.congr
        (affineCechScalarRestrictLinearEquiv f).symm
        (LinearEquiv.refl R (TensorProduct R MD ME))).trans
      ((TensorProduct.AlgebraTensorModule.distribBaseChange R A MD ME).trans
        (TensorProduct.congr eDRaw eERaw)))
      (a ⊗ₜ[R] (m ⊗ₜ[R] n))) = _
  rfl

/-- The cover object of the selected tensor Čech datum is canonically the
tensor product of the two original cover objects. -/
noncomputable def affineCechSelectedTensorDescentDataCoverIso
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D E : AffineCechModuleDescentData f) :
    (affineCechSelectedTensorDescentData f hf D E).obj PUnit.unit ≅
      ModuleCat.of A
        (TensorProduct A
          ((AffineCechModuleDescentData.evaluation f).obj D)
          ((AffineCechModuleDescentData.evaluation f).obj E)) :=
  affineCechDescendedTensorBaseChangeIso f hf D E

/-- The selected descended tensor datum has the expected cover-level
base-change formula. -/
noncomputable def affineCechSelectedTensorDescendedBaseChangeIso
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D E : AffineCechModuleDescentData f) :
    (ModuleCat.extendScalars f.hom).obj
        (affineCechDescendedModule f hf
          (affineCechSelectedTensorDescentData f hf D E)) ≅
      ModuleCat.of A
        (TensorProduct A
          ((AffineCechModuleDescentData.evaluation f).obj D)
          ((AffineCechModuleDescentData.evaluation f).obj E)) :=
  affineCechDescendedModuleBaseChangeIso f hf
      (affineCechSelectedTensorDescentData f hf D E) ≪≫
    affineCechSelectedTensorDescentDataCoverIso f hf D E

set_option maxHeartbeats 800000 in
-- Normalizing the comparison-functor square requires substantial categorical reduction.
/-- The selected descended-map formula in comparison-square form. -/
theorem affineCechDescendedModuleHom_baseChange_comp
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    {D D' : AffineCechModuleDescentData f} (g : D ⟶ D') :
    (ModuleCat.extendScalars f.hom).map
        (affineCechDescendedModuleHom f hf g) ≫
        (affineCechDescendedModuleBaseChangeIso f hf D').hom =
      (affineCechDescendedModuleBaseChangeIso f hf D).hom ≫
        (AffineCechModuleDescentData.evaluation f).map g := by
  let eD :
      (ModuleCat.extendScalars f.hom).obj
          (affineCechDescendedModule f hf D) ≅
        (AffineCechModuleDescentData.evaluation f).obj D :=
    affineCechDescendedModuleBaseChangeIso f hf D
  let eD' :
      (ModuleCat.extendScalars f.hom).obj
          (affineCechDescendedModule f hf D') ≅
        (AffineCechModuleDescentData.evaluation f).obj D' :=
    affineCechDescendedModuleBaseChangeIso f hf D'
  change
    (ModuleCat.extendScalars f.hom).map
        (affineCechDescendedModuleHom f hf g) ≫ eD'.hom =
      eD.hom ≫ (AffineCechModuleDescentData.evaluation f).map g
  rw [affineCechDescendedModuleHom_baseChange]
  change
    ((eD.hom ≫ (AffineCechModuleDescentData.evaluation f).map g) ≫
        eD'.inv) ≫ eD'.hom =
      eD.hom ≫ (AffineCechModuleDescentData.evaluation f).map g
  rw [Category.assoc, eD'.inv_hom_id, Category.comp_id]

set_option maxHeartbeats 800000 in
-- Evaluating the comparison square on scalar-extension tensors unfolds both chosen isomorphisms.
set_option linter.style.haveILetI false in
/-- The selected descended-map base-change square evaluated on a pure tensor. -/
theorem affineCechDescendedModuleHom_baseChange_apply
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    {D D' : AffineCechModuleDescentData f} (g : D ⟶ D')
    (a : A) (m : affineCechDescendedModule f hf D) :
    letI : Algebra R A := f.hom.toAlgebra
    (show (AffineCechModuleDescentData.evaluation f).obj D' from
      ModuleCat.Hom.hom
        (affineCechDescendedModuleBaseChangeIso f hf D').hom
        (ModuleCat.Hom.hom
          ((ModuleCat.extendScalars f.hom).map
            (affineCechDescendedModuleHom f hf g))
          (a ⊗ₜ[R] m))) =
      ModuleCat.Hom.hom
        ((AffineCechModuleDescentData.evaluation f).map g)
        (show (AffineCechModuleDescentData.evaluation f).obj D from
          ModuleCat.Hom.hom
            (affineCechDescendedModuleBaseChangeIso f hf D).hom
            (a ⊗ₜ[R] m)) := by
  letI : Algebra R A := f.hom.toAlgebra
  let eD :
      (ModuleCat.extendScalars f.hom).obj
          (affineCechDescendedModule f hf D) ≅
        (AffineCechModuleDescentData.evaluation f).obj D :=
    affineCechDescendedModuleBaseChangeIso f hf D
  let eD' :
      (ModuleCat.extendScalars f.hom).obj
          (affineCechDescendedModule f hf D') ≅
        (AffineCechModuleDescentData.evaluation f).obj D' :=
    affineCechDescendedModuleBaseChangeIso f hf D'
  have sq := affineCechDescendedModuleHom_baseChange_comp f hf g
  have p := congrArg
    (fun q => ModuleCat.Hom.hom q (a ⊗ₜ[R] m)) sq
  change
    ModuleCat.Hom.hom eD'.hom
        (ModuleCat.Hom.hom
          ((ModuleCat.extendScalars f.hom).map
            (affineCechDescendedModuleHom f hf g))
          (a ⊗ₜ[R] m)) =
      ModuleCat.Hom.hom
        ((AffineCechModuleDescentData.evaluation f).map g)
        (ModuleCat.Hom.hom eD.hom (a ⊗ₜ[R] m))
  exact p

/-- Tensoring selected descended morphisms gives a morphism between the
corresponding base-ring tensor products. -/
noncomputable def affineCechDescendedTensorMap
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    {D D' E E' : AffineCechModuleDescentData f}
    (g : D ⟶ D') (h : E ⟶ E') :
    ModuleCat.of R
        (TensorProduct R
          (affineCechDescendedModule f hf D)
          (affineCechDescendedModule f hf E)) ⟶
      ModuleCat.of R
        (TensorProduct R
          (affineCechDescendedModule f hf D')
          (affineCechDescendedModule f hf E')) :=
  ModuleCat.ofHom
    (TensorProduct.map
      (ModuleCat.Hom.hom (affineCechDescendedModuleHom f hf g))
      (ModuleCat.Hom.hom (affineCechDescendedModuleHom f hf h)))

set_option linter.style.haveILetI false in
/-- Scalar extension of a selected tensor map on a pure tensor generator. -/
@[simp] theorem affineCechDescendedTensorMap_baseChange_tmul
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    {D D' E E' : AffineCechModuleDescentData f}
    (g : D ⟶ D') (h : E ⟶ E')
    (a : A) (m : affineCechDescendedModule f hf D)
    (n : affineCechDescendedModule f hf E) :
    letI : Algebra R A := f.hom.toAlgebra
    (ModuleCat.extendScalars f.hom).map
        (affineCechDescendedTensorMap f hf g h)
        (a ⊗ₜ[R] (m ⊗ₜ[R] n)) =
      a ⊗ₜ[R]
        (ModuleCat.Hom.hom (affineCechDescendedModuleHom f hf g) m ⊗ₜ[R]
          ModuleCat.Hom.hom (affineCechDescendedModuleHom f hf h) n) := by
  letI : Algebra R A := f.hom.toAlgebra
  change LinearMap.baseChange A
      (TensorProduct.map
        (ModuleCat.Hom.hom (affineCechDescendedModuleHom f hf g))
        (ModuleCat.Hom.hom (affineCechDescendedModuleHom f hf h)))
      (a ⊗ₜ[R] (m ⊗ₜ[R] n)) = _
  rw [LinearMap.baseChange_tmul, TensorProduct.map_tmul]

set_option maxHeartbeats 800000 in
-- Two nested tensor inductions are required for the naturality calculation.
set_option linter.style.haveILetI false in
/-- The tensor base-change comparison is natural in both descent data. -/
theorem affineCechDescendedTensorBaseChangeIso_natural
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    {D D' E E' : AffineCechModuleDescentData f}
    (g : D ⟶ D') (h : E ⟶ E') :
    (ModuleCat.extendScalars f.hom).map
        (affineCechDescendedTensorMap f hf g h) ≫
        (affineCechDescendedTensorBaseChangeIso f hf D' E').hom =
      (affineCechDescendedTensorBaseChangeIso f hf D E).hom ≫
        ModuleCat.ofHom
          (TensorProduct.map
            (ModuleCat.Hom.hom
              ((AffineCechModuleDescentData.evaluation f).map g))
            (ModuleCat.Hom.hom
              ((AffineCechModuleDescentData.evaluation f).map h))) := by
  letI : Algebra R A := f.hom.toAlgebra
  let MD := affineCechDescendedModule f hf D
  let ME := affineCechDescendedModule f hf E
  let DA : ModuleCat A := (AffineCechModuleDescentData.evaluation f).obj D
  let EA : ModuleCat A := (AffineCechModuleDescentData.evaluation f).obj E
  let DA' : ModuleCat A := (AffineCechModuleDescentData.evaluation f).obj D'
  let EA' : ModuleCat A := (AffineCechModuleDescentData.evaluation f).obj E'
  let eDE := affineCechDescendedTensorBaseChangeIso f hf D E
  let eD'E' := affineCechDescendedTensorBaseChangeIso f hf D' E'
  let evalg : DA →ₗ[A] DA' :=
    ModuleCat.Hom.hom ((AffineCechModuleDescentData.evaluation f).map g)
  let evalh : EA →ₗ[A] EA' :=
    ModuleCat.Hom.hom ((AffineCechModuleDescentData.evaluation f).map h)
  let L : TensorProduct R A (TensorProduct R MD ME) →ₗ[A]
      TensorProduct A DA' EA' :=
    ModuleCat.Hom.hom
      ((ModuleCat.extendScalars f.hom).map
          (affineCechDescendedTensorMap f hf g h) ≫ eD'E'.hom)
  let K : TensorProduct R A (TensorProduct R MD ME) →ₗ[A]
      TensorProduct A DA' EA' :=
    ModuleCat.Hom.hom
      (eDE.hom ≫ ModuleCat.ofHom (TensorProduct.map evalg evalh))
  apply ModuleCat.hom_ext
  change L = K
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a z =>
      induction z using TensorProduct.induction_on with
      | zero => simp only [TensorProduct.tmul_zero, map_zero]
      | tmul m n =>
          let gm :=
            ModuleCat.Hom.hom (affineCechDescendedModuleHom f hf g) m
          let hn :=
            ModuleCat.Hom.hom (affineCechDescendedModuleHom f hf h) n
          have hmap :=
            affineCechDescendedTensorMap_baseChange_tmul
              f hf g h a m n
          have hbc' :=
            affineCechDescendedTensorBaseChangeIso_hom_tmul
              f hf D' E' a gm hn
          have hbc :=
            affineCechDescendedTensorBaseChangeIso_hom_tmul
              f hf D E a m n
          have hgm :=
            affineCechDescendedModuleHom_baseChange_apply f hf g a m
          have hhn :=
            affineCechDescendedModuleHom_baseChange_apply f hf h (1 : A) n
          change
            ModuleCat.Hom.hom eD'E'.hom
                (ModuleCat.Hom.hom
                  ((ModuleCat.extendScalars f.hom).map
                    (affineCechDescendedTensorMap f hf g h))
                  (a ⊗ₜ[R] (m ⊗ₜ[R] n))) =
              TensorProduct.map evalg evalh
                (ModuleCat.Hom.hom eDE.hom
                  (a ⊗ₜ[R] (m ⊗ₜ[R] n)))
          calc
            _ = ModuleCat.Hom.hom eD'E'.hom
                (a ⊗ₜ[R] (gm ⊗ₜ[R] hn)) :=
              congrArg (ModuleCat.Hom.hom eD'E'.hom) hmap
            _ =
                (show DA' from ModuleCat.Hom.hom
                  (affineCechDescendedModuleBaseChangeIso f hf D').hom
                  (a ⊗ₜ[R] gm)) ⊗ₜ[A]
                (show EA' from ModuleCat.Hom.hom
                  (affineCechDescendedModuleBaseChangeIso f hf E').hom
                  ((1 : A) ⊗ₜ[R] hn)) := hbc'
            _ = evalg
                  (show DA from ModuleCat.Hom.hom
                    (affineCechDescendedModuleBaseChangeIso f hf D).hom
                    (a ⊗ₜ[R] m)) ⊗ₜ[A]
                evalh
                  (show EA from ModuleCat.Hom.hom
                    (affineCechDescendedModuleBaseChangeIso f hf E).hom
                    ((1 : A) ⊗ₜ[R] n)) :=
              congrArg₂ (fun (x : DA') (y : EA') => x ⊗ₜ[A] y) hgm hhn
            _ = TensorProduct.map evalg evalh
                ((show DA from ModuleCat.Hom.hom
                    (affineCechDescendedModuleBaseChangeIso f hf D).hom
                    (a ⊗ₜ[R] m)) ⊗ₜ[A]
                  (show EA from ModuleCat.Hom.hom
                    (affineCechDescendedModuleBaseChangeIso f hf E).hom
                    ((1 : A) ⊗ₜ[R] n))) := by
              rw [TensorProduct.map_tmul]
            _ = _ := congrArg (TensorProduct.map evalg evalh) hbc.symm
      | add x y hx hy =>
          simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Tensoring selected descended identity morphisms gives the identity. -/
@[simp] theorem affineCechDescendedTensorMap_id
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D E : AffineCechModuleDescentData f) :
    affineCechDescendedTensorMap f hf (𝟙 D) (𝟙 E) =
      𝟙 (ModuleCat.of R
        (TensorProduct R
          (affineCechDescendedModule f hf D)
          (affineCechDescendedModule f hf E))) := by
  unfold affineCechDescendedTensorMap
  rw [affineCechDescendedModuleHom_id, affineCechDescendedModuleHom_id]
  apply ModuleCat.hom_ext
  change TensorProduct.map LinearMap.id LinearMap.id = LinearMap.id
  exact TensorProduct.map_id

/-- Tensoring selected descended morphisms preserves composition. -/
@[simp] theorem affineCechDescendedTensorMap_comp
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    {D₁ D₂ D₃ E₁ E₂ E₃ : AffineCechModuleDescentData f}
    (g₁ : D₁ ⟶ D₂) (g₂ : D₂ ⟶ D₃)
    (h₁ : E₁ ⟶ E₂) (h₂ : E₂ ⟶ E₃) :
    affineCechDescendedTensorMap f hf (g₁ ≫ g₂) (h₁ ≫ h₂) =
      affineCechDescendedTensorMap f hf g₁ h₁ ≫
        affineCechDescendedTensorMap f hf g₂ h₂ := by
  unfold affineCechDescendedTensorMap
  rw [affineCechDescendedModuleHom_comp,
    affineCechDescendedModuleHom_comp]
  apply ModuleCat.hom_ext
  change TensorProduct.map
      ((ModuleCat.Hom.hom (affineCechDescendedModuleHom f hf g₂)).comp
        (ModuleCat.Hom.hom (affineCechDescendedModuleHom f hf g₁)))
      ((ModuleCat.Hom.hom (affineCechDescendedModuleHom f hf h₂)).comp
        (ModuleCat.Hom.hom (affineCechDescendedModuleHom f hf h₁))) =
    (TensorProduct.map
      (ModuleCat.Hom.hom (affineCechDescendedModuleHom f hf g₂))
      (ModuleCat.Hom.hom (affineCechDescendedModuleHom f hf h₂))).comp
    (TensorProduct.map
      (ModuleCat.Hom.hom (affineCechDescendedModuleHom f hf g₁))
      (ModuleCat.Hom.hom (affineCechDescendedModuleHom f hf h₁)))
  exact TensorProduct.map_comp _ _ _ _

/-- The selected tensor construction on morphisms of Čech descent data. -/
noncomputable def affineCechSelectedTensorMap
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    {D D' E E' : AffineCechModuleDescentData f}
    (g : D ⟶ D') (h : E ⟶ E') :
    affineCechSelectedTensorDescentData f hf D E ⟶
      affineCechSelectedTensorDescentData f hf D' E' :=
  (affineCechModuleDescentComparison f).map
    (affineCechDescendedTensorMap f hf g h)

set_option maxHeartbeats 800000 in
-- This unfolds the comparison functor at the cover object.
/-- The cover-level tensor comparison is natural in both descent data. -/
theorem affineCechSelectedTensorDescentDataCoverIso_natural
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    {D D' E E' : AffineCechModuleDescentData f}
    (g : D ⟶ D') (h : E ⟶ E') :
    (affineCechSelectedTensorMap f hf g h).hom PUnit.unit ≫
        (affineCechSelectedTensorDescentDataCoverIso f hf D' E').hom =
      (affineCechSelectedTensorDescentDataCoverIso f hf D E).hom ≫
        ModuleCat.ofHom
          (TensorProduct.map
            (ModuleCat.Hom.hom
              ((AffineCechModuleDescentData.evaluation f).map g))
            (ModuleCat.Hom.hom
              ((AffineCechModuleDescentData.evaluation f).map h))) := by
  exact affineCechDescendedTensorBaseChangeIso_natural f hf g h

/-- The selected tensor construction preserves identity morphisms. -/
@[simp] theorem affineCechSelectedTensorMap_id
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D E : AffineCechModuleDescentData f) :
    affineCechSelectedTensorMap f hf (𝟙 D) (𝟙 E) =
      𝟙 (affineCechSelectedTensorDescentData f hf D E) := by
  rw [affineCechSelectedTensorMap, affineCechDescendedTensorMap_id]
  exact (affineCechModuleDescentComparison f).map_id _

/-- The selected tensor construction preserves composition. -/
@[simp] theorem affineCechSelectedTensorMap_comp
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    {D₁ D₂ D₃ E₁ E₂ E₃ : AffineCechModuleDescentData f}
    (g₁ : D₁ ⟶ D₂) (g₂ : D₂ ⟶ D₃)
    (h₁ : E₁ ⟶ E₂) (h₂ : E₂ ⟶ E₃) :
    affineCechSelectedTensorMap f hf (g₁ ≫ g₂) (h₁ ≫ h₂) =
      affineCechSelectedTensorMap f hf g₁ h₁ ≫
        affineCechSelectedTensorMap f hf g₂ h₂ := by
  rw [affineCechSelectedTensorMap, affineCechDescendedTensorMap_comp]
  exact (affineCechModuleDescentComparison f).map_comp _ _

/-- The selected tensor products and tensor maps form a bifunctor on chosen
Čech module descent data. -/
noncomputable def affineCechSelectedTensorFunctor
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat) :
    (AffineCechModuleDescentData f × AffineCechModuleDescentData f) ⥤
      AffineCechModuleDescentData f where
  obj X := affineCechSelectedTensorDescentData f hf X.1 X.2
  map g := affineCechSelectedTensorMap f hf g.1 g.2
  map_id X := affineCechSelectedTensorMap_id f hf X.1 X.2
  map_comp g h :=
    affineCechSelectedTensorMap_comp f hf g.1 h.1 g.2 h.2

/-- Scalar extension of the selected-preimage comparison is the chosen
base-change comparison for the corresponding comparison object. -/
theorem affineCechDescendedComparisonObjIso_hom_baseChange
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat) (M : ModuleCat R) :
    (ModuleCat.extendScalars f.hom).map
        (affineCechDescendedComparisonObjIso f hf M).hom =
      (affineCechDescendedModuleBaseChangeIso f hf
        ((affineCechModuleDescentComparison f).obj M)).hom := by
  let G := affineCechModuleDescentComparison f
  let _ : G.IsEquivalence :=
    affineCechModuleDescentComparison_isEquivalence f hf
  let e := affineCechDescendedModuleIso f hf (G.obj M)
  change (AffineCechModuleDescentData.evaluation f).map
      (G.map (G.preimage e.hom)) =
    (AffineCechModuleDescentData.evaluation f).map e.hom
  rw [G.map_preimage]

/-- The inverse selected-preimage comparison has the corresponding inverse
base-change formula. -/
theorem affineCechDescendedComparisonObjIso_inv_baseChange
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat) (M : ModuleCat R) :
    (ModuleCat.extendScalars f.hom).map
        (affineCechDescendedComparisonObjIso f hf M).inv =
      (affineCechDescendedModuleBaseChangeIso f hf
        ((affineCechModuleDescentComparison f).obj M)).inv := by
  let G := affineCechModuleDescentComparison f
  let _ : G.IsEquivalence :=
    affineCechModuleDescentComparison_isEquivalence f hf
  let e := affineCechDescendedModuleIso f hf (G.obj M)
  change (AffineCechModuleDescentData.evaluation f).map
      (G.map (G.preimage e.inv)) =
    (AffineCechModuleDescentData.evaluation f).map e.inv
  rw [G.map_preimage]

set_option linter.style.haveILetI false in

/-- Scalar extension of an arbitrary base-module morphism on a pure
scalar-extension tensor. -/
@[simp] theorem affineCechModuleHom_baseChange_tmul
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    {M N : ModuleCat R} (q : M ⟶ N)
    (a : A) (m : M) :
    letI : Algebra R A := f.hom.toAlgebra
    (ModuleCat.extendScalars f.hom).map q (a ⊗ₜ[R] m) =
      a ⊗ₜ[R] ModuleCat.Hom.hom q m := by
  letI : Algebra R A := f.hom.toAlgebra
  change LinearMap.baseChange A (ModuleCat.Hom.hom q) (a ⊗ₜ[R] m) = _
  rw [LinearMap.baseChange_tmul]

set_option linter.style.haveILetI false in
/-- Base change of the inverse selected tensor comparison cancels the chosen
base-change comparison on pure scalar-extension tensors. -/
@[simp] theorem affineCechSelectedTensorDescendedIso_baseChange_inv_tmul
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D E : AffineCechModuleDescentData f)
    (a : A)
    (z : TensorProduct R
      (affineCechDescendedModule f hf D)
      (affineCechDescendedModule f hf E)) :
    letI : Algebra R A := f.hom.toAlgebra
    ModuleCat.Hom.hom
      (affineCechDescendedModuleBaseChangeIso f hf
        (affineCechSelectedTensorDescentData f hf D E)).hom
        (a ⊗ₜ[R]
          ModuleCat.Hom.hom
            (affineCechSelectedTensorDescendedIso f hf D E).inv z) =
      a ⊗ₜ[R] z := by
  letI : Algebra R A := f.hom.toAlgebra
  let M := ModuleCat.of R
    (TensorProduct R
      (affineCechDescendedModule f hf D)
      (affineCechDescendedModule f hf E))
  let e := affineCechDescendedComparisonObjIso f hf M
  let b := affineCechDescendedModuleBaseChangeIso f hf
    ((affineCechModuleDescentComparison f).obj M)
  change ModuleCat.Hom.hom b.hom
      (a ⊗ₜ[R] ModuleCat.Hom.hom e.inv z) = a ⊗ₜ[R] z
  have hmap := affineCechDescendedComparisonObjIso_hom_baseChange f hf M
  have happ := congrArg
    (fun q => ModuleCat.Hom.hom q
      (a ⊗ₜ[R] ModuleCat.Hom.hom e.inv z)) hmap
  calc
    _ = ModuleCat.Hom.hom
        ((ModuleCat.extendScalars f.hom).map e.hom)
        (a ⊗ₜ[R] ModuleCat.Hom.hom e.inv z) := happ.symm
    _ = _ := by
      rw [affineCechModuleHom_baseChange_tmul]
      exact congrArg (fun w => a ⊗ₜ[R] w) (e.inv_hom_id_apply z)

/-- The base-ring associator for selected tensor data. The ordinary tensor
associator is conjugated by the chosen descended-module comparisons for the
two nested selected tensor objects. -/
noncomputable def affineCechSelectedTensorAssociatorBaseIso
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D E F : AffineCechModuleDescentData f) :
    ModuleCat.of R
        (TensorProduct R
          (affineCechDescendedModule f hf
            (affineCechSelectedTensorDescentData f hf D E))
          (affineCechDescendedModule f hf F)) ≅
      ModuleCat.of R
        (TensorProduct R
          (affineCechDescendedModule f hf D)
          (affineCechDescendedModule f hf
            (affineCechSelectedTensorDescentData f hf E F))) :=
  ((TensorProduct.congr
      (affineCechSelectedTensorDescendedIso f hf D E).toLinearEquiv
      (LinearEquiv.refl R (affineCechDescendedModule f hf F))).trans
    ((TensorProduct.assoc R
      (affineCechDescendedModule f hf D)
      (affineCechDescendedModule f hf E)
      (affineCechDescendedModule f hf F)).trans
    (TensorProduct.congr
      (LinearEquiv.refl R (affineCechDescendedModule f hf D))
      (affineCechSelectedTensorDescendedIso f hf E F).symm.toLinearEquiv))).toModuleIso

set_option linter.style.haveILetI false in
/-- Scalar extension applies the selected associator base map to the module
factor of a pure scalar-extension tensor. -/
@[simp] theorem affineCechSelectedTensorAssociatorBaseIso_baseChange_tmul
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D E F : AffineCechModuleDescentData f)
    (a : A)
    (m : affineCechDescendedModule f hf
      (affineCechSelectedTensorDescentData f hf D E))
    (n : affineCechDescendedModule f hf F) :
    letI : Algebra R A := f.hom.toAlgebra
    (ModuleCat.extendScalars f.hom).map
        (affineCechSelectedTensorAssociatorBaseIso f hf D E F).hom
        (a ⊗ₜ[R] (m ⊗ₜ[R] n)) =
      a ⊗ₜ[R]
        ((affineCechSelectedTensorAssociatorBaseIso f hf D E F).hom
          (m ⊗ₜ[R] n)) := by
  letI : Algebra R A := f.hom.toAlgebra
  change LinearMap.baseChange A _ (a ⊗ₜ[R] (m ⊗ₜ[R] n)) = _
  rw [LinearMap.baseChange_tmul]

/-- The selected-datum associator obtained by comparing the conjugated
base-ring tensor associator. -/
noncomputable def affineCechSelectedTensorAssociatorIso
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D E F : AffineCechModuleDescentData f) :
    affineCechSelectedTensorDescentData f hf
        (affineCechSelectedTensorDescentData f hf D E) F ≅
      affineCechSelectedTensorDescentData f hf D
        (affineCechSelectedTensorDescentData f hf E F) :=
  (affineCechModuleDescentComparison f).mapIso
    (affineCechSelectedTensorAssociatorBaseIso f hf D E F)

/-- The left-associated selected tensor cover, identified with the
left-associated tensor product of the three supplied cover modules. -/
noncomputable def affineCechSelectedTensorLeftAssociatedCoverIso
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D E F : AffineCechModuleDescentData f) :
    (affineCechSelectedTensorDescentData f hf
        (affineCechSelectedTensorDescentData f hf D E) F).obj PUnit.unit ≅
      ModuleCat.of A
        (TensorProduct A
          (TensorProduct A
            ((AffineCechModuleDescentData.evaluation f).obj D)
            ((AffineCechModuleDescentData.evaluation f).obj E))
          ((AffineCechModuleDescentData.evaluation f).obj F)) := by
  let DE : ModuleCat A :=
    (AffineCechModuleDescentData.evaluation f).obj
      (affineCechSelectedTensorDescentData f hf D E)
  let DA : ModuleCat A := (AffineCechModuleDescentData.evaluation f).obj D
  let EA : ModuleCat A := (AffineCechModuleDescentData.evaluation f).obj E
  let FA : ModuleCat A := (AffineCechModuleDescentData.evaluation f).obj F
  let eDE : DE ≅ ModuleCat.of A (TensorProduct A DA EA) :=
    affineCechSelectedTensorDescentDataCoverIso f hf D E
  exact affineCechSelectedTensorDescentDataCoverIso f hf
      (affineCechSelectedTensorDescentData f hf D E) F ≪≫
    (TensorProduct.congr eDE.toLinearEquiv
      (LinearEquiv.refl A FA)).toModuleIso

/-- The right-associated selected tensor cover, identified with the
right-associated tensor product of the three supplied cover modules. -/
noncomputable def affineCechSelectedTensorRightAssociatedCoverIso
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D E F : AffineCechModuleDescentData f) :
    (affineCechSelectedTensorDescentData f hf D
        (affineCechSelectedTensorDescentData f hf E F)).obj PUnit.unit ≅
      ModuleCat.of A
        (TensorProduct A
          ((AffineCechModuleDescentData.evaluation f).obj D)
          (TensorProduct A
            ((AffineCechModuleDescentData.evaluation f).obj E)
            ((AffineCechModuleDescentData.evaluation f).obj F))) := by
  let EF : ModuleCat A :=
    (AffineCechModuleDescentData.evaluation f).obj
      (affineCechSelectedTensorDescentData f hf E F)
  let DA : ModuleCat A := (AffineCechModuleDescentData.evaluation f).obj D
  let EA : ModuleCat A := (AffineCechModuleDescentData.evaluation f).obj E
  let FA : ModuleCat A := (AffineCechModuleDescentData.evaluation f).obj F
  let eEF : EF ≅ ModuleCat.of A (TensorProduct A EA FA) :=
    affineCechSelectedTensorDescentDataCoverIso f hf E F
  exact affineCechSelectedTensorDescentDataCoverIso f hf D
      (affineCechSelectedTensorDescentData f hf E F) ≪≫
    (TensorProduct.congr
      (LinearEquiv.refl A DA) eEF.toLinearEquiv).toModuleIso

set_option maxHeartbeats 1600000 in
-- Nested tensor induction is needed to normalize all scalar-extension generators.
set_option linter.style.haveILetI false in
theorem affineCechSelectedTensorAssociatorIso_cover
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D E F : AffineCechModuleDescentData f) :
    (affineCechSelectedTensorAssociatorIso f hf D E F).hom.hom PUnit.unit ≫
        (affineCechSelectedTensorRightAssociatedCoverIso f hf D E F).hom =
      (affineCechSelectedTensorLeftAssociatedCoverIso f hf D E F).hom ≫
        ModuleCat.ofHom
          (TensorProduct.assoc A
            ((AffineCechModuleDescentData.evaluation f).obj D)
            ((AffineCechModuleDescentData.evaluation f).obj E)
            ((AffineCechModuleDescentData.evaluation f).obj F)).toLinearMap := by
  letI : Algebra R A := f.hom.toAlgebra
  let AR := (ModuleCat.restrictScalars f.hom).obj (ModuleCat.of A A)
  letI : Module R AR := AR.isModule
  letI : IsScalarTower R A AR :=
    IsScalarTower.of_algebraMap_smul (by intro r x; rfl)
  let DE := affineCechSelectedTensorDescentData f hf D E
  let EF := affineCechSelectedTensorDescentData f hf E F
  let MDE := affineCechDescendedModule f hf DE
  let MEF := affineCechDescendedModule f hf EF
  let MF := affineCechDescendedModule f hf F
  let DA : ModuleCat A := (AffineCechModuleDescentData.evaluation f).obj D
  let EA : ModuleCat A := (AffineCechModuleDescentData.evaluation f).obj E
  let FA : ModuleCat A := (AffineCechModuleDescentData.evaluation f).obj F
  let bDE := affineCechDescendedModuleBaseChangeIso f hf DE
  let bEF := affineCechDescendedModuleBaseChangeIso f hf EF
  let eDE := affineCechSelectedTensorDescendedIso f hf D E
  let eEF := affineCechSelectedTensorDescendedIso f hf E F
  let tDE := affineCechSelectedTensorDescentDataCoverIso f hf D E
  let tEF := affineCechSelectedTensorDescentDataCoverIso f hf E F
  let L : TensorProduct R A (TensorProduct R MDE MF) →ₗ[A]
      TensorProduct A DA (TensorProduct A EA FA) :=
    ModuleCat.Hom.hom
      ((affineCechSelectedTensorAssociatorIso f hf D E F).hom.hom PUnit.unit ≫
        (affineCechSelectedTensorRightAssociatedCoverIso f hf D E F).hom)
  let K : TensorProduct R A (TensorProduct R MDE MF) →ₗ[A]
      TensorProduct A DA (TensorProduct A EA FA) :=
    ModuleCat.Hom.hom
      ((affineCechSelectedTensorLeftAssociatedCoverIso f hf D E F).hom ≫
        ModuleCat.ofHom
          (TensorProduct.assoc A DA EA FA).toLinearMap)
  apply ModuleCat.hom_ext
  change L = K
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a z =>
      induction z using TensorProduct.induction_on with
      | zero => simp only [TensorProduct.tmul_zero, map_zero]
      | tmul m n =>
          rw [← eDE.hom_inv_id_apply m]
          generalize eDE.hom m = z
          induction z using TensorProduct.induction_on with
          | zero =>
              simp only [TensorProduct.zero_tmul, TensorProduct.tmul_zero,
                map_zero]
          | tmul p q =>
              have hbase :
                  (ModuleCat.extendScalars f.hom).map
                      (affineCechSelectedTensorAssociatorBaseIso
                        f hf D E F).hom
                      (a ⊗ₜ[R] (eDE.inv (p ⊗ₜ[R] q) ⊗ₜ[R] n)) =
                    a ⊗ₜ[R] (p ⊗ₜ[R] eEF.inv (q ⊗ₜ[R] n)) := by
                rw [affineCechSelectedTensorAssociatorBaseIso_baseChange_tmul]
                apply congrArg (fun z =>
                  (show
                    ((ModuleCat.restrictScalars f.hom).obj
                      (ModuleCat.of A A) : Type u) from a) ⊗ₜ[R] z)
                simp only [affineCechSelectedTensorAssociatorBaseIso]
                change
                  ((TensorProduct.congr eDE.toLinearEquiv
                      (LinearEquiv.refl R _)).trans
                    ((TensorProduct.assoc R _ _ _).trans
                      (TensorProduct.congr
                        (LinearEquiv.refl R _)
                        eEF.symm.toLinearEquiv)))
                    (eDE.inv (p ⊗ₜ[R] q) ⊗ₜ[R] n) =
                      p ⊗ₜ[R] eEF.inv (q ⊗ₜ[R] n)
                rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply]
                rw [TensorProduct.congr_tmul]
                have hDEcancel :
                    eDE.toLinearEquiv (eDE.inv (p ⊗ₜ[R] q)) =
                      p ⊗ₜ[R] q := by
                  exact eDE.inv_hom_id_apply _
                rw [hDEcancel, LinearEquiv.refl_apply]
                rw [TensorProduct.assoc_tmul]
                rw [TensorProduct.congr_tmul]
                rfl
              dsimp [L, K]
              have hright := congrArg
                (ModuleCat.Hom.hom
                  (affineCechSelectedTensorRightAssociatedCoverIso
                    f hf D E F).hom) hbase
              let oneAR : AR := show AR from (1 : A)
              let aAR : AR := show AR from a
              let qnA :
                  (ModuleCat.extendScalars f.hom).obj
                    (ModuleCat.of R
                      (TensorProduct R
                        (affineCechDescendedModule f hf E)
                        (affineCechDescendedModule f hf F))) :=
                oneAR ⊗ₜ[R] (q ⊗ₜ[R] n)
              let pqA :
                  (ModuleCat.extendScalars f.hom).obj
                    (ModuleCat.of R
                      (TensorProduct R
                        (affineCechDescendedModule f hf D)
                        (affineCechDescendedModule f hf E))) :=
                aAR ⊗ₜ[R] (p ⊗ₜ[R] q)
              let dp : DA :=
                show (AffineCechModuleDescentData.evaluation f).obj D from
                  ModuleCat.Hom.hom
                    (affineCechDescendedModuleBaseChangeIso f hf D).hom
                    (a ⊗ₜ[R] p)
              let eq : EA :=
                show (AffineCechModuleDescentData.evaluation f).obj E from
                  ModuleCat.Hom.hom
                    (affineCechDescendedModuleBaseChangeIso f hf E).hom
                    ((1 : A) ⊗ₜ[R] q)
              let fn : FA :=
                show (AffineCechModuleDescentData.evaluation f).obj F from
                  ModuleCat.Hom.hom
                    (affineCechDescendedModuleBaseChangeIso f hf F).hom
                    ((1 : A) ⊗ₜ[R] n)
              calc
                _ = _ := hright
                _ = _ := by
                  rw [show
                    (affineCechSelectedTensorRightAssociatedCoverIso
                      f hf D E F).hom =
                        (affineCechDescendedTensorBaseChangeIso
                          f hf D EF).hom ≫
                        (TensorProduct.congr
                          (LinearEquiv.refl A DA)
                          (affineCechDescendedTensorBaseChangeIso
                            f hf E F).toLinearEquiv).toModuleIso.hom from rfl]
                  rw [show
                    (affineCechSelectedTensorLeftAssociatedCoverIso
                      f hf D E F).hom =
                        (affineCechDescendedTensorBaseChangeIso
                          f hf DE F).hom ≫
                        (TensorProduct.congr
                          (affineCechDescendedTensorBaseChangeIso
                            f hf D E).toLinearEquiv
                          (LinearEquiv.refl A FA)).toModuleIso.hom from rfl]
                  change
                    (TensorProduct.congr
                      (LinearEquiv.refl A DA)
                      (affineCechDescendedTensorBaseChangeIso
                        f hf E F).toLinearEquiv)
                      (ModuleCat.Hom.hom
                        (affineCechDescendedTensorBaseChangeIso
                          f hf D EF).hom
                        (a ⊗ₜ[R]
                          (p ⊗ₜ[R] eEF.inv (q ⊗ₜ[R] n)))) =
                    (TensorProduct.assoc A DA EA FA)
                      ((TensorProduct.congr
                        (affineCechDescendedTensorBaseChangeIso
                          f hf D E).toLinearEquiv
                        (LinearEquiv.refl A FA))
                        (ModuleCat.Hom.hom
                          (affineCechDescendedTensorBaseChangeIso
                            f hf DE F).hom
                          (a ⊗ₜ[R]
                            (eDE.inv (p ⊗ₜ[R] q) ⊗ₜ[R] n))))
                  rw [affineCechDescendedTensorBaseChangeIso_hom_tmul
                    f hf D EF]
                  rw [affineCechSelectedTensorDescendedIso_baseChange_inv_tmul
                    f hf E F]
                  change
                    (TensorProduct.congr
                      (LinearEquiv.refl A DA)
                      (affineCechDescendedTensorBaseChangeIso
                        f hf E F).toLinearEquiv)
                      (dp ⊗ₜ[A] qnA) =
                    (TensorProduct.assoc A DA EA FA)
                      ((TensorProduct.congr
                        (affineCechDescendedTensorBaseChangeIso
                          f hf D E).toLinearEquiv
                        (LinearEquiv.refl A FA))
                        (ModuleCat.Hom.hom
                          (affineCechDescendedTensorBaseChangeIso
                            f hf DE F).hom
                          (a ⊗ₜ[R]
                            (eDE.inv (p ⊗ₜ[R] q) ⊗ₜ[R] n))))
                  rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply]
                  have hEF :
                      (affineCechDescendedTensorBaseChangeIso
                        f hf E F).toLinearEquiv qnA =
                        eq ⊗ₜ[A] fn := by
                    change
                      ModuleCat.Hom.hom
                          (affineCechDescendedTensorBaseChangeIso
                            f hf E F).hom
                          ((1 : A) ⊗ₜ[R] (q ⊗ₜ[R] n)) =
                        eq ⊗ₜ[A] fn
                    exact affineCechDescendedTensorBaseChangeIso_hom_tmul
                      f hf E F (1 : A) q n
                  rw [hEF]
                  rw [affineCechDescendedTensorBaseChangeIso_hom_tmul
                    f hf DE F]
                  rw [affineCechSelectedTensorDescendedIso_baseChange_inv_tmul
                    f hf D E]
                  change
                    dp ⊗ₜ[A] (eq ⊗ₜ[A] fn) =
                      (TensorProduct.assoc A DA EA FA)
                        ((TensorProduct.congr
                          (affineCechDescendedTensorBaseChangeIso
                            f hf D E).toLinearEquiv
                          (LinearEquiv.refl A FA))
                          (pqA ⊗ₜ[A] fn))
                  rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply]
                  have hDE :
                      (affineCechDescendedTensorBaseChangeIso
                        f hf D E).toLinearEquiv pqA =
                        dp ⊗ₜ[A] eq := by
                    change
                      ModuleCat.Hom.hom
                          (affineCechDescendedTensorBaseChangeIso
                            f hf D E).hom
                          (a ⊗ₜ[R] (p ⊗ₜ[R] q)) =
                        dp ⊗ₜ[A] eq
                    exact affineCechDescendedTensorBaseChangeIso_hom_tmul
                      f hf D E a p q
                  rw [hDE]
                  rw [TensorProduct.assoc_tmul]
          | add x y hx hy =>
              simp only [TensorProduct.add_tmul, TensorProduct.tmul_add,
                map_add, hx, hy]
      | add x y hx hy =>
          simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The selected tensor unit is the comparison datum associated to the base
ring regarded as a module over itself. -/
noncomputable def affineCechSelectedTensorUnitDescentData
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    AffineCechModuleDescentData f :=
  (affineCechModuleDescentComparison f).obj (ModuleCat.of R R)

/-- Descending the selected tensor unit recovers the base ring as its regular
module. -/
noncomputable def affineCechSelectedTensorUnitDescendedIso
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat) :
    affineCechDescendedModule f hf
        (affineCechSelectedTensorUnitDescentData f) ≅
      ModuleCat.of R R :=
  affineCechDescendedComparisonObjIso f hf _

/-- The cover object of the selected tensor unit is the cover ring as its
regular module. -/
noncomputable def affineCechSelectedTensorUnitCoverIso
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    (affineCechSelectedTensorUnitDescentData f).obj PUnit.unit ≅
      ModuleCat.of A A := by
  letI : Algebra R A := f.hom.toAlgebra
  change ModuleCat.of A (TensorProduct R A R) ≅ ModuleCat.of A A
  exact (TensorProduct.AlgebraTensorModule.rid R A A).toModuleIso

/-- The base-ring left unitor for the selected tensor datum.  It first
identifies the descended selected unit with the regular base module. -/
noncomputable def affineCechSelectedTensorLeftUnitorBaseIso
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D : AffineCechModuleDescentData f) :
    ModuleCat.of R
        (TensorProduct R
          (affineCechDescendedModule f hf
            (affineCechSelectedTensorUnitDescentData f))
          (affineCechDescendedModule f hf D)) ≅
      affineCechDescendedModule f hf D :=
  ((TensorProduct.congr
      (affineCechSelectedTensorUnitDescendedIso f hf).toLinearEquiv
      (LinearEquiv.refl R
        (affineCechDescendedModule f hf D))).trans
    (TensorProduct.lid R
      (affineCechDescendedModule f hf D))).toModuleIso

/-- The base-ring right unitor for the selected tensor datum. -/
noncomputable def affineCechSelectedTensorRightUnitorBaseIso
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D : AffineCechModuleDescentData f) :
    ModuleCat.of R
        (TensorProduct R
          (affineCechDescendedModule f hf D)
          (affineCechDescendedModule f hf
            (affineCechSelectedTensorUnitDescentData f))) ≅
      affineCechDescendedModule f hf D :=
  ((TensorProduct.congr
      (LinearEquiv.refl R
        (affineCechDescendedModule f hf D))
      (affineCechSelectedTensorUnitDescendedIso f hf).toLinearEquiv).trans
    (TensorProduct.rid R
      (affineCechDescendedModule f hf D))).toModuleIso

/-- The selected-datum left unitor. -/
noncomputable def affineCechSelectedTensorLeftUnitorIso
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D : AffineCechModuleDescentData f) :
    affineCechSelectedTensorDescentData f hf
        (affineCechSelectedTensorUnitDescentData f) D ≅ D :=
  (affineCechModuleDescentComparison f).mapIso
      (affineCechSelectedTensorLeftUnitorBaseIso f hf D) ≪≫
    affineCechDescendedModuleIso f hf D

/-- The selected-datum right unitor. -/
noncomputable def affineCechSelectedTensorRightUnitorIso
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D : AffineCechModuleDescentData f) :
    affineCechSelectedTensorDescentData f hf D
        (affineCechSelectedTensorUnitDescentData f) ≅ D :=
  (affineCechModuleDescentComparison f).mapIso
      (affineCechSelectedTensorRightUnitorBaseIso f hf D) ≪≫
    affineCechDescendedModuleIso f hf D

/-- The cover of a selected tensor with the unit on the left, identified with
the standard left-unit tensor product. -/
noncomputable def affineCechSelectedTensorLeftUnitorCoverIso
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D : AffineCechModuleDescentData f) :
    (affineCechSelectedTensorDescentData f hf
        (affineCechSelectedTensorUnitDescentData f) D).obj PUnit.unit ≅
      ModuleCat.of A
        (TensorProduct A A
          ((AffineCechModuleDescentData.evaluation f).obj D)) := by
  let UA : ModuleCat A :=
    (AffineCechModuleDescentData.evaluation f).obj
      (affineCechSelectedTensorUnitDescentData f)
  let DA : ModuleCat A :=
    (AffineCechModuleDescentData.evaluation f).obj D
  let eU : UA ≅ ModuleCat.of A A :=
    affineCechSelectedTensorUnitCoverIso f
  exact affineCechSelectedTensorDescentDataCoverIso f hf
      (affineCechSelectedTensorUnitDescentData f) D ≪≫
    (TensorProduct.congr eU.toLinearEquiv
      (LinearEquiv.refl A DA)).toModuleIso

/-- The cover of a selected tensor with the unit on the right, identified with
the standard right-unit tensor product. -/
noncomputable def affineCechSelectedTensorRightUnitorCoverIso
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D : AffineCechModuleDescentData f) :
    (affineCechSelectedTensorDescentData f hf D
        (affineCechSelectedTensorUnitDescentData f)).obj PUnit.unit ≅
      ModuleCat.of A
        (TensorProduct A
          ((AffineCechModuleDescentData.evaluation f).obj D) A) := by
  let UA : ModuleCat A :=
    (AffineCechModuleDescentData.evaluation f).obj
      (affineCechSelectedTensorUnitDescentData f)
  let DA : ModuleCat A :=
    (AffineCechModuleDescentData.evaluation f).obj D
  let eU : UA ≅ ModuleCat.of A A :=
    affineCechSelectedTensorUnitCoverIso f
  exact affineCechSelectedTensorDescentDataCoverIso f hf D
      (affineCechSelectedTensorUnitDescentData f) ≪≫
    (TensorProduct.congr
      (LinearEquiv.refl A DA) eU.toLinearEquiv).toModuleIso

set_option maxHeartbeats 1600000 in
-- The cover calculation normalizes nested scalar-extension tensor generators.
set_option linter.style.haveILetI false in
/-- Under the selected cover comparison, the selected left unitor is exactly
the standard tensor-product left unitor. -/
theorem affineCechSelectedTensorLeftUnitorIso_cover
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D : AffineCechModuleDescentData f) :
    (affineCechSelectedTensorLeftUnitorIso f hf D).hom.hom PUnit.unit =
      (affineCechSelectedTensorLeftUnitorCoverIso f hf D).hom ≫
        ModuleCat.ofHom
          (TensorProduct.lid A
            ((AffineCechModuleDescentData.evaluation f).obj D)).toLinearMap := by
  letI : Algebra R A := f.hom.toAlgebra
  let U := affineCechDescendedModule f hf
    (affineCechSelectedTensorUnitDescentData f)
  let M := affineCechDescendedModule f hf D
  let UA : ModuleCat A :=
    (AffineCechModuleDescentData.evaluation f).obj
      (affineCechSelectedTensorUnitDescentData f)
  let DA : ModuleCat A :=
    (AffineCechModuleDescentData.evaluation f).obj D
  let eU := affineCechSelectedTensorUnitDescendedIso f hf
  let eUA : UA ≅ ModuleCat.of A A :=
    affineCechSelectedTensorUnitCoverIso f
  let bU := affineCechDescendedModuleBaseChangeIso f hf
    (affineCechSelectedTensorUnitDescentData f)
  let bD := affineCechDescendedModuleBaseChangeIso f hf D
  let L : TensorProduct R A (TensorProduct R U M) →ₗ[A] DA :=
    ModuleCat.Hom.hom
      ((affineCechSelectedTensorLeftUnitorIso f hf D).hom.hom PUnit.unit)
  let K : TensorProduct R A (TensorProduct R U M) →ₗ[A] DA :=
    ModuleCat.Hom.hom
      ((affineCechSelectedTensorLeftUnitorCoverIso f hf D).hom ≫
        ModuleCat.ofHom (TensorProduct.lid A DA).toLinearMap)
  apply ModuleCat.hom_ext
  change L = K
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a z =>
      induction z using TensorProduct.induction_on with
      | zero => simp only [TensorProduct.tmul_zero, map_zero]
      | tmul u m =>
          dsimp [L, K]
          rw [show
            (affineCechSelectedTensorLeftUnitorIso f hf D).hom.hom PUnit.unit =
              (ModuleCat.extendScalars f.hom).map
                  (affineCechSelectedTensorLeftUnitorBaseIso f hf D).hom ≫
                bD.hom from rfl]
          rw [show
            (affineCechSelectedTensorLeftUnitorCoverIso f hf D).hom =
              (affineCechDescendedTensorBaseChangeIso f hf
                  (affineCechSelectedTensorUnitDescentData f) D).hom ≫
                (TensorProduct.congr eUA.toLinearEquiv
                  (LinearEquiv.refl A DA)).toModuleIso.hom from rfl]
          change
            ModuleCat.Hom.hom bD.hom
                (ModuleCat.Hom.hom
                  ((ModuleCat.extendScalars f.hom).map
                    (affineCechSelectedTensorLeftUnitorBaseIso f hf D).hom)
                  (a ⊗ₜ[R] (u ⊗ₜ[R] m))) =
              (TensorProduct.lid A DA)
                ((TensorProduct.congr eUA.toLinearEquiv
                  (LinearEquiv.refl A DA))
                  (ModuleCat.Hom.hom
                    (affineCechDescendedTensorBaseChangeIso f hf
                      (affineCechSelectedTensorUnitDescentData f) D).hom
                    (a ⊗ₜ[R] (u ⊗ₜ[R] m))))
          rw [affineCechModuleHom_baseChange_tmul]
          change
            ModuleCat.Hom.hom bD.hom
                (a ⊗ₜ[R]
                  (affineCechSelectedTensorLeftUnitorBaseIso f hf D).hom
                    (u ⊗ₜ[R] m)) = _
          set_option linter.unusedSimpArgs false in
            simp only [affineCechSelectedTensorLeftUnitorBaseIso,
              TensorProduct.congr_tmul, LinearEquiv.refl_apply,
              TensorProduct.lid_tmul]
          rw [affineCechDescendedTensorBaseChangeIso_hom_tmul]
          rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply,
            TensorProduct.lid_tmul]
          have hmap :=
            affineCechDescendedComparisonObjIso_hom_baseChange f hf
              (ModuleCat.of R R)
          have happ := congrArg
            (fun q => ModuleCat.Hom.hom q (a ⊗ₜ[R] u)) hmap
          have heUA :
              (show A from ModuleCat.Hom.hom eUA.hom
                (ModuleCat.Hom.hom bU.hom (a ⊗ₜ[R] u))) =
                (TensorProduct.AlgebraTensorModule.rid R A A)
                  (ModuleCat.Hom.hom
                    ((ModuleCat.extendScalars f.hom).map eU.hom)
                    (a ⊗ₜ[R] u)) := by
            change
              (TensorProduct.AlgebraTensorModule.rid R A A)
                  (ModuleCat.Hom.hom bU.hom (a ⊗ₜ[R] u)) =
                (TensorProduct.AlgebraTensorModule.rid R A A)
                  (ModuleCat.Hom.hom
                    ((ModuleCat.extendScalars f.hom).map eU.hom)
                    (a ⊗ₜ[R] u))
            exact congrArg
              (TensorProduct.AlgebraTensorModule.rid R A A) happ.symm
          change
            ModuleCat.Hom.hom bD.hom
                (a ⊗ₜ[R] ((show R from eU.hom u) • m)) =
              (show A from ModuleCat.Hom.hom eUA.hom
                  (ModuleCat.Hom.hom bU.hom (a ⊗ₜ[R] u))) •
                (show DA from
                  ModuleCat.Hom.hom bD.hom ((1 : A) ⊗ₜ[R] m))
          rw [heUA]
          rw [affineCechModuleHom_baseChange_tmul]
          rw [TensorProduct.AlgebraTensorModule.rid_tmul]
          let q : TensorProduct R A M →ₗ[A] DA :=
            ModuleCat.Hom.hom bD.hom
          change
            q (a ⊗ₜ[R] ((show R from eU.hom u) • m)) =
              ((show R from eU.hom u) • a) •
                q ((1 : A) ⊗ₜ[R] m)
          rw [TensorProduct.tmul_smul (R := R) (R' := R)
            (show R from eU.hom u) a m]
          have htensor :
              ((show R from eU.hom u) • a) ⊗ₜ[R] m =
                ((show R from eU.hom u) • a) •
                  ((1 : A) ⊗ₜ[R] m) := by
            simpa only [smul_eq_mul, mul_one] using
              (TensorProduct.smul_tmul' (R := R) (R' := A)
                ((show R from eU.hom u) • a) (1 : A) m).symm
          calc
            q (((show R from eU.hom u) • a) ⊗ₜ[R] m) =
                q (((show R from eU.hom u) • a) •
                  ((1 : A) ⊗ₜ[R] m)) :=
              congrArg q htensor
            _ = _ := q.map_smul _ _
      | add x y hx hy =>
          simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

set_option maxHeartbeats 1600000 in
-- The cover calculation normalizes nested scalar-extension tensor generators.
set_option linter.style.haveILetI false in
/-- Under the selected cover comparison, the selected right unitor is exactly
the standard tensor-product right unitor. -/
theorem affineCechSelectedTensorRightUnitorIso_cover
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D : AffineCechModuleDescentData f) :
    (affineCechSelectedTensorRightUnitorIso f hf D).hom.hom PUnit.unit =
      (affineCechSelectedTensorRightUnitorCoverIso f hf D).hom ≫
        ModuleCat.ofHom
          (TensorProduct.rid A
            ((AffineCechModuleDescentData.evaluation f).obj D)).toLinearMap := by
  letI : Algebra R A := f.hom.toAlgebra
  let U := affineCechDescendedModule f hf
    (affineCechSelectedTensorUnitDescentData f)
  let M := affineCechDescendedModule f hf D
  let UA : ModuleCat A :=
    (AffineCechModuleDescentData.evaluation f).obj
      (affineCechSelectedTensorUnitDescentData f)
  let DA : ModuleCat A :=
    (AffineCechModuleDescentData.evaluation f).obj D
  let eU := affineCechSelectedTensorUnitDescendedIso f hf
  let eUA : UA ≅ ModuleCat.of A A :=
    affineCechSelectedTensorUnitCoverIso f
  let bU := affineCechDescendedModuleBaseChangeIso f hf
    (affineCechSelectedTensorUnitDescentData f)
  let bD := affineCechDescendedModuleBaseChangeIso f hf D
  let L : TensorProduct R A (TensorProduct R M U) →ₗ[A] DA :=
    ModuleCat.Hom.hom
      ((affineCechSelectedTensorRightUnitorIso f hf D).hom.hom PUnit.unit)
  let K : TensorProduct R A (TensorProduct R M U) →ₗ[A] DA :=
    ModuleCat.Hom.hom
      ((affineCechSelectedTensorRightUnitorCoverIso f hf D).hom ≫
        ModuleCat.ofHom (TensorProduct.rid A DA).toLinearMap)
  apply ModuleCat.hom_ext
  change L = K
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a z =>
      induction z using TensorProduct.induction_on with
      | zero => simp only [TensorProduct.tmul_zero, map_zero]
      | tmul m u =>
          dsimp [L, K]
          rw [show
            (affineCechSelectedTensorRightUnitorIso f hf D).hom.hom PUnit.unit =
              (ModuleCat.extendScalars f.hom).map
                  (affineCechSelectedTensorRightUnitorBaseIso f hf D).hom ≫
                bD.hom from rfl]
          rw [show
            (affineCechSelectedTensorRightUnitorCoverIso f hf D).hom =
              (affineCechDescendedTensorBaseChangeIso f hf D
                  (affineCechSelectedTensorUnitDescentData f)).hom ≫
                (TensorProduct.congr (LinearEquiv.refl A DA)
                  eUA.toLinearEquiv).toModuleIso.hom from rfl]
          change
            ModuleCat.Hom.hom bD.hom
                (ModuleCat.Hom.hom
                  ((ModuleCat.extendScalars f.hom).map
                    (affineCechSelectedTensorRightUnitorBaseIso f hf D).hom)
                  (a ⊗ₜ[R] (m ⊗ₜ[R] u))) =
              (TensorProduct.rid A DA)
                ((TensorProduct.congr (LinearEquiv.refl A DA)
                  eUA.toLinearEquiv)
                  (ModuleCat.Hom.hom
                    (affineCechDescendedTensorBaseChangeIso f hf D
                      (affineCechSelectedTensorUnitDescentData f)).hom
                    (a ⊗ₜ[R] (m ⊗ₜ[R] u))))
          rw [affineCechModuleHom_baseChange_tmul]
          change
            ModuleCat.Hom.hom bD.hom
                (a ⊗ₜ[R]
                  (affineCechSelectedTensorRightUnitorBaseIso f hf D).hom
                    (m ⊗ₜ[R] u)) = _
          set_option linter.unusedSimpArgs false in
            simp only [affineCechSelectedTensorRightUnitorBaseIso,
              TensorProduct.congr_tmul, LinearEquiv.refl_apply,
              TensorProduct.rid_tmul]
          rw [affineCechDescendedTensorBaseChangeIso_hom_tmul]
          rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply,
            TensorProduct.rid_tmul]
          have hmap :=
            affineCechDescendedComparisonObjIso_hom_baseChange f hf
              (ModuleCat.of R R)
          have happ := congrArg
            (fun q => ModuleCat.Hom.hom q ((1 : A) ⊗ₜ[R] u)) hmap
          have heUA :
              (show A from ModuleCat.Hom.hom eUA.hom
                (ModuleCat.Hom.hom bU.hom ((1 : A) ⊗ₜ[R] u))) =
                (TensorProduct.AlgebraTensorModule.rid R A A)
                  (ModuleCat.Hom.hom
                    ((ModuleCat.extendScalars f.hom).map eU.hom)
                    ((1 : A) ⊗ₜ[R] u)) := by
            change
              (TensorProduct.AlgebraTensorModule.rid R A A)
                  (ModuleCat.Hom.hom bU.hom ((1 : A) ⊗ₜ[R] u)) =
                (TensorProduct.AlgebraTensorModule.rid R A A)
                  (ModuleCat.Hom.hom
                    ((ModuleCat.extendScalars f.hom).map eU.hom)
                    ((1 : A) ⊗ₜ[R] u))
            exact congrArg
              (TensorProduct.AlgebraTensorModule.rid R A A) happ.symm
          change
            ModuleCat.Hom.hom bD.hom
                (a ⊗ₜ[R] ((show R from eU.hom u) • m)) =
              (show A from ModuleCat.Hom.hom eUA.hom
                  (ModuleCat.Hom.hom bU.hom ((1 : A) ⊗ₜ[R] u))) •
                (show DA from ModuleCat.Hom.hom bD.hom (a ⊗ₜ[R] m))
          rw [heUA]
          rw [affineCechModuleHom_baseChange_tmul]
          rw [TensorProduct.AlgebraTensorModule.rid_tmul]
          let q : TensorProduct R A M →ₗ[A] DA :=
            ModuleCat.Hom.hom bD.hom
          change
            q (a ⊗ₜ[R] ((show R from eU.hom u) • m)) =
              ((show R from eU.hom u) • (1 : A)) •
                q (a ⊗ₜ[R] m)
          rw [TensorProduct.tmul_smul (R := R) (R' := R)
            (show R from eU.hom u) a m]
          have htensor :
              ((show R from eU.hom u) • a) ⊗ₜ[R] m =
                ((show R from eU.hom u) • (1 : A)) •
                  (a ⊗ₜ[R] m) := by
            simpa only [smul_eq_mul, Algebra.smul_def, mul_one] using
              (TensorProduct.smul_tmul' (R := R) (R' := A)
                ((show R from eU.hom u) • (1 : A)) a m).symm
          calc
            q (((show R from eU.hom u) • a) ⊗ₜ[R] m) =
                q (((show R from eU.hom u) • (1 : A)) •
                  (a ⊗ₜ[R] m)) :=
              congrArg q htensor
            _ = _ := q.map_smul _ _
      | add x y hx hy =>
          simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The selected left-unitor base maps are natural in the supplied descent
datum. -/
theorem affineCechSelectedTensorLeftUnitorBaseIso_natural
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    {D E : AffineCechModuleDescentData f} (g : D ⟶ E) :
    affineCechDescendedTensorMap f hf
          (𝟙 (affineCechSelectedTensorUnitDescentData f)) g ≫
        (affineCechSelectedTensorLeftUnitorBaseIso f hf E).hom =
      (affineCechSelectedTensorLeftUnitorBaseIso f hf D).hom ≫
        affineCechDescendedModuleHom f hf g := by
  let U := affineCechDescendedModule f hf
    (affineCechSelectedTensorUnitDescentData f)
  let M := affineCechDescendedModule f hf D
  let N := affineCechDescendedModule f hf E
  let eU := affineCechSelectedTensorUnitDescendedIso f hf
  let q : M →ₗ[R] N :=
    ModuleCat.Hom.hom (affineCechDescendedModuleHom f hf g)
  let L : TensorProduct R U M →ₗ[R] N :=
    ModuleCat.Hom.hom
      (affineCechDescendedTensorMap f hf
          (𝟙 (affineCechSelectedTensorUnitDescentData f)) g ≫
        (affineCechSelectedTensorLeftUnitorBaseIso f hf E).hom)
  let K : TensorProduct R U M →ₗ[R] N :=
    ModuleCat.Hom.hom
      ((affineCechSelectedTensorLeftUnitorBaseIso f hf D).hom ≫
        affineCechDescendedModuleHom f hf g)
  apply ModuleCat.hom_ext
  change L = K
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul u m =>
      dsimp [L, K]
      change
        ModuleCat.Hom.hom
            (affineCechSelectedTensorLeftUnitorBaseIso f hf E).hom
            (TensorProduct.map
              (ModuleCat.Hom.hom
                (affineCechDescendedModuleHom f hf
                  (𝟙 (affineCechSelectedTensorUnitDescentData f))))
              q (u ⊗ₜ[R] m)) =
          q (ModuleCat.Hom.hom
            (affineCechSelectedTensorLeftUnitorBaseIso f hf D).hom
            (u ⊗ₜ[R] m))
      rw [TensorProduct.map_tmul, affineCechDescendedModuleHom_id]
      change
        (TensorProduct.lid R N)
            ((TensorProduct.congr eU.toLinearEquiv
              (LinearEquiv.refl R N)) (u ⊗ₜ[R] q m)) =
          q ((TensorProduct.lid R M)
            ((TensorProduct.congr eU.toLinearEquiv
              (LinearEquiv.refl R M)) (u ⊗ₜ[R] m)))
      rw [TensorProduct.congr_tmul, TensorProduct.congr_tmul,
        LinearEquiv.refl_apply, LinearEquiv.refl_apply,
        TensorProduct.lid_tmul, TensorProduct.lid_tmul]
      exact (q.map_smul (show R from eU.hom u) m).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The selected right-unitor base maps are natural in the supplied descent
datum. -/
theorem affineCechSelectedTensorRightUnitorBaseIso_natural
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    {D E : AffineCechModuleDescentData f} (g : D ⟶ E) :
    affineCechDescendedTensorMap f hf g
          (𝟙 (affineCechSelectedTensorUnitDescentData f)) ≫
        (affineCechSelectedTensorRightUnitorBaseIso f hf E).hom =
      (affineCechSelectedTensorRightUnitorBaseIso f hf D).hom ≫
        affineCechDescendedModuleHom f hf g := by
  let U := affineCechDescendedModule f hf
    (affineCechSelectedTensorUnitDescentData f)
  let M := affineCechDescendedModule f hf D
  let N := affineCechDescendedModule f hf E
  let eU := affineCechSelectedTensorUnitDescendedIso f hf
  let q : M →ₗ[R] N :=
    ModuleCat.Hom.hom (affineCechDescendedModuleHom f hf g)
  let L : TensorProduct R M U →ₗ[R] N :=
    ModuleCat.Hom.hom
      (affineCechDescendedTensorMap f hf g
          (𝟙 (affineCechSelectedTensorUnitDescentData f)) ≫
        (affineCechSelectedTensorRightUnitorBaseIso f hf E).hom)
  let K : TensorProduct R M U →ₗ[R] N :=
    ModuleCat.Hom.hom
      ((affineCechSelectedTensorRightUnitorBaseIso f hf D).hom ≫
        affineCechDescendedModuleHom f hf g)
  apply ModuleCat.hom_ext
  change L = K
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul m u =>
      dsimp [L, K]
      change
        ModuleCat.Hom.hom
            (affineCechSelectedTensorRightUnitorBaseIso f hf E).hom
            (TensorProduct.map q
              (ModuleCat.Hom.hom
                (affineCechDescendedModuleHom f hf
                  (𝟙 (affineCechSelectedTensorUnitDescentData f))))
              (m ⊗ₜ[R] u)) =
          q (ModuleCat.Hom.hom
            (affineCechSelectedTensorRightUnitorBaseIso f hf D).hom
            (m ⊗ₜ[R] u))
      rw [TensorProduct.map_tmul, affineCechDescendedModuleHom_id]
      change
        (TensorProduct.rid R N)
            ((TensorProduct.congr (LinearEquiv.refl R N)
              eU.toLinearEquiv) (q m ⊗ₜ[R] u)) =
          q ((TensorProduct.rid R M)
            ((TensorProduct.congr (LinearEquiv.refl R M)
              eU.toLinearEquiv) (m ⊗ₜ[R] u)))
      rw [TensorProduct.congr_tmul, TensorProduct.congr_tmul,
        LinearEquiv.refl_apply, LinearEquiv.refl_apply,
        TensorProduct.rid_tmul, TensorProduct.rid_tmul]
      exact (q.map_smul (show R from eU.hom u) m).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The selected-datum left unitors are natural. -/
theorem affineCechSelectedTensorLeftUnitorIso_natural
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    {D E : AffineCechModuleDescentData f} (g : D ⟶ E) :
    affineCechSelectedTensorMap f hf
          (𝟙 (affineCechSelectedTensorUnitDescentData f)) g ≫
        (affineCechSelectedTensorLeftUnitorIso f hf E).hom =
      (affineCechSelectedTensorLeftUnitorIso f hf D).hom ≫ g := by
  let F := affineCechModuleDescentComparison f
  let eD := affineCechDescendedModuleIso f hf D
  let eE := affineCechDescendedModuleIso f hf E
  let t := affineCechDescendedTensorMap f hf
    (𝟙 (affineCechSelectedTensorUnitDescentData f)) g
  let lD := affineCechSelectedTensorLeftUnitorBaseIso f hf D
  let lE := affineCechSelectedTensorLeftUnitorBaseIso f hf E
  have hbase :
      t ≫ lE.hom =
        lD.hom ≫ affineCechDescendedModuleHom f hf g :=
    affineCechSelectedTensorLeftUnitorBaseIso_natural f hf g
  have he :
      F.map (affineCechDescendedModuleHom f hf g) ≫ eE.hom =
        eD.hom ≫ g :=
    (affineCechDescendedModuleComparisonIso f hf).hom.naturality g
  change
    (F.map t ≫ F.map lE.hom) ≫ eE.hom =
      (F.map lD.hom ≫ eD.hom) ≫ g
  rw [← F.map_comp, hbase, F.map_comp, Category.assoc, he]
  simp only [Category.assoc]

/-- The selected-datum right unitors are natural. -/
theorem affineCechSelectedTensorRightUnitorIso_natural
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    {D E : AffineCechModuleDescentData f} (g : D ⟶ E) :
    affineCechSelectedTensorMap f hf g
          (𝟙 (affineCechSelectedTensorUnitDescentData f)) ≫
        (affineCechSelectedTensorRightUnitorIso f hf E).hom =
      (affineCechSelectedTensorRightUnitorIso f hf D).hom ≫ g := by
  let F := affineCechModuleDescentComparison f
  let eD := affineCechDescendedModuleIso f hf D
  let eE := affineCechDescendedModuleIso f hf E
  let t := affineCechDescendedTensorMap f hf g
    (𝟙 (affineCechSelectedTensorUnitDescentData f))
  let rD := affineCechSelectedTensorRightUnitorBaseIso f hf D
  let rE := affineCechSelectedTensorRightUnitorBaseIso f hf E
  have hbase :
      t ≫ rE.hom =
        rD.hom ≫ affineCechDescendedModuleHom f hf g :=
    affineCechSelectedTensorRightUnitorBaseIso_natural f hf g
  have he :
      F.map (affineCechDescendedModuleHom f hf g) ≫ eE.hom =
        eD.hom ≫ g :=
    (affineCechDescendedModuleComparisonIso f hf).hom.naturality g
  change
    (F.map t ≫ F.map rE.hom) ≫ eE.hom =
      (F.map rD.hom ≫ eD.hom) ≫ g
  rw [← F.map_comp, hbase, F.map_comp, Category.assoc, he]
  simp only [Category.assoc]

/-- Tensoring with the selected unit on the left defines an endofunctor. -/
noncomputable def affineCechSelectedTensorLeftUnitFunctor
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat) :
    AffineCechModuleDescentData f ⥤ AffineCechModuleDescentData f where
  obj D := affineCechSelectedTensorDescentData f hf
    (affineCechSelectedTensorUnitDescentData f) D
  map g := affineCechSelectedTensorMap f hf
    (𝟙 (affineCechSelectedTensorUnitDescentData f)) g
  map_id D := affineCechSelectedTensorMap_id f hf
    (affineCechSelectedTensorUnitDescentData f) D
  map_comp g h := by
    simpa using affineCechSelectedTensorMap_comp f hf
      (𝟙 (affineCechSelectedTensorUnitDescentData f))
      (𝟙 (affineCechSelectedTensorUnitDescentData f)) g h

/-- Tensoring with the selected unit on the right defines an endofunctor. -/
noncomputable def affineCechSelectedTensorRightUnitFunctor
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat) :
    AffineCechModuleDescentData f ⥤ AffineCechModuleDescentData f where
  obj D := affineCechSelectedTensorDescentData f hf D
    (affineCechSelectedTensorUnitDescentData f)
  map g := affineCechSelectedTensorMap f hf g
    (𝟙 (affineCechSelectedTensorUnitDescentData f))
  map_id D := affineCechSelectedTensorMap_id f hf D
    (affineCechSelectedTensorUnitDescentData f)
  map_comp g h := by
    simpa using affineCechSelectedTensorMap_comp f hf g h
      (𝟙 (affineCechSelectedTensorUnitDescentData f))
      (𝟙 (affineCechSelectedTensorUnitDescentData f))

/-- The selected left unitors form a natural isomorphism to the identity
functor. -/
noncomputable def affineCechSelectedTensorLeftUnitorNatIso
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat) :
    affineCechSelectedTensorLeftUnitFunctor f hf ≅
      𝟭 (AffineCechModuleDescentData f) :=
  NatIso.ofComponents
    (fun D => affineCechSelectedTensorLeftUnitorIso f hf D)
    (by
      intro D E g
      exact affineCechSelectedTensorLeftUnitorIso_natural f hf g)

/-- The selected right unitors form a natural isomorphism to the identity
functor. -/
noncomputable def affineCechSelectedTensorRightUnitorNatIso
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat) :
    affineCechSelectedTensorRightUnitFunctor f hf ≅
      𝟭 (AffineCechModuleDescentData f) :=
  NatIso.ofComponents
    (fun D => affineCechSelectedTensorRightUnitorIso f hf D)
    (by
      intro D E g
      exact affineCechSelectedTensorRightUnitorIso_natural f hf g)

/-- The standard base-ring tensor swap between the selected descended
modules. -/
noncomputable def affineCechSelectedTensorSymmetryBaseIso
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D E : AffineCechModuleDescentData f) :
    ModuleCat.of R
        (TensorProduct R
          (affineCechDescendedModule f hf D)
          (affineCechDescendedModule f hf E)) ≅
      ModuleCat.of R
        (TensorProduct R
          (affineCechDescendedModule f hf E)
          (affineCechDescendedModule f hf D)) :=
  (TensorProduct.comm R
    (affineCechDescendedModule f hf D)
    (affineCechDescendedModule f hf E)).toModuleIso

/-- The selected-datum tensor symmetry obtained by transporting the standard
base-ring tensor swap through affine Čech comparison. -/
noncomputable def affineCechSelectedTensorSymmetryIso
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D E : AffineCechModuleDescentData f) :
    affineCechSelectedTensorDescentData f hf D E ≅
      affineCechSelectedTensorDescentData f hf E D :=
  (affineCechModuleDescentComparison f).mapIso
    (affineCechSelectedTensorSymmetryBaseIso f hf D E)

/-- The standard tensor swap between the two supplied cover modules. -/
noncomputable def affineCechSelectedTensorSymmetryCoverIso
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (D E : AffineCechModuleDescentData f) :
    ModuleCat.of A
        (TensorProduct A
          ((AffineCechModuleDescentData.evaluation f).obj D)
          ((AffineCechModuleDescentData.evaluation f).obj E)) ≅
      ModuleCat.of A
        (TensorProduct A
          ((AffineCechModuleDescentData.evaluation f).obj E)
          ((AffineCechModuleDescentData.evaluation f).obj D)) :=
  (TensorProduct.comm A
    ((AffineCechModuleDescentData.evaluation f).obj D)
    ((AffineCechModuleDescentData.evaluation f).obj E)).toModuleIso

set_option maxHeartbeats 1600000 in
-- Two tensor inductions and scalar balancing identify the transported swap.
set_option linter.style.haveILetI false in
/-- Under the selected cover comparisons, the descended tensor symmetry is
exactly the standard cover-module tensor swap. -/
theorem affineCechSelectedTensorSymmetryIso_cover
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D E : AffineCechModuleDescentData f) :
    (affineCechSelectedTensorSymmetryIso f hf D E).hom.hom PUnit.unit ≫
        (affineCechSelectedTensorDescentDataCoverIso f hf E D).hom =
      (affineCechSelectedTensorDescentDataCoverIso f hf D E).hom ≫
        (affineCechSelectedTensorSymmetryCoverIso f D E).hom := by
  letI : Algebra R A := f.hom.toAlgebra
  let MD := affineCechDescendedModule f hf D
  let ME := affineCechDescendedModule f hf E
  let DA : ModuleCat A := (AffineCechModuleDescentData.evaluation f).obj D
  let EA : ModuleCat A := (AffineCechModuleDescentData.evaluation f).obj E
  let bD := affineCechDescendedModuleBaseChangeIso f hf D
  let bE := affineCechDescendedModuleBaseChangeIso f hf E
  let bDE := affineCechDescendedTensorBaseChangeIso f hf D E
  let bED := affineCechDescendedTensorBaseChangeIso f hf E D
  let L : TensorProduct R A (TensorProduct R MD ME) →ₗ[A]
      TensorProduct A EA DA :=
    ModuleCat.Hom.hom
      ((affineCechSelectedTensorSymmetryIso f hf D E).hom.hom PUnit.unit ≫
        (affineCechSelectedTensorDescentDataCoverIso f hf E D).hom)
  let K : TensorProduct R A (TensorProduct R MD ME) →ₗ[A]
      TensorProduct A EA DA :=
    ModuleCat.Hom.hom
      ((affineCechSelectedTensorDescentDataCoverIso f hf D E).hom ≫
        (affineCechSelectedTensorSymmetryCoverIso f D E).hom)
  apply ModuleCat.hom_ext
  change L = K
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a z =>
      induction z using TensorProduct.induction_on with
      | zero => simp only [TensorProduct.tmul_zero, map_zero]
      | tmul m n =>
          dsimp [L, K]
          rw [show
            (affineCechSelectedTensorSymmetryIso f hf D E).hom.hom
                PUnit.unit =
              (ModuleCat.extendScalars f.hom).map
                (affineCechSelectedTensorSymmetryBaseIso f hf D E).hom
            from rfl]
          change
            ModuleCat.Hom.hom bED.hom
                (ModuleCat.Hom.hom
                  ((ModuleCat.extendScalars f.hom).map
                    (affineCechSelectedTensorSymmetryBaseIso f hf D E).hom)
                  (a ⊗ₜ[R] (m ⊗ₜ[R] n))) =
              (TensorProduct.comm A DA EA)
                (ModuleCat.Hom.hom bDE.hom
                  (a ⊗ₜ[R] (m ⊗ₜ[R] n)))
          rw [affineCechModuleHom_baseChange_tmul]
          change
            ModuleCat.Hom.hom bED.hom (a ⊗ₜ[R] (n ⊗ₜ[R] m)) =
              (TensorProduct.comm A DA EA)
                (ModuleCat.Hom.hom bDE.hom (a ⊗ₜ[R] (m ⊗ₜ[R] n)))
          rw [affineCechDescendedTensorBaseChangeIso_hom_tmul,
            affineCechDescendedTensorBaseChangeIso_hom_tmul,
            TensorProduct.comm_tmul]
          let qD : TensorProduct R A MD →ₗ[A] DA :=
            ModuleCat.Hom.hom bD.hom
          let qE : TensorProduct R A ME →ₗ[A] EA :=
            ModuleCat.Hom.hom bE.hom
          have hD :
              qD (a ⊗ₜ[R] m) = a • qD ((1 : A) ⊗ₜ[R] m) := by
            have htensor :
                a ⊗ₜ[R] m = a • ((1 : A) ⊗ₜ[R] m) := by
              simpa only [smul_eq_mul, mul_one] using
                (TensorProduct.smul_tmul' (R := R) (R' := A)
                  a (1 : A) m).symm
            calc
              qD (a ⊗ₜ[R] m) =
                  qD (a • ((1 : A) ⊗ₜ[R] m)) := congrArg qD htensor
              _ = a • qD ((1 : A) ⊗ₜ[R] m) := qD.map_smul _ _
          have hE :
              qE (a ⊗ₜ[R] n) = a • qE ((1 : A) ⊗ₜ[R] n) := by
            have htensor :
                a ⊗ₜ[R] n = a • ((1 : A) ⊗ₜ[R] n) := by
              simpa only [smul_eq_mul, mul_one] using
                (TensorProduct.smul_tmul' (R := R) (R' := A)
                  a (1 : A) n).symm
            calc
              qE (a ⊗ₜ[R] n) =
                  qE (a • ((1 : A) ⊗ₜ[R] n)) := congrArg qE htensor
              _ = a • qE ((1 : A) ⊗ₜ[R] n) := qE.map_smul _ _
          change
            qE (a ⊗ₜ[R] n) ⊗ₜ[A] qD ((1 : A) ⊗ₜ[R] m) =
              qE ((1 : A) ⊗ₜ[R] n) ⊗ₜ[A] qD (a ⊗ₜ[R] m)
          rw [hE, hD]
          exact TensorProduct.smul_tmul _ _ _
      | add x y hx hy =>
          simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The base tensor symmetries are natural in both descent data. -/
theorem affineCechSelectedTensorSymmetryBaseIso_natural
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    {D D' E E' : AffineCechModuleDescentData f}
    (g : D ⟶ D') (h : E ⟶ E') :
    affineCechDescendedTensorMap f hf g h ≫
        (affineCechSelectedTensorSymmetryBaseIso f hf D' E').hom =
      (affineCechSelectedTensorSymmetryBaseIso f hf D E).hom ≫
        affineCechDescendedTensorMap f hf h g := by
  let MD := affineCechDescendedModule f hf D
  let ME := affineCechDescendedModule f hf E
  let p : MD →ₗ[R] affineCechDescendedModule f hf D' :=
    ModuleCat.Hom.hom (affineCechDescendedModuleHom f hf g)
  let q : ME →ₗ[R] affineCechDescendedModule f hf E' :=
    ModuleCat.Hom.hom (affineCechDescendedModuleHom f hf h)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul m n =>
      change (TensorProduct.comm R _ _)
          (TensorProduct.map p q (m ⊗ₜ[R] n)) =
        TensorProduct.map q p
          ((TensorProduct.comm R _ _) (m ⊗ₜ[R] n))
      simp only [TensorProduct.comm_tmul, TensorProduct.map_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The selected-datum tensor symmetries are natural in both arguments. -/
theorem affineCechSelectedTensorSymmetryIso_natural
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    {D D' E E' : AffineCechModuleDescentData f}
    (g : D ⟶ D') (h : E ⟶ E') :
    affineCechSelectedTensorMap f hf g h ≫
        (affineCechSelectedTensorSymmetryIso f hf D' E').hom =
      (affineCechSelectedTensorSymmetryIso f hf D E).hom ≫
        affineCechSelectedTensorMap f hf h g := by
  let F := affineCechModuleDescentComparison f
  change
    F.map (affineCechDescendedTensorMap f hf g h) ≫
        F.map (affineCechSelectedTensorSymmetryBaseIso f hf D' E').hom =
      F.map (affineCechSelectedTensorSymmetryBaseIso f hf D E).hom ≫
        F.map (affineCechDescendedTensorMap f hf h g)
  rw [← F.map_comp,
    affineCechSelectedTensorSymmetryBaseIso_natural f hf g h,
    F.map_comp]

/-- Swapping the two base tensor factors twice is the identity. -/
theorem affineCechSelectedTensorSymmetryBaseIso_hom_comp
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D E : AffineCechModuleDescentData f) :
    (affineCechSelectedTensorSymmetryBaseIso f hf D E).hom ≫
        (affineCechSelectedTensorSymmetryBaseIso f hf E D).hom =
      𝟙 (ModuleCat.of R
        (TensorProduct R
          (affineCechDescendedModule f hf D)
          (affineCechDescendedModule f hf E))) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul m n =>
      change
        (TensorProduct.comm R _ _)
            ((TensorProduct.comm R _ _) (m ⊗ₜ[R] n)) =
          m ⊗ₜ[R] n
      rw [TensorProduct.comm_tmul, TensorProduct.comm_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Swapping the two selected tensor factors twice is the identity. -/
theorem affineCechSelectedTensorSymmetryIso_hom_comp
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D E : AffineCechModuleDescentData f) :
    (affineCechSelectedTensorSymmetryIso f hf D E).hom ≫
        (affineCechSelectedTensorSymmetryIso f hf E D).hom =
      𝟙 (affineCechSelectedTensorDescentData f hf D E) := by
  let F := affineCechModuleDescentComparison f
  change
    F.map (affineCechSelectedTensorSymmetryBaseIso f hf D E).hom ≫
        F.map (affineCechSelectedTensorSymmetryBaseIso f hf E D).hom =
      𝟙 (F.obj (ModuleCat.of R
        (TensorProduct R
          (affineCechDescendedModule f hf D)
          (affineCechDescendedModule f hf E))))
  rw [← F.map_comp,
    affineCechSelectedTensorSymmetryBaseIso_hom_comp f hf D E,
    F.map_id]

/-- The selected tensor bifunctor with its two factors exchanged. -/
noncomputable def affineCechSelectedTensorSwapFunctor
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat) :
    (AffineCechModuleDescentData f × AffineCechModuleDescentData f) ⥤
      AffineCechModuleDescentData f where
  obj X := affineCechSelectedTensorDescentData f hf X.2 X.1
  map g := affineCechSelectedTensorMap f hf g.2 g.1
  map_id X := affineCechSelectedTensorMap_id f hf X.2 X.1
  map_comp g h :=
    affineCechSelectedTensorMap_comp f hf g.2 h.2 g.1 h.1

/-- The selected tensor symmetry forms a natural isomorphism from the tensor
bifunctor to the factor-swapped tensor bifunctor. -/
noncomputable def affineCechSelectedTensorSymmetryNatIso
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat) :
    affineCechSelectedTensorFunctor f hf ≅
      affineCechSelectedTensorSwapFunctor f hf :=
  NatIso.ofComponents
    (fun X => affineCechSelectedTensorSymmetryIso f hf X.1 X.2)
    (by
      intro X Y g
      exact affineCechSelectedTensorSymmetryIso_natural f hf g.1 g.2)

/-- Comparing the chosen preimage isomorphism recovers the selected
object-level comparison isomorphism. -/
theorem affineCechDescendedComparisonObjIso_hom_comparison
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat) (M : ModuleCat R) :
    (affineCechModuleDescentComparison f).map
        (affineCechDescendedComparisonObjIso f hf M).hom =
      (affineCechDescendedModuleIso f hf
        ((affineCechModuleDescentComparison f).obj M)).hom := by
  let F := affineCechModuleDescentComparison f
  let _ : F.IsEquivalence :=
    affineCechModuleDescentComparison_isEquivalence f hf
  exact F.map_preimage _

/-- Comparing the inverse chosen preimage isomorphism recovers the inverse
selected object-level comparison isomorphism. -/
theorem affineCechDescendedComparisonObjIso_inv_comparison
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat) (M : ModuleCat R) :
    (affineCechModuleDescentComparison f).map
        (affineCechDescendedComparisonObjIso f hf M).inv =
      (affineCechDescendedModuleIso f hf
        ((affineCechModuleDescentComparison f).obj M)).inv := by
  let F := affineCechModuleDescentComparison f
  let _ : F.IsEquivalence :=
    affineCechModuleDescentComparison_isEquivalence f hf
  exact F.map_preimage _

/-- Descending a morphism already in the image of affine Čech comparison
conjugates it by the two chosen preimage isomorphisms. -/
theorem affineCechDescendedModuleHom_of_comparison_map
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat) {M N : ModuleCat R}
    (q : M ⟶ N) :
    affineCechDescendedModuleHom f hf
        ((affineCechModuleDescentComparison f).map q) =
      (affineCechDescendedComparisonObjIso f hf M).hom ≫ q ≫
        (affineCechDescendedComparisonObjIso f hf N).inv := by
  let F := affineCechModuleDescentComparison f
  let _ : F.IsEquivalence :=
    affineCechModuleDescentComparison_isEquivalence f hf
  apply F.map_injective
  rw [affineCechDescendedModuleHom_comparison, F.map_comp, F.map_comp,
    affineCechDescendedComparisonObjIso_hom_comparison,
    affineCechDescendedComparisonObjIso_inv_comparison]

/-- Descending the selected left unitor recovers its base map after the
selected tensor preimage comparison. -/
theorem affineCechDescendedModuleHom_leftUnitorIso_hom
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D : AffineCechModuleDescentData f) :
    affineCechDescendedModuleHom f hf
        (affineCechSelectedTensorLeftUnitorIso f hf D).hom =
      (affineCechSelectedTensorDescendedIso f hf
          (affineCechSelectedTensorUnitDescentData f) D).hom ≫
        (affineCechSelectedTensorLeftUnitorBaseIso f hf D).hom := by
  let F := affineCechModuleDescentComparison f
  let _ : F.IsEquivalence :=
    affineCechModuleDescentComparison_isEquivalence f hf
  let U := affineCechSelectedTensorUnitDescentData f
  let M := ModuleCat.of R
    (TensorProduct R
      (affineCechDescendedModule f hf U)
      (affineCechDescendedModule f hf D))
  apply F.map_injective
  rw [affineCechDescendedModuleHom_comparison, F.map_comp]
  change
    (affineCechDescendedModuleIso f hf (F.obj M)).hom ≫
        (F.map (affineCechSelectedTensorLeftUnitorBaseIso f hf D).hom ≫
          (affineCechDescendedModuleIso f hf D).hom) ≫
        (affineCechDescendedModuleIso f hf D).inv =
      F.map (affineCechDescendedComparisonObjIso f hf M).hom ≫
        F.map (affineCechSelectedTensorLeftUnitorBaseIso f hf D).hom
  rw [affineCechDescendedComparisonObjIso_hom_comparison]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

/-- Descending the selected right unitor recovers its base map after the
selected tensor preimage comparison. -/
theorem affineCechDescendedModuleHom_rightUnitorIso_hom
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D : AffineCechModuleDescentData f) :
    affineCechDescendedModuleHom f hf
        (affineCechSelectedTensorRightUnitorIso f hf D).hom =
      (affineCechSelectedTensorDescendedIso f hf D
          (affineCechSelectedTensorUnitDescentData f)).hom ≫
        (affineCechSelectedTensorRightUnitorBaseIso f hf D).hom := by
  let F := affineCechModuleDescentComparison f
  let _ : F.IsEquivalence :=
    affineCechModuleDescentComparison_isEquivalence f hf
  let U := affineCechSelectedTensorUnitDescentData f
  let M := ModuleCat.of R
    (TensorProduct R
      (affineCechDescendedModule f hf D)
      (affineCechDescendedModule f hf U))
  apply F.map_injective
  rw [affineCechDescendedModuleHom_comparison, F.map_comp]
  change
    (affineCechDescendedModuleIso f hf (F.obj M)).hom ≫
        (F.map (affineCechSelectedTensorRightUnitorBaseIso f hf D).hom ≫
          (affineCechDescendedModuleIso f hf D).hom) ≫
        (affineCechDescendedModuleIso f hf D).inv =
      F.map (affineCechDescendedComparisonObjIso f hf M).hom ≫
        F.map (affineCechSelectedTensorRightUnitorBaseIso f hf D).hom
  rw [affineCechDescendedComparisonObjIso_hom_comparison]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

/-- The selected associator and unitors satisfy the triangle coherence law. -/
theorem affineCechSelectedTensor_triangle
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D E : AffineCechModuleDescentData f) :
    (affineCechSelectedTensorAssociatorIso f hf D
          (affineCechSelectedTensorUnitDescentData f) E).hom ≫
        affineCechSelectedTensorMap f hf (𝟙 D)
          (affineCechSelectedTensorLeftUnitorIso f hf E).hom =
      affineCechSelectedTensorMap f hf
        (affineCechSelectedTensorRightUnitorIso f hf D).hom (𝟙 E) := by
  let F := affineCechModuleDescentComparison f
  let _ : F.IsEquivalence :=
    affineCechModuleDescentComparison_isEquivalence f hf
  let U := affineCechSelectedTensorUnitDescentData f
  let MD := affineCechDescendedModule f hf D
  let ME := affineCechDescendedModule f hf E
  let eDU := affineCechSelectedTensorDescendedIso f hf D U
  let eUE := affineCechSelectedTensorDescendedIso f hf U E
  let lE := affineCechSelectedTensorLeftUnitorBaseIso f hf E
  let rD := affineCechSelectedTensorRightUnitorBaseIso f hf D
  have hbase :
      (affineCechSelectedTensorAssociatorBaseIso f hf D U E).hom ≫
          affineCechDescendedTensorMap f hf (𝟙 D)
            (affineCechSelectedTensorLeftUnitorIso f hf E).hom =
        affineCechDescendedTensorMap f hf
          (affineCechSelectedTensorRightUnitorIso f hf D).hom (𝟙 E) := by
    unfold affineCechDescendedTensorMap
    simp only [affineCechDescendedModuleHom_id,
      affineCechDescendedModuleHom_leftUnitorIso_hom,
      affineCechDescendedModuleHom_rightUnitorIso_hom]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul m n =>
        rw [← eDU.hom_inv_id_apply m]
        generalize eDU.hom m = w
        induction w using TensorProduct.induction_on with
        | zero =>
            simp only [TensorProduct.zero_tmul, map_zero]
        | tmul p u =>
            change
              TensorProduct.map LinearMap.id
                  (ModuleCat.Hom.hom (eUE.hom ≫ lE.hom))
                ((affineCechSelectedTensorAssociatorBaseIso f hf D U E).hom
                  (eDU.inv (p ⊗ₜ[R] u) ⊗ₜ[R] n)) =
                TensorProduct.map
                    (ModuleCat.Hom.hom (eDU.hom ≫ rD.hom)) LinearMap.id
                  (eDU.inv (p ⊗ₜ[R] u) ⊗ₜ[R] n)
            change
              TensorProduct.map LinearMap.id
                  (ModuleCat.Hom.hom (eUE.hom ≫ lE.hom))
                (((TensorProduct.congr eDU.toLinearEquiv
                    (LinearEquiv.refl R ME)).trans
                  ((TensorProduct.assoc R MD
                      (affineCechDescendedModule f hf U) ME).trans
                    (TensorProduct.congr
                      (LinearEquiv.refl R MD)
                      eUE.symm.toLinearEquiv)))
                  (eDU.inv (p ⊗ₜ[R] u) ⊗ₜ[R] n)) =
                TensorProduct.map
                    (ModuleCat.Hom.hom (eDU.hom ≫ rD.hom)) LinearMap.id
                  (eDU.inv (p ⊗ₜ[R] u) ⊗ₜ[R] n)
            rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply]
            rw [TensorProduct.congr_tmul]
            have hDUcancel :
                eDU.toLinearEquiv (eDU.inv (p ⊗ₜ[R] u)) =
                  p ⊗ₜ[R] u := by
              exact eDU.inv_hom_id_apply _
            rw [hDUcancel, LinearEquiv.refl_apply]
            rw [TensorProduct.assoc_tmul]
            rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply]
            rw [TensorProduct.map_tmul, TensorProduct.map_tmul]
            change
              p ⊗ₜ[R]
                  lE.hom (eUE.hom (eUE.inv (u ⊗ₜ[R] n))) =
                rD.hom (eDU.hom (eDU.inv (p ⊗ₜ[R] u))) ⊗ₜ[R] n
            rw [eUE.inv_hom_id_apply, eDU.inv_hom_id_apply]
            change
              p ⊗ₜ[R]
                  (TensorProduct.lid R _)
                    ((TensorProduct.congr
                      (affineCechSelectedTensorUnitDescendedIso f hf).toLinearEquiv
                      (LinearEquiv.refl R _)) (u ⊗ₜ[R] n)) =
                (TensorProduct.rid R _)
                    ((TensorProduct.congr
                      (LinearEquiv.refl R _)
                      (affineCechSelectedTensorUnitDescendedIso f hf).toLinearEquiv)
                      (p ⊗ₜ[R] u)) ⊗ₜ[R] n
            rw [TensorProduct.congr_tmul, TensorProduct.congr_tmul,
              LinearEquiv.refl_apply, LinearEquiv.refl_apply,
              TensorProduct.lid_tmul, TensorProduct.rid_tmul]
            exact TensorProduct.tmul_smul (R := R) (R' := R)
              (show R from
                (affineCechSelectedTensorUnitDescendedIso f hf).hom u)
              p n
        | add x y hx hy =>
            simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  change
    F.map (affineCechSelectedTensorAssociatorBaseIso f hf D U E).hom ≫
        F.map (affineCechDescendedTensorMap f hf (𝟙 D)
          (affineCechSelectedTensorLeftUnitorIso f hf E).hom) =
      F.map (affineCechDescendedTensorMap f hf
        (affineCechSelectedTensorRightUnitorIso f hf D).hom (𝟙 E))
  rw [← F.map_comp, hbase]

/-- The selected associator base map on a pure tensor whose first factor
is expressed through the selected tensor preimage comparison. -/
theorem affineCechSelectedTensorAssociatorBaseIso_hom_tmul
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D E G : AffineCechModuleDescentData f)
    (m : affineCechDescendedModule f hf D)
    (n : affineCechDescendedModule f hf E)
    (p : affineCechDescendedModule f hf G) :
    (affineCechSelectedTensorAssociatorBaseIso f hf D E G).hom
        ((affineCechSelectedTensorDescendedIso f hf D E).inv
          (m ⊗ₜ[R] n) ⊗ₜ[R] p) =
      m ⊗ₜ[R]
        (affineCechSelectedTensorDescendedIso f hf E G).inv
          (n ⊗ₜ[R] p) := by
  let eDE := affineCechSelectedTensorDescendedIso f hf D E
  let eEG := affineCechSelectedTensorDescendedIso f hf E G
  change
    (((TensorProduct.congr eDE.toLinearEquiv
        (LinearEquiv.refl R _)).trans
      ((TensorProduct.assoc R _ _ _).trans
        (TensorProduct.congr
          (LinearEquiv.refl R _)
          eEG.symm.toLinearEquiv)))
      (eDE.inv (m ⊗ₜ[R] n) ⊗ₜ[R] p)) =
        m ⊗ₜ[R] eEG.inv (n ⊗ₜ[R] p)
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply]
  rw [TensorProduct.congr_tmul]
  have hcancel :
      eDE.toLinearEquiv (eDE.inv (m ⊗ₜ[R] n)) =
        m ⊗ₜ[R] n := by
    exact eDE.inv_hom_id_apply _
  rw [hcancel, LinearEquiv.refl_apply]
  rw [TensorProduct.assoc_tmul]
  rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply]
  rfl

/-- Descending the selected associator recovers its base map, conjugated by
the two selected tensor preimage comparisons. -/
theorem affineCechDescendedModuleHom_associatorIso_hom
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D E G : AffineCechModuleDescentData f) :
    affineCechDescendedModuleHom f hf
        (affineCechSelectedTensorAssociatorIso f hf D E G).hom =
      (affineCechSelectedTensorDescendedIso f hf
          (affineCechSelectedTensorDescentData f hf D E) G).hom ≫
        (affineCechSelectedTensorAssociatorBaseIso f hf D E G).hom ≫
        (affineCechSelectedTensorDescendedIso f hf D
          (affineCechSelectedTensorDescentData f hf E G)).inv := by
  exact affineCechDescendedModuleHom_of_comparison_map f hf
    (affineCechSelectedTensorAssociatorBaseIso f hf D E G).hom

/-- The selected associators are natural in all three arguments. -/
theorem affineCechSelectedTensorAssociatorIso_natural
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    {D D' E E' G G' : AffineCechModuleDescentData f}
    (p : D ⟶ D') (q : E ⟶ E') (r : G ⟶ G') :
    affineCechSelectedTensorMap f hf
          (affineCechSelectedTensorMap f hf p q) r ≫
        (affineCechSelectedTensorAssociatorIso f hf D' E' G').hom =
      (affineCechSelectedTensorAssociatorIso f hf D E G).hom ≫
        affineCechSelectedTensorMap f hf p
          (affineCechSelectedTensorMap f hf q r) := by
  let F := affineCechModuleDescentComparison f
  let _ : F.IsEquivalence :=
    affineCechModuleDescentComparison_isEquivalence f hf
  let DE := affineCechSelectedTensorDescentData f hf D E
  let D'E' := affineCechSelectedTensorDescentData f hf D' E'
  let EG := affineCechSelectedTensorDescentData f hf E G
  let E'G' := affineCechSelectedTensorDescentData f hf E' G'
  let eDE := affineCechSelectedTensorDescendedIso f hf D E
  let eD'E' := affineCechSelectedTensorDescendedIso f hf D' E'
  let eEG := affineCechSelectedTensorDescendedIso f hf E G
  let eE'G' := affineCechSelectedTensorDescendedIso f hf E' G'
  let pD := ModuleCat.Hom.hom (affineCechDescendedModuleHom f hf p)
  let pE := ModuleCat.Hom.hom (affineCechDescendedModuleHom f hf q)
  let pG := ModuleCat.Hom.hom (affineCechDescendedModuleHom f hf r)
  have hDE :
      affineCechDescendedModuleHom f hf
          (affineCechSelectedTensorMap f hf p q) =
        eDE.hom ≫ affineCechDescendedTensorMap f hf p q ≫ eD'E'.inv := by
    exact affineCechDescendedModuleHom_of_comparison_map f hf
      (affineCechDescendedTensorMap f hf p q)
  have hEG :
      affineCechDescendedModuleHom f hf
          (affineCechSelectedTensorMap f hf q r) =
        eEG.hom ≫ affineCechDescendedTensorMap f hf q r ≫ eE'G'.inv := by
    exact affineCechDescendedModuleHom_of_comparison_map f hf
      (affineCechDescendedTensorMap f hf q r)
  have hbase :
      affineCechDescendedTensorMap f hf
            (affineCechSelectedTensorMap f hf p q) r ≫
          (affineCechSelectedTensorAssociatorBaseIso f hf D' E' G').hom =
        (affineCechSelectedTensorAssociatorBaseIso f hf D E G).hom ≫
          affineCechDescendedTensorMap f hf p
            (affineCechSelectedTensorMap f hf q r) := by
    unfold affineCechDescendedTensorMap
    simp only [hDE, hEG]
    let pDE :=
      ModuleCat.Hom.hom
        (eDE.hom ≫ affineCechDescendedTensorMap f hf p q ≫ eD'E'.inv)
    let pEG :=
      ModuleCat.Hom.hom
        (eEG.hom ≫ affineCechDescendedTensorMap f hf q r ≫ eE'G'.inv)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul m g =>
        rw [← eDE.hom_inv_id_apply m]
        generalize eDE.hom m = w
        induction w using TensorProduct.induction_on with
        | zero => simp only [TensorProduct.zero_tmul, map_zero]
        | tmul d e =>
            change
              (affineCechSelectedTensorAssociatorBaseIso f hf D' E' G').hom
                (TensorProduct.map pDE pG
                  (eDE.inv (d ⊗ₜ[R] e) ⊗ₜ[R] g)) =
                TensorProduct.map pD pEG
                  ((affineCechSelectedTensorAssociatorBaseIso f hf D E G).hom
                    (eDE.inv (d ⊗ₜ[R] e) ⊗ₜ[R] g))
            rw [TensorProduct.map_tmul]
            have hpDE :
                pDE (eDE.inv (d ⊗ₜ[R] e)) =
                  eD'E'.inv (pD d ⊗ₜ[R] pE e) := by
              dsimp [pDE]
              rw [eDE.inv_hom_id_apply]
              change
                eD'E'.inv (TensorProduct.map pD pE (d ⊗ₜ[R] e)) =
                  eD'E'.inv (pD d ⊗ₜ[R] pE e)
              rw [TensorProduct.map_tmul]
            rw [hpDE]
            rw [affineCechSelectedTensorAssociatorBaseIso_hom_tmul]
            rw [affineCechSelectedTensorAssociatorBaseIso_hom_tmul]
            rw [TensorProduct.map_tmul]
            have hpEG :
                pEG (eEG.inv (e ⊗ₜ[R] g)) =
                  eE'G'.inv (pE e ⊗ₜ[R] pG g) := by
              dsimp [pEG]
              rw [eEG.inv_hom_id_apply]
              change
                eE'G'.inv (TensorProduct.map pE pG (e ⊗ₜ[R] g)) =
                  eE'G'.inv (pE e ⊗ₜ[R] pG g)
              rw [TensorProduct.map_tmul]
            rw [hpEG]
        | add x y hx hy =>
            simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  change
    F.map (affineCechDescendedTensorMap f hf
          (affineCechSelectedTensorMap f hf p q) r) ≫
        F.map (affineCechSelectedTensorAssociatorBaseIso f hf D' E' G').hom =
      F.map (affineCechSelectedTensorAssociatorBaseIso f hf D E G).hom ≫
        F.map (affineCechDescendedTensorMap f hf p
          (affineCechSelectedTensorMap f hf q r))
  rw [← F.map_comp, hbase, F.map_comp]

/-- The selected associators satisfy the pentagon coherence law. -/
theorem affineCechSelectedTensor_pentagon
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D E G H : AffineCechModuleDescentData f) :
    (affineCechSelectedTensorAssociatorIso f hf
          (affineCechSelectedTensorDescentData f hf D E) G H).hom ≫
        (affineCechSelectedTensorAssociatorIso f hf D E
          (affineCechSelectedTensorDescentData f hf G H)).hom =
      affineCechSelectedTensorMap f hf
          (affineCechSelectedTensorAssociatorIso f hf D E G).hom (𝟙 H) ≫
        (affineCechSelectedTensorAssociatorIso f hf D
          (affineCechSelectedTensorDescentData f hf E G) H).hom ≫
        affineCechSelectedTensorMap f hf (𝟙 D)
          (affineCechSelectedTensorAssociatorIso f hf E G H).hom := by
  let F := affineCechModuleDescentComparison f
  let _ : F.IsEquivalence :=
    affineCechModuleDescentComparison_isEquivalence f hf
  let DE := affineCechSelectedTensorDescentData f hf D E
  let EG := affineCechSelectedTensorDescentData f hf E G
  let GH := affineCechSelectedTensorDescentData f hf G H
  let DEG := affineCechSelectedTensorDescentData f hf DE G
  let D_EG := affineCechSelectedTensorDescentData f hf D EG
  let E_GH := affineCechSelectedTensorDescentData f hf E GH
  let EGH := affineCechSelectedTensorDescentData f hf EG H
  let eDE := affineCechSelectedTensorDescendedIso f hf D E
  let eDEG := affineCechSelectedTensorDescendedIso f hf DE G
  let eD_EG := affineCechSelectedTensorDescendedIso f hf D EG
  let eEG := affineCechSelectedTensorDescendedIso f hf E G
  let eGH := affineCechSelectedTensorDescendedIso f hf G H
  let eEGH := affineCechSelectedTensorDescendedIso f hf EG H
  let eE_GH := affineCechSelectedTensorDescendedIso f hf E GH
  have hbase :
      (affineCechSelectedTensorAssociatorBaseIso f hf DE G H).hom ≫
          (affineCechSelectedTensorAssociatorBaseIso f hf D E GH).hom =
        affineCechDescendedTensorMap f hf
            (affineCechSelectedTensorAssociatorIso f hf D E G).hom (𝟙 H) ≫
          (affineCechSelectedTensorAssociatorBaseIso f hf D EG H).hom ≫
          affineCechDescendedTensorMap f hf (𝟙 D)
            (affineCechSelectedTensorAssociatorIso f hf E G H).hom := by
    unfold affineCechDescendedTensorMap
    simp only [affineCechDescendedModuleHom_id,
      affineCechDescendedModuleHom_associatorIso_hom]
    let qDEG :=
      ModuleCat.Hom.hom
        (eDEG.hom ≫
          (affineCechSelectedTensorAssociatorBaseIso f hf D E G).hom ≫
          eD_EG.inv)
    let qEGH :=
      ModuleCat.Hom.hom
        (eEGH.hom ≫
          (affineCechSelectedTensorAssociatorBaseIso f hf E G H).hom ≫
          eE_GH.inv)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul m h =>
        rw [← eDEG.hom_inv_id_apply m]
        generalize eDEG.hom m = w
        induction w using TensorProduct.induction_on with
        | zero => simp only [TensorProduct.zero_tmul, map_zero]
        | tmul de g =>
            rw [← eDE.hom_inv_id_apply de]
            generalize eDE.hom de = v
            induction v using TensorProduct.induction_on with
            | zero => simp only [TensorProduct.zero_tmul, map_zero]
            | tmul d e =>
                change
                  (affineCechSelectedTensorAssociatorBaseIso f hf D E GH).hom
                    ((affineCechSelectedTensorAssociatorBaseIso f hf DE G H).hom
                      (eDEG.inv (eDE.inv (d ⊗ₜ[R] e) ⊗ₜ[R] g) ⊗ₜ[R] h)) =
                    TensorProduct.map LinearMap.id qEGH
                      ((affineCechSelectedTensorAssociatorBaseIso
                        f hf D EG H).hom
                        (TensorProduct.map qDEG LinearMap.id
                          (eDEG.inv
                            (eDE.inv (d ⊗ₜ[R] e) ⊗ₜ[R] g) ⊗ₜ[R] h)))
                rw [affineCechSelectedTensorAssociatorBaseIso_hom_tmul,
                  affineCechSelectedTensorAssociatorBaseIso_hom_tmul]
                rw [TensorProduct.map_tmul]
                have hqDEG :
                    qDEG
                        (eDEG.inv
                          (eDE.inv (d ⊗ₜ[R] e) ⊗ₜ[R] g)) =
                      eD_EG.inv (d ⊗ₜ[R] eEG.inv (e ⊗ₜ[R] g)) := by
                  dsimp [qDEG]
                  rw [eDEG.inv_hom_id_apply]
                  rw [affineCechSelectedTensorAssociatorBaseIso_hom_tmul]
                rw [hqDEG]
                rw [affineCechSelectedTensorAssociatorBaseIso_hom_tmul]
                rw [TensorProduct.map_tmul]
                have hqEGH :
                    qEGH
                        (eEGH.inv
                          (eEG.inv (e ⊗ₜ[R] g) ⊗ₜ[R] h)) =
                      eE_GH.inv (e ⊗ₜ[R] eGH.inv (g ⊗ₜ[R] h)) := by
                  dsimp [qEGH]
                  rw [eEGH.inv_hom_id_apply]
                  rw [affineCechSelectedTensorAssociatorBaseIso_hom_tmul]
                change
                  d ⊗ₜ[R] eE_GH.inv
                      (e ⊗ₜ[R] eGH.inv (g ⊗ₜ[R] h)) =
                    d ⊗ₜ[R]
                      qEGH
                        (eEGH.inv
                          (eEG.inv (e ⊗ₜ[R] g) ⊗ₜ[R] h))
                rw [hqEGH]
            | add x y hx hy =>
                simp only [TensorProduct.add_tmul, map_add, hx, hy]
        | add x y hx hy =>
            simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  change
    F.map (affineCechSelectedTensorAssociatorBaseIso f hf DE G H).hom ≫
        F.map (affineCechSelectedTensorAssociatorBaseIso f hf D E GH).hom =
      F.map (affineCechDescendedTensorMap f hf
          (affineCechSelectedTensorAssociatorIso f hf D E G).hom (𝟙 H)) ≫
        F.map (affineCechSelectedTensorAssociatorBaseIso f hf D EG H).hom ≫
        F.map (affineCechDescendedTensorMap f hf (𝟙 D)
          (affineCechSelectedTensorAssociatorIso f hf E G H).hom)
  rw [← F.map_comp, ← F.map_comp, ← F.map_comp, hbase]

/-- Descending the selected symmetry recovers its base map, conjugated by the
two selected tensor preimage comparisons. -/
theorem affineCechDescendedModuleHom_symmetryIso_hom
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D E : AffineCechModuleDescentData f) :
    affineCechDescendedModuleHom f hf
        (affineCechSelectedTensorSymmetryIso f hf D E).hom =
      (affineCechSelectedTensorDescendedIso f hf D E).hom ≫
        (affineCechSelectedTensorSymmetryBaseIso f hf D E).hom ≫
        (affineCechSelectedTensorDescendedIso f hf E D).inv := by
  exact affineCechDescendedModuleHom_of_comparison_map f hf
    (affineCechSelectedTensorSymmetryBaseIso f hf D E).hom

set_option maxHeartbeats 800000 in
-- Normalizing both three-factor hexagon paths requires nested tensor induction.
/-- The selected associator and symmetry satisfy the braided hexagon law. -/
theorem affineCechSelectedTensor_hexagon
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D E G : AffineCechModuleDescentData f) :
    (affineCechSelectedTensorAssociatorIso f hf D E G).hom ≫
        (affineCechSelectedTensorSymmetryIso f hf D
          (affineCechSelectedTensorDescentData f hf E G)).hom ≫
        (affineCechSelectedTensorAssociatorIso f hf E G D).hom =
      affineCechSelectedTensorMap f hf
          (affineCechSelectedTensorSymmetryIso f hf D E).hom (𝟙 G) ≫
        (affineCechSelectedTensorAssociatorIso f hf E D G).hom ≫
        affineCechSelectedTensorMap f hf (𝟙 E)
          (affineCechSelectedTensorSymmetryIso f hf D G).hom := by
  let F := affineCechModuleDescentComparison f
  let _ : F.IsEquivalence :=
    affineCechModuleDescentComparison_isEquivalence f hf
  let DE := affineCechSelectedTensorDescentData f hf D E
  let ED := affineCechSelectedTensorDescentData f hf E D
  let EG := affineCechSelectedTensorDescentData f hf E G
  let DG := affineCechSelectedTensorDescentData f hf D G
  let GD := affineCechSelectedTensorDescentData f hf G D
  let eDE := affineCechSelectedTensorDescendedIso f hf D E
  let eED := affineCechSelectedTensorDescendedIso f hf E D
  let eEG := affineCechSelectedTensorDescendedIso f hf E G
  let eDG := affineCechSelectedTensorDescendedIso f hf D G
  let eGD := affineCechSelectedTensorDescendedIso f hf G D
  have hbase :
      (affineCechSelectedTensorAssociatorBaseIso f hf D E G).hom ≫
          (affineCechSelectedTensorSymmetryBaseIso f hf D EG).hom ≫
          (affineCechSelectedTensorAssociatorBaseIso f hf E G D).hom =
        affineCechDescendedTensorMap f hf
            (affineCechSelectedTensorSymmetryIso f hf D E).hom (𝟙 G) ≫
          (affineCechSelectedTensorAssociatorBaseIso f hf E D G).hom ≫
          affineCechDescendedTensorMap f hf (𝟙 E)
            (affineCechSelectedTensorSymmetryIso f hf D G).hom := by
    unfold affineCechDescendedTensorMap
    simp only [affineCechDescendedModuleHom_id,
      affineCechDescendedModuleHom_symmetryIso_hom]
    let qDE :=
      ModuleCat.Hom.hom
        (eDE.hom ≫
          (affineCechSelectedTensorSymmetryBaseIso f hf D E).hom ≫
          eED.inv)
    let qDG :=
      ModuleCat.Hom.hom
        (eDG.hom ≫
          (affineCechSelectedTensorSymmetryBaseIso f hf D G).hom ≫
          eGD.inv)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul m g =>
        rw [← eDE.hom_inv_id_apply m]
        generalize eDE.hom m = w
        induction w using TensorProduct.induction_on with
        | zero => simp only [TensorProduct.zero_tmul, map_zero]
        | tmul d e =>
            change
              (affineCechSelectedTensorAssociatorBaseIso f hf E G D).hom
                ((affineCechSelectedTensorSymmetryBaseIso f hf D EG).hom
                  ((affineCechSelectedTensorAssociatorBaseIso f hf D E G).hom
                    (eDE.inv (d ⊗ₜ[R] e) ⊗ₜ[R] g))) =
                TensorProduct.map LinearMap.id qDG
                  ((affineCechSelectedTensorAssociatorBaseIso f hf E D G).hom
                    (TensorProduct.map qDE LinearMap.id
                      (eDE.inv (d ⊗ₜ[R] e) ⊗ₜ[R] g)))
            rw [affineCechSelectedTensorAssociatorBaseIso_hom_tmul]
            change
              (affineCechSelectedTensorAssociatorBaseIso f hf E G D).hom
                (eEG.inv (e ⊗ₜ[R] g) ⊗ₜ[R] d) =
              TensorProduct.map LinearMap.id qDG
                ((affineCechSelectedTensorAssociatorBaseIso f hf E D G).hom
                  (TensorProduct.map qDE LinearMap.id
                    (eDE.inv (d ⊗ₜ[R] e) ⊗ₜ[R] g)))
            rw [affineCechSelectedTensorAssociatorBaseIso_hom_tmul]
            rw [TensorProduct.map_tmul]
            have hqDE :
                qDE (eDE.inv (d ⊗ₜ[R] e)) =
                  eED.inv (e ⊗ₜ[R] d) := by
              dsimp [qDE]
              rw [eDE.inv_hom_id_apply]
              change
                eED.inv
                    ((TensorProduct.comm R
                      (affineCechDescendedModule f hf D)
                      (affineCechDescendedModule f hf E))
                      (d ⊗ₜ[R] e)) =
                  eED.inv (e ⊗ₜ[R] d)
              rw [TensorProduct.comm_tmul]
            rw [hqDE]
            rw [affineCechSelectedTensorAssociatorBaseIso_hom_tmul]
            rw [TensorProduct.map_tmul]
            have hqDG :
                qDG (eDG.inv (d ⊗ₜ[R] g)) =
                  eGD.inv (g ⊗ₜ[R] d) := by
              dsimp [qDG]
              rw [eDG.inv_hom_id_apply]
              change
                eGD.inv
                    ((TensorProduct.comm R
                      (affineCechDescendedModule f hf D)
                      (affineCechDescendedModule f hf G))
                      (d ⊗ₜ[R] g)) =
                  eGD.inv (g ⊗ₜ[R] d)
              rw [TensorProduct.comm_tmul]
            change
              e ⊗ₜ[R] eGD.inv (g ⊗ₜ[R] d) =
                e ⊗ₜ[R] qDG (eDG.inv (d ⊗ₜ[R] g))
            rw [hqDG]
        | add x y hx hy =>
            simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  change
    F.map (affineCechSelectedTensorAssociatorBaseIso f hf D E G).hom ≫
        F.map (affineCechSelectedTensorSymmetryBaseIso f hf D EG).hom ≫
        F.map (affineCechSelectedTensorAssociatorBaseIso f hf E G D).hom =
      F.map (affineCechDescendedTensorMap f hf
          (affineCechSelectedTensorSymmetryIso f hf D E).hom (𝟙 G)) ≫
        F.map (affineCechSelectedTensorAssociatorBaseIso f hf E D G).hom ≫
        F.map (affineCechDescendedTensorMap f hf (𝟙 E)
          (affineCechSelectedTensorSymmetryIso f hf D G).hom)
  rw [← F.map_comp, ← F.map_comp, ← F.map_comp, ← F.map_comp, hbase]

end RiemannResearch.AlgebraicGeometry
