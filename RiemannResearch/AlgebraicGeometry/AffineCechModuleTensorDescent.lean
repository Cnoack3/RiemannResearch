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
It also constructs the selected associator and tensor unit, proves exact
cover-level formulas for the associator and both unitors, and packages the
unitors as natural isomorphisms.  Symmetry and the remaining coherence laws
are not asserted here.
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

end RiemannResearch.AlgebraicGeometry
