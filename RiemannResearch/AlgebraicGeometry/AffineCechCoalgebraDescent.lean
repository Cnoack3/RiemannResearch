/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.AffineCechAlgebraDescent

/-!
# Coalgebra objects in affine Čech module descent

This file begins the coalgebra side of the affine Čech Hopf-descent program.
It packages coalgebra and cocommutative coalgebra objects for the selected
symmetric tensor structure, descends their comultiplication and counit, and
proves exact scalar-extension formulas recovering the ordinary cover maps.
It transports coassociativity, both counit equations, and cocommutativity to
the ordinary tensor product on the selected descended base module.

Bialgebra compatibility and antipode descent remain a separate next layer.

Source: user-provided affine Čech descent program; the formal proof transports
coalgebra-object maps through the previously verified selected symmetric
tensor comparisons.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory

namespace RiemannResearch.AlgebraicGeometry

/-- A coassociative counital coalgebra object for the selected tensor
structure on affine Čech module descent data. -/
structure AffineCechSelectedCoalgebraObject
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat) where
  obj : AffineCechModuleDescentData f
  comul :
    obj ⟶ affineCechSelectedTensorDescentData f hf obj obj
  counit :
    obj ⟶ affineCechSelectedTensorUnitDescentData f
  comul_assoc :
    comul ≫
          affineCechSelectedTensorMap f hf comul (𝟙 obj) ≫
          (affineCechSelectedTensorAssociatorIso f hf obj obj obj).hom =
      comul ≫
          affineCechSelectedTensorMap f hf (𝟙 obj) comul
  counit_left :
    comul ≫
          affineCechSelectedTensorMap f hf counit (𝟙 obj) ≫
          (affineCechSelectedTensorLeftUnitorIso f hf obj).hom =
      𝟙 obj
  counit_right :
    comul ≫
          affineCechSelectedTensorMap f hf (𝟙 obj) counit ≫
          (affineCechSelectedTensorRightUnitorIso f hf obj).hom =
      𝟙 obj

/-- A cocommutative coalgebra object for the selected symmetric tensor
structure on affine Čech module descent data. -/
structure AffineCechSelectedCocommCoalgebraObject
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    extends AffineCechSelectedCoalgebraObject f hf where
  comul_comm :
    toAffineCechSelectedCoalgebraObject.comul ≫
        (affineCechSelectedTensorSymmetryIso f hf
          toAffineCechSelectedCoalgebraObject.obj
          toAffineCechSelectedCoalgebraObject.obj).hom =
      toAffineCechSelectedCoalgebraObject.comul

namespace AffineCechSelectedCoalgebraObject

variable {R A : CommRingCat.{u}} {f : R ⟶ A}
variable {hf : f.hom.FaithfullyFlat}
variable (C : AffineCechSelectedCoalgebraObject f hf)

/-- Comultiplication on the selected descended base module. -/
noncomputable def descendedComul :
    affineCechDescendedModule f hf C.obj ⟶
      ModuleCat.of R
        (TensorProduct R
          (affineCechDescendedModule f hf C.obj)
          (affineCechDescendedModule f hf C.obj)) :=
  affineCechDescendedModuleHom f hf C.comul ≫
    (affineCechSelectedTensorDescendedIso f hf C.obj C.obj).hom

/-- Counit on the selected descended base module. -/
noncomputable def descendedCounit :
    affineCechDescendedModule f hf C.obj ⟶ ModuleCat.of R R :=
  affineCechDescendedModuleHom f hf C.counit ≫
    (affineCechSelectedTensorUnitDescendedIso f hf).hom

/-- Comultiplication on the cover module, expressed into the ordinary tensor
product of the cover object with itself. -/
noncomputable def coverComul :
    (AffineCechModuleDescentData.evaluation f).obj C.obj ⟶
      ModuleCat.of A
        (TensorProduct A
          ((AffineCechModuleDescentData.evaluation f).obj C.obj)
          ((AffineCechModuleDescentData.evaluation f).obj C.obj)) :=
  (AffineCechModuleDescentData.evaluation f).map C.comul ≫
    (affineCechSelectedTensorDescentDataCoverIso f hf C.obj C.obj).hom

/-- Counit on the cover module, expressed into the regular cover module. -/
noncomputable def coverCounit :
    (AffineCechModuleDescentData.evaluation f).obj C.obj ⟶
      ModuleCat.of A A :=
  (AffineCechModuleDescentData.evaluation f).map C.counit ≫
    (affineCechSelectedTensorUnitCoverIso f).hom

/-- Before transporting the target by the cover tensor comparison, scalar
extension of the descended comultiplication is exactly the evaluated
comultiplication morphism. -/
theorem descendedComul_baseChange_raw :
    (affineCechDescendedModuleBaseChangeIso f hf C.obj).hom ≫
        (AffineCechModuleDescentData.evaluation f).map C.comul =
      (ModuleCat.extendScalars f.hom).map C.descendedComul := by
  let M := affineCechDescendedModule f hf C.obj
  let X := ModuleCat.of R (TensorProduct R M M)
  let T := affineCechSelectedTensorDescentData f hf C.obj C.obj
  let DA : ModuleCat A :=
    (AffineCechModuleDescentData.evaluation f).obj C.obj
  let TA : ModuleCat A := (ModuleCat.extendScalars f.hom).obj X
  let e : affineCechDescendedModule f hf T ≅ X :=
    affineCechSelectedTensorDescendedIso f hf C.obj C.obj
  let bT : (ModuleCat.extendScalars f.hom).obj
      (affineCechDescendedModule f hf T) ≅ TA :=
    affineCechDescendedModuleBaseChangeIso f hf T
  let bC : (ModuleCat.extendScalars f.hom).obj M ≅ DA :=
    affineCechDescendedModuleBaseChangeIso f hf C.obj
  let q : DA ⟶ TA :=
    (AffineCechModuleDescentData.evaluation f).map C.comul
  have he : (ModuleCat.extendScalars f.hom).map e.hom = bT.hom := by
    exact affineCechDescendedComparisonObjIso_hom_baseChange f hf X
  change bC.hom ≫ q =
    (ModuleCat.extendScalars f.hom).map
      (affineCechDescendedModuleHom f hf C.comul ≫ e.hom)
  rw [Functor.map_comp, he]
  exact (affineCechDescendedModuleHom_baseChange_comp f hf C.comul).symm

/-- Before transporting the target by the cover-unit comparison, scalar
extension of the descended counit is exactly the evaluated counit morphism. -/
theorem descendedCounit_baseChange_raw :
    (affineCechDescendedModuleBaseChangeIso f hf C.obj).hom ≫
        (AffineCechModuleDescentData.evaluation f).map C.counit =
      (ModuleCat.extendScalars f.hom).map C.descendedCounit := by
  let M := affineCechDescendedModule f hf C.obj
  let X := ModuleCat.of R R
  let U := affineCechSelectedTensorUnitDescentData f
  let DA : ModuleCat A :=
    (AffineCechModuleDescentData.evaluation f).obj C.obj
  let UA : ModuleCat A := (ModuleCat.extendScalars f.hom).obj X
  let e : affineCechDescendedModule f hf U ≅ X :=
    affineCechSelectedTensorUnitDescendedIso f hf
  let bU : (ModuleCat.extendScalars f.hom).obj
      (affineCechDescendedModule f hf U) ≅ UA :=
    affineCechDescendedModuleBaseChangeIso f hf U
  let bC : (ModuleCat.extendScalars f.hom).obj M ≅ DA :=
    affineCechDescendedModuleBaseChangeIso f hf C.obj
  let q : DA ⟶ UA :=
    (AffineCechModuleDescentData.evaluation f).map C.counit
  have he : (ModuleCat.extendScalars f.hom).map e.hom = bU.hom := by
    exact affineCechDescendedComparisonObjIso_hom_baseChange f hf X
  change bC.hom ≫ q =
    (ModuleCat.extendScalars f.hom).map
      (affineCechDescendedModuleHom f hf C.counit ≫ e.hom)
  rw [Functor.map_comp, he]
  exact (affineCechDescendedModuleHom_baseChange_comp f hf C.counit).symm

/-- Scalar extension of the descended comultiplication recovers the ordinary
cover comultiplication through the selected tensor comparison. -/
theorem descendedComul_baseChange :
    (affineCechDescendedModuleBaseChangeIso f hf C.obj).hom ≫
        C.coverComul =
      (ModuleCat.extendScalars f.hom).map C.descendedComul ≫
        (affineCechDescendedTensorBaseChangeIso f hf C.obj C.obj).hom := by
  let b := affineCechDescendedModuleBaseChangeIso f hf C.obj
  let q := (AffineCechModuleDescentData.evaluation f).map C.comul
  let c := affineCechSelectedTensorDescentDataCoverIso f hf C.obj C.obj
  have h := C.descendedComul_baseChange_raw
  change b.hom ≫ q =
    (ModuleCat.extendScalars f.hom).map C.descendedComul at h
  change (b.hom ≫ q) ≫ c.hom =
    (ModuleCat.extendScalars f.hom).map C.descendedComul ≫ c.hom
  rw [h]
  rfl

/-- Scalar extension of the descended counit recovers the ordinary cover
counit through the selected tensor-unit comparison. -/
theorem descendedCounit_baseChange :
    (affineCechDescendedModuleBaseChangeIso f hf C.obj).hom ≫
        C.coverCounit =
      (ModuleCat.extendScalars f.hom).map C.descendedCounit ≫
        (affineCechSelectedTensorUnitCoverIso f).hom := by
  let b := affineCechDescendedModuleBaseChangeIso f hf C.obj
  let q := (AffineCechModuleDescentData.evaluation f).map C.counit
  let c := affineCechSelectedTensorUnitCoverIso f
  have h := C.descendedCounit_baseChange_raw
  change b.hom ≫ q =
    (ModuleCat.extendScalars f.hom).map C.descendedCounit at h
  change (b.hom ≫ q) ≫ c.hom =
    (ModuleCat.extendScalars f.hom).map C.descendedCounit ≫ c.hom
  rw [h]
  rfl


/-- The descended comultiplication is coassociative with respect to the
ordinary tensor-product associator over the base ring. -/
theorem descendedComul_assoc :
    let M := affineCechDescendedModule f hf C.obj
    C.descendedComul ≫
          ModuleCat.ofHom
            (TensorProduct.map
              (ModuleCat.Hom.hom C.descendedComul) LinearMap.id) ≫
          (TensorProduct.assoc R M M M).toModuleIso.hom =
      C.descendedComul ≫
        ModuleCat.ofHom
          (TensorProduct.map LinearMap.id
            (ModuleCat.Hom.hom C.descendedComul)) := by
  dsimp only
  let M := affineCechDescendedModule f hf C.obj
  let T := affineCechSelectedTensorDescentData f hf C.obj C.obj
  let eT := affineCechSelectedTensorDescendedIso f hf C.obj C.obj
  let eL := affineCechSelectedTensorDescendedIso f hf T C.obj
  let eR := affineCechSelectedTensorDescendedIso f hf C.obj T
  let aB := affineCechSelectedTensorAssociatorBaseIso
    f hf C.obj C.obj C.obj
  let δ₀ := affineCechDescendedModuleHom f hf C.comul
  let tL := affineCechDescendedTensorMap f hf C.comul (𝟙 C.obj)
  let tR := affineCechDescendedTensorMap f hf (𝟙 C.obj) C.comul
  let pL := ModuleCat.ofHom
    (TensorProduct.map (ModuleCat.Hom.hom eT.hom)
      (LinearMap.id : M →ₗ[R] M))
  let pR := ModuleCat.ofHom
    (TensorProduct.map (LinearMap.id : M →ₗ[R] M)
      (ModuleCat.Hom.hom eT.hom))
  let dL := ModuleCat.ofHom
    (TensorProduct.map (ModuleCat.Hom.hom C.descendedComul)
      (LinearMap.id : M →ₗ[R] M))
  let dR := ModuleCat.ofHom
    (TensorProduct.map (LinearMap.id : M →ₗ[R] M)
      (ModuleCat.Hom.hom C.descendedComul))
  let a := (TensorProduct.assoc R M M M).toModuleIso.hom
  have htensor_left :
      affineCechDescendedModuleHom f hf
          (affineCechSelectedTensorMap f hf C.comul (𝟙 C.obj)) =
        eT.hom ≫ tL ≫ eL.inv := by
    exact affineCechDescendedModuleHom_of_comparison_map f hf
      (affineCechDescendedTensorMap f hf C.comul (𝟙 C.obj))
  have htensor_right :
      affineCechDescendedModuleHom f hf
          (affineCechSelectedTensorMap f hf (𝟙 C.obj) C.comul) =
        eT.hom ≫ tR ≫ eR.inv := by
    exact affineCechDescendedModuleHom_of_comparison_map f hf
      (affineCechDescendedTensorMap f hf (𝟙 C.obj) C.comul)
  have h := congrArg
    (fun q => affineCechDescendedModuleHom f hf q) C.comul_assoc
  simp only [affineCechDescendedModuleHom_comp] at h
  rw [htensor_left, htensor_right,
    affineCechDescendedModuleHom_associatorIso_hom] at h
  dsimp [eL, eR, T] at h
  have hbase :
      δ₀ ≫ eT.hom ≫ tL ≫ aB.hom =
        δ₀ ≫ eT.hom ≫ tR := by
    apply (cancel_mono eR.inv).1
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h
  have hassoc : aB.hom ≫ pR = pL ≫ a := by
    dsimp [aB, pR, pL, a]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul q p =>
        rw [← eT.hom_inv_id_apply q]
        generalize eT.hom q = w
        induction w using TensorProduct.induction_on with
        | zero => simp only [TensorProduct.zero_tmul, map_zero]
        | tmul m n =>
            simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
            rw [affineCechSelectedTensorAssociatorBaseIso_hom_tmul]
            change
              m ⊗ₜ[R] eT.hom (eT.inv (n ⊗ₜ[R] p)) =
                (TensorProduct.assoc R M M M)
                  (eT.hom (eT.inv (m ⊗ₜ[R] n)) ⊗ₜ[R] p)
            rw [eT.inv_hom_id_apply, eT.inv_hom_id_apply,
              TensorProduct.assoc_tmul]
        | add x y hx hy =>
            simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hmap_left : tL ≫ pL = dL := by
    dsimp [tL, pL, dL]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
          affineCechDescendedTensorMap, affineCechDescendedModuleHom_id]
        change
          (TensorProduct.map (ModuleCat.Hom.hom eT.hom)
              (LinearMap.id : M →ₗ[R] M))
              ((TensorProduct.map (ModuleCat.Hom.hom δ₀)
                (LinearMap.id : M →ₗ[R] M)) (x ⊗ₜ[R] y)) =
            (TensorProduct.map
                (ModuleCat.Hom.hom (δ₀ ≫ eT.hom))
                (LinearMap.id : M →ₗ[R] M)) (x ⊗ₜ[R] y)
        rw [TensorProduct.map_tmul, TensorProduct.map_tmul,
          TensorProduct.map_tmul]
        simp only [LinearMap.id_apply, ModuleCat.hom_comp,
          LinearMap.comp_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hmap_right : tR ≫ pR = dR := by
    dsimp [tR, pR, dR]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
          affineCechDescendedTensorMap, affineCechDescendedModuleHom_id]
        change
          (TensorProduct.map (LinearMap.id : M →ₗ[R] M)
              (ModuleCat.Hom.hom eT.hom))
              ((TensorProduct.map (LinearMap.id : M →ₗ[R] M)
                (ModuleCat.Hom.hom δ₀)) (x ⊗ₜ[R] y)) =
            (TensorProduct.map (LinearMap.id : M →ₗ[R] M)
                (ModuleCat.Hom.hom (δ₀ ≫ eT.hom)))
              (x ⊗ₜ[R] y)
        rw [TensorProduct.map_tmul, TensorProduct.map_tmul,
          TensorProduct.map_tmul]
        simp only [LinearMap.id_apply, ModuleCat.hom_comp,
          LinearMap.comp_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hmap_left_assoc : tL ≫ pL ≫ a = dL ≫ a := by
    rw [← Category.assoc, hmap_left]
  have hpost := congrArg (fun q => q ≫ pR) hbase
  change (δ₀ ≫ eT.hom) ≫ dL ≫ a =
    (δ₀ ≫ eT.hom) ≫ dR
  simpa only [Category.assoc, hassoc, hmap_left_assoc, hmap_right] using hpost

/-- The descended counit satisfies the ordinary left-counit equation. -/
theorem descendedCounit_left :
    let M := affineCechDescendedModule f hf C.obj
    C.descendedComul ≫
          ModuleCat.ofHom
            (TensorProduct.map
              (ModuleCat.Hom.hom C.descendedCounit) LinearMap.id) ≫
          (TensorProduct.lid R M).toModuleIso.hom =
      𝟙 M := by
  dsimp only
  let M := affineCechDescendedModule f hf C.obj
  let U := affineCechSelectedTensorUnitDescentData f
  let eU := affineCechSelectedTensorUnitDescendedIso f hf
  let eT := affineCechSelectedTensorDescendedIso f hf C.obj C.obj
  let eL := affineCechSelectedTensorDescendedIso f hf U C.obj
  let lB := affineCechSelectedTensorLeftUnitorBaseIso f hf C.obj
  let δ₀ := affineCechDescendedModuleHom f hf C.comul
  let ε₀ := affineCechDescendedModuleHom f hf C.counit
  have htensor :
      affineCechDescendedModuleHom f hf
          (affineCechSelectedTensorMap f hf C.counit (𝟙 C.obj)) =
        eT.hom ≫
          affineCechDescendedTensorMap f hf C.counit (𝟙 C.obj) ≫ eL.inv := by
    exact affineCechDescendedModuleHom_of_comparison_map f hf
      (affineCechDescendedTensorMap f hf C.counit (𝟙 C.obj))
  have h := congrArg
    (fun q => affineCechDescendedModuleHom f hf q) C.counit_left
  simp only [affineCechDescendedModuleHom_comp] at h
  rw [htensor, affineCechDescendedModuleHom_leftUnitorIso_hom] at h
  dsimp [eL, U] at h
  have hbase :
      δ₀ ≫ eT.hom ≫
          affineCechDescendedTensorMap f hf C.counit (𝟙 C.obj) ≫
          lB.hom =
        𝟙 M := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc,
      affineCechDescendedModuleHom_id] using h
  have hcompare (z : TensorProduct R M M) :
      (TensorProduct.lid R M)
          (TensorProduct.map (ModuleCat.Hom.hom (ε₀ ≫ eU.hom))
            LinearMap.id z) =
        lB.hom
          (TensorProduct.map (ModuleCat.Hom.hom ε₀) LinearMap.id z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
        change
          eU.hom (ε₀ x) • y =
            (TensorProduct.lid R M)
              ((TensorProduct.congr eU.toLinearEquiv
                (LinearEquiv.refl R M)) (ε₀ x ⊗ₜ[R] y))
        rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply,
          TensorProduct.lid_tmul]
        rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  have hp := congrArg (fun q => ModuleCat.Hom.hom q m) hbase
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hp
  simp only [affineCechDescendedTensorMap] at hp
  rw [affineCechDescendedModuleHom_id] at hp
  change
    lB.hom
      (TensorProduct.map (ModuleCat.Hom.hom ε₀) LinearMap.id
        (eT.hom (δ₀ m))) = m at hp
  change
    (TensorProduct.lid R M)
      (TensorProduct.map (ModuleCat.Hom.hom (ε₀ ≫ eU.hom)) LinearMap.id
        (eT.hom (δ₀ m))) = m
  rw [hcompare]
  exact hp

/-- The descended counit satisfies the ordinary right-counit equation. -/
theorem descendedCounit_right :
    let M := affineCechDescendedModule f hf C.obj
    C.descendedComul ≫
          ModuleCat.ofHom
            (TensorProduct.map LinearMap.id
              (ModuleCat.Hom.hom C.descendedCounit)) ≫
          (TensorProduct.rid R M).toModuleIso.hom =
      𝟙 M := by
  dsimp only
  let M := affineCechDescendedModule f hf C.obj
  let U := affineCechSelectedTensorUnitDescentData f
  let eU := affineCechSelectedTensorUnitDescendedIso f hf
  let eT := affineCechSelectedTensorDescendedIso f hf C.obj C.obj
  let eR := affineCechSelectedTensorDescendedIso f hf C.obj U
  let rB := affineCechSelectedTensorRightUnitorBaseIso f hf C.obj
  let δ₀ := affineCechDescendedModuleHom f hf C.comul
  let ε₀ := affineCechDescendedModuleHom f hf C.counit
  have htensor :
      affineCechDescendedModuleHom f hf
          (affineCechSelectedTensorMap f hf (𝟙 C.obj) C.counit) =
        eT.hom ≫
          affineCechDescendedTensorMap f hf (𝟙 C.obj) C.counit ≫ eR.inv := by
    exact affineCechDescendedModuleHom_of_comparison_map f hf
      (affineCechDescendedTensorMap f hf (𝟙 C.obj) C.counit)
  have h := congrArg
    (fun q => affineCechDescendedModuleHom f hf q) C.counit_right
  simp only [affineCechDescendedModuleHom_comp] at h
  rw [htensor, affineCechDescendedModuleHom_rightUnitorIso_hom] at h
  dsimp [eR, U] at h
  have hbase :
      δ₀ ≫ eT.hom ≫
          affineCechDescendedTensorMap f hf (𝟙 C.obj) C.counit ≫
          rB.hom =
        𝟙 M := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc,
      affineCechDescendedModuleHom_id] using h
  have hcompare (z : TensorProduct R M M) :
      (TensorProduct.rid R M)
          (TensorProduct.map LinearMap.id
            (ModuleCat.Hom.hom (ε₀ ≫ eU.hom)) z) =
        rB.hom
          (TensorProduct.map LinearMap.id (ModuleCat.Hom.hom ε₀) z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
        change
          eU.hom (ε₀ y) • x =
            (TensorProduct.rid R M)
              ((TensorProduct.congr (LinearEquiv.refl R M)
                eU.toLinearEquiv) (x ⊗ₜ[R] ε₀ y))
        rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply,
          TensorProduct.rid_tmul]
        rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  have hp := congrArg (fun q => ModuleCat.Hom.hom q m) hbase
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hp
  simp only [affineCechDescendedTensorMap] at hp
  rw [affineCechDescendedModuleHom_id] at hp
  change
    rB.hom
      (TensorProduct.map LinearMap.id (ModuleCat.Hom.hom ε₀)
        (eT.hom (δ₀ m))) = m at hp
  change
    (TensorProduct.rid R M)
      (TensorProduct.map LinearMap.id
        (ModuleCat.Hom.hom (ε₀ ≫ eU.hom))
        (eT.hom (δ₀ m))) = m
  rw [hcompare]
  exact hp

end AffineCechSelectedCoalgebraObject

namespace AffineCechSelectedCocommCoalgebraObject

variable {R A : CommRingCat.{u}} {f : R ⟶ A}
variable {hf : f.hom.FaithfullyFlat}
variable (C : AffineCechSelectedCocommCoalgebraObject f hf)

/-- A cocommutative selected coalgebra object descends to a comultiplication
invariant under the ordinary tensor swap over the base ring. -/
theorem descendedComul_comm :
    let M := affineCechDescendedModule f hf C.obj
    C.toAffineCechSelectedCoalgebraObject.descendedComul ≫
        (TensorProduct.comm R M M).toModuleIso.hom =
      C.toAffineCechSelectedCoalgebraObject.descendedComul := by
  dsimp only
  let B := C.toAffineCechSelectedCoalgebraObject
  let eT := affineCechSelectedTensorDescendedIso f hf B.obj B.obj
  let deltaZero := affineCechDescendedModuleHom f hf B.comul
  have h := congrArg
    (fun q => affineCechDescendedModuleHom f hf q) C.comul_comm
  simp only [affineCechDescendedModuleHom_comp] at h
  rw [affineCechDescendedModuleHom_symmetryIso_hom] at h
  change
    deltaZero ≫ eT.hom ≫
        (affineCechSelectedTensorSymmetryBaseIso
          f hf B.obj B.obj).hom ≫ eT.inv =
      deltaZero at h
  change
    deltaZero ≫ eT.hom ≫
        (affineCechSelectedTensorSymmetryBaseIso
          f hf B.obj B.obj).hom =
      deltaZero ≫ eT.hom
  apply (cancel_mono eT.inv).1
  simpa only [Category.assoc, eT.hom_inv_id, Category.comp_id] using h

end AffineCechSelectedCocommCoalgebraObject

end RiemannResearch.AlgebraicGeometry
