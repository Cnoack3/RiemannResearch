/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.AffineCechModuleTensorDescent

/-!
# Algebra objects in affine Čech module descent

For a faithfully flat affine cover, the selected tensor product, tensor unit,
associator, unitors, and symmetry constructed in
AffineCechModuleTensorDescent can be used to formulate associative algebra
objects directly in the category of chosen Čech module descent data.

This file packages associative, unital, and commutative selected algebra
objects; descends their multiplication and unit to the selected base module;
proves exact scalar-extension formulas recovering the cover maps; and proves
the ordinary tensor-product associativity, left-unit, right-unit, and
commutativity equations for the descended base maps.

No monoidal typeclass instance is required. Coalgebra, bialgebra, antipode,
Hopf-algebra, affine-group-scheme, torsor, and Serre-II assembly remain
separate layers.

Source: user-provided affine Čech descent program; the formal proof transports
the algebra-object axioms through the previously verified selected symmetric
tensor coherence.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory

namespace RiemannResearch.AlgebraicGeometry

/-- An associative unital algebra object for the selected tensor structure on
affine Čech module descent data. -/
structure AffineCechSelectedAlgebraObject
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat) where
  obj : AffineCechModuleDescentData f
  mul :
    affineCechSelectedTensorDescentData f hf obj obj ⟶ obj
  unit :
    affineCechSelectedTensorUnitDescentData f ⟶ obj
  mul_assoc :
    (affineCechSelectedTensorAssociatorIso f hf obj obj obj).hom ≫
          affineCechSelectedTensorMap f hf (𝟙 obj) mul ≫ mul =
      affineCechSelectedTensorMap f hf mul (𝟙 obj) ≫ mul
  unit_mul :
    affineCechSelectedTensorMap f hf unit (𝟙 obj) ≫ mul =
      (affineCechSelectedTensorLeftUnitorIso f hf obj).hom
  mul_unit :
    affineCechSelectedTensorMap f hf (𝟙 obj) unit ≫ mul =
      (affineCechSelectedTensorRightUnitorIso f hf obj).hom

/-- A commutative algebra object for the selected symmetric tensor structure
on affine Čech module descent data. -/
structure AffineCechSelectedCommAlgebraObject
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    extends AffineCechSelectedAlgebraObject f hf where
  mul_comm :
    (affineCechSelectedTensorSymmetryIso f hf
          toAffineCechSelectedAlgebraObject.obj
          toAffineCechSelectedAlgebraObject.obj).hom ≫
        toAffineCechSelectedAlgebraObject.mul =
      toAffineCechSelectedAlgebraObject.mul

namespace AffineCechSelectedAlgebraObject

variable {R A : CommRingCat.{u}} {f : R ⟶ A}
variable {hf : f.hom.FaithfullyFlat}
variable (B : AffineCechSelectedAlgebraObject f hf)

/-- Multiplication on the selected descended base module. -/
noncomputable def descendedMul :
    ModuleCat.of R
        (TensorProduct R
          (affineCechDescendedModule f hf B.obj)
          (affineCechDescendedModule f hf B.obj)) ⟶
      affineCechDescendedModule f hf B.obj :=
  (affineCechSelectedTensorDescendedIso f hf B.obj B.obj).inv ≫
    affineCechDescendedModuleHom f hf B.mul

/-- Unit on the selected descended base module. -/
noncomputable def descendedUnit :
    ModuleCat.of R R ⟶ affineCechDescendedModule f hf B.obj :=
  (affineCechSelectedTensorUnitDescendedIso f hf).inv ≫
    affineCechDescendedModuleHom f hf B.unit

/-- Multiplication on the cover module, expressed on the ordinary tensor
product of the cover object with itself. -/
noncomputable def coverMul :
    ModuleCat.of A
        (TensorProduct A
          ((AffineCechModuleDescentData.evaluation f).obj B.obj)
          ((AffineCechModuleDescentData.evaluation f).obj B.obj)) ⟶
      (AffineCechModuleDescentData.evaluation f).obj B.obj :=
  (affineCechSelectedTensorDescentDataCoverIso f hf B.obj B.obj).inv ≫
    (AffineCechModuleDescentData.evaluation f).map B.mul

/-- Unit on the cover module, expressed from the regular cover module. -/
noncomputable def coverUnit :
    ModuleCat.of A A ⟶
      (AffineCechModuleDescentData.evaluation f).obj B.obj :=
  (affineCechSelectedTensorUnitCoverIso f).inv ≫
    (AffineCechModuleDescentData.evaluation f).map B.unit

/-- Before transporting the source by the cover tensor comparison, scalar
extension of the descended multiplication is exactly the evaluated
multiplication morphism. -/
theorem descendedMul_baseChange_raw :
    (ModuleCat.extendScalars f.hom).map B.descendedMul ≫
        (affineCechDescendedModuleBaseChangeIso f hf B.obj).hom =
      (AffineCechModuleDescentData.evaluation f).map B.mul := by
  let M := affineCechDescendedModule f hf B.obj
  let X := ModuleCat.of R (TensorProduct R M M)
  let T := affineCechSelectedTensorDescentData f hf B.obj B.obj
  let DA : ModuleCat A :=
    (AffineCechModuleDescentData.evaluation f).obj B.obj
  let TA : ModuleCat A := (ModuleCat.extendScalars f.hom).obj X
  let e : affineCechDescendedModule f hf T ≅ X :=
    affineCechSelectedTensorDescendedIso f hf B.obj B.obj
  let bT : (ModuleCat.extendScalars f.hom).obj
      (affineCechDescendedModule f hf T) ≅ TA :=
    affineCechDescendedModuleBaseChangeIso f hf T
  let bB : (ModuleCat.extendScalars f.hom).obj M ≅ DA :=
    affineCechDescendedModuleBaseChangeIso f hf B.obj
  let q : TA ⟶ DA :=
    (AffineCechModuleDescentData.evaluation f).map B.mul
  change
    (ModuleCat.extendScalars f.hom).map
        (e.inv ≫ affineCechDescendedModuleHom f hf B.mul) ≫ bB.hom = q
  rw [Functor.map_comp, Category.assoc]
  change
    (ModuleCat.extendScalars f.hom).map e.inv ≫
      ((ModuleCat.extendScalars f.hom).map
          (affineCechDescendedModuleHom f hf B.mul) ≫
        (affineCechDescendedModuleBaseChangeIso f hf B.obj).hom) = q
  rw [affineCechDescendedModuleHom_baseChange_comp]
  change (ModuleCat.extendScalars f.hom).map e.inv ≫ bT.hom ≫ q = q
  change
    (ModuleCat.extendScalars f.hom).map
        (affineCechDescendedComparisonObjIso f hf X).inv ≫ bT.hom ≫ q = q
  rw [affineCechDescendedComparisonObjIso_inv_baseChange]
  exact bT.inv_hom_id_assoc q

/-- Before transporting the source by the cover-unit comparison, scalar
extension of the descended unit is exactly the evaluated unit morphism. -/
theorem descendedUnit_baseChange_raw :
    (ModuleCat.extendScalars f.hom).map B.descendedUnit ≫
        (affineCechDescendedModuleBaseChangeIso f hf B.obj).hom =
      (AffineCechModuleDescentData.evaluation f).map B.unit := by
  let M := affineCechDescendedModule f hf B.obj
  let X := ModuleCat.of R R
  let U := affineCechSelectedTensorUnitDescentData f
  let DA : ModuleCat A :=
    (AffineCechModuleDescentData.evaluation f).obj B.obj
  let UA : ModuleCat A := (ModuleCat.extendScalars f.hom).obj X
  let e : affineCechDescendedModule f hf U ≅ X :=
    affineCechSelectedTensorUnitDescendedIso f hf
  let bU : (ModuleCat.extendScalars f.hom).obj
      (affineCechDescendedModule f hf U) ≅ UA :=
    affineCechDescendedModuleBaseChangeIso f hf U
  let bB : (ModuleCat.extendScalars f.hom).obj M ≅ DA :=
    affineCechDescendedModuleBaseChangeIso f hf B.obj
  let q : UA ⟶ DA :=
    (AffineCechModuleDescentData.evaluation f).map B.unit
  change
    (ModuleCat.extendScalars f.hom).map
        (e.inv ≫ affineCechDescendedModuleHom f hf B.unit) ≫ bB.hom = q
  rw [Functor.map_comp, Category.assoc]
  change
    (ModuleCat.extendScalars f.hom).map e.inv ≫
      ((ModuleCat.extendScalars f.hom).map
          (affineCechDescendedModuleHom f hf B.unit) ≫
        (affineCechDescendedModuleBaseChangeIso f hf B.obj).hom) = q
  rw [affineCechDescendedModuleHom_baseChange_comp]
  change (ModuleCat.extendScalars f.hom).map e.inv ≫ bU.hom ≫ q = q
  change
    (ModuleCat.extendScalars f.hom).map
        (affineCechDescendedComparisonObjIso f hf X).inv ≫ bU.hom ≫ q = q
  rw [affineCechDescendedComparisonObjIso_inv_baseChange]
  exact bU.inv_hom_id_assoc q

/-- The cover tensor comparison followed by coverMul is the original
evaluated multiplication morphism. -/
theorem coverMul_comparison :
    (affineCechSelectedTensorDescentDataCoverIso
          f hf B.obj B.obj).hom ≫ B.coverMul =
      (AffineCechModuleDescentData.evaluation f).map B.mul := by
  let c := affineCechSelectedTensorDescentDataCoverIso f hf B.obj B.obj
  let q := (AffineCechModuleDescentData.evaluation f).map B.mul
  change c.hom ≫ c.inv ≫ q = q
  exact c.hom_inv_id_assoc q

/-- The cover-unit comparison followed by coverUnit is the original evaluated
unit morphism. -/
theorem coverUnit_comparison :
    (affineCechSelectedTensorUnitCoverIso f).hom ≫ B.coverUnit =
      (AffineCechModuleDescentData.evaluation f).map B.unit := by
  let c := affineCechSelectedTensorUnitCoverIso f
  let q := (AffineCechModuleDescentData.evaluation f).map B.unit
  change c.hom ≫ c.inv ≫ q = q
  exact c.hom_inv_id_assoc q

/-- After the ordinary cover tensor comparison, scalar extension of the
descended multiplication recovers coverMul. -/
theorem descendedMul_baseChange :
    (ModuleCat.extendScalars f.hom).map B.descendedMul ≫
        (affineCechDescendedModuleBaseChangeIso f hf B.obj).hom =
      (affineCechDescendedTensorBaseChangeIso f hf B.obj B.obj).hom ≫
        B.coverMul := by
  rw [B.descendedMul_baseChange_raw]
  exact B.coverMul_comparison.symm

/-- After the cover-unit comparison, scalar extension of the descended unit
recovers coverUnit. -/
theorem descendedUnit_baseChange :
    (ModuleCat.extendScalars f.hom).map B.descendedUnit ≫
        (affineCechDescendedModuleBaseChangeIso f hf B.obj).hom =
      (affineCechSelectedTensorUnitCoverIso f).hom ≫ B.coverUnit := by
  rw [B.descendedUnit_baseChange_raw]
  exact B.coverUnit_comparison.symm

/-- The descended multiplication is associative with respect to the ordinary
tensor-product associator over the base ring. -/
theorem descendedMul_assoc :
    let M := affineCechDescendedModule f hf B.obj
    (TensorProduct.assoc R M M M).toModuleIso.hom ≫
          ModuleCat.ofHom
            (TensorProduct.map LinearMap.id
              (ModuleCat.Hom.hom B.descendedMul)) ≫
          B.descendedMul =
      ModuleCat.ofHom
            (TensorProduct.map
              (ModuleCat.Hom.hom B.descendedMul) LinearMap.id) ≫
          B.descendedMul := by
  dsimp only
  let T := affineCechSelectedTensorDescentData f hf B.obj B.obj
  let eT := affineCechSelectedTensorDescendedIso f hf B.obj B.obj
  let eL := affineCechSelectedTensorDescendedIso f hf T B.obj
  let eR := affineCechSelectedTensorDescendedIso f hf B.obj T
  let μ₀ := affineCechDescendedModuleHom f hf B.mul
  have hleft :
      affineCechDescendedModuleHom f hf
          (affineCechSelectedTensorMap f hf (𝟙 B.obj) B.mul) =
        eR.hom ≫
          affineCechDescendedTensorMap f hf (𝟙 B.obj) B.mul ≫ eT.inv := by
    exact affineCechDescendedModuleHom_of_comparison_map f hf
      (affineCechDescendedTensorMap f hf (𝟙 B.obj) B.mul)
  have hright :
      affineCechDescendedModuleHom f hf
          (affineCechSelectedTensorMap f hf B.mul (𝟙 B.obj)) =
        eL.hom ≫
          affineCechDescendedTensorMap f hf B.mul (𝟙 B.obj) ≫ eT.inv := by
    exact affineCechDescendedModuleHom_of_comparison_map f hf
      (affineCechDescendedTensorMap f hf B.mul (𝟙 B.obj))
  have h := congrArg
    (fun q => affineCechDescendedModuleHom f hf q) B.mul_assoc
  simp only [affineCechDescendedModuleHom_comp] at h
  rw [affineCechDescendedModuleHom_associatorIso_hom, hleft, hright] at h
  change
    (eL.hom ≫
          (affineCechSelectedTensorAssociatorBaseIso
            f hf B.obj B.obj B.obj).hom ≫
          eR.inv) ≫
        (eR.hom ≫
          affineCechDescendedTensorMap f hf (𝟙 B.obj) B.mul ≫ eT.inv) ≫
        μ₀ =
      (eL.hom ≫
          affineCechDescendedTensorMap f hf B.mul (𝟙 B.obj) ≫ eT.inv) ≫
        μ₀ at h
  have hbase := congrArg (fun q => eL.inv ≫ q) h
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at hbase
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul mn p =>
      induction mn using TensorProduct.induction_on with
      | zero => simp only [TensorProduct.zero_tmul, map_zero]
      | tmul m n =>
          have hp := congrArg
            (fun q => ModuleCat.Hom.hom q
              (ModuleCat.Hom.hom eT.inv (m ⊗ₜ[R] n) ⊗ₜ[R] p)) hbase
          simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hp
          rw [affineCechSelectedTensorAssociatorBaseIso_hom_tmul] at hp
          simp only [affineCechDescendedTensorMap] at hp
          rw [affineCechDescendedModuleHom_id] at hp
          change
            ModuleCat.Hom.hom μ₀
                (ModuleCat.Hom.hom eT.inv
                  (m ⊗ₜ[R]
                    ModuleCat.Hom.hom μ₀
                      (ModuleCat.Hom.hom eT.inv (n ⊗ₜ[R] p)))) =
              ModuleCat.Hom.hom μ₀
                (ModuleCat.Hom.hom eT.inv
                  (ModuleCat.Hom.hom μ₀
                    (ModuleCat.Hom.hom eT.inv (m ⊗ₜ[R] n)) ⊗ₜ[R] p)) at hp
          change
            ModuleCat.Hom.hom μ₀
                (ModuleCat.Hom.hom eT.inv
                  (m ⊗ₜ[R]
                    ModuleCat.Hom.hom μ₀
                      (ModuleCat.Hom.hom eT.inv (n ⊗ₜ[R] p)))) =
              ModuleCat.Hom.hom μ₀
                (ModuleCat.Hom.hom eT.inv
                  (ModuleCat.Hom.hom μ₀
                    (ModuleCat.Hom.hom eT.inv (m ⊗ₜ[R] n)) ⊗ₜ[R] p))
          simpa only [descendedMul, ModuleCat.hom_comp, LinearMap.comp_apply,
            ModuleCat.ofHom_apply, TensorProduct.assoc_tmul,
            TensorProduct.map_tmul, LinearMap.id_apply] using hp
      | add x y hx hy =>
          simp only [TensorProduct.add_tmul, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The descended unit is a left unit for the descended multiplication. -/
theorem descendedUnit_mul :
    let M := affineCechDescendedModule f hf B.obj
    ModuleCat.ofHom
          (TensorProduct.map
            (ModuleCat.Hom.hom B.descendedUnit) LinearMap.id) ≫
        B.descendedMul =
      (TensorProduct.lid R M).toModuleIso.hom := by
  dsimp only
  let U := affineCechSelectedTensorUnitDescentData f
  let eU := affineCechSelectedTensorUnitDescendedIso f hf
  let eT := affineCechSelectedTensorDescendedIso f hf B.obj B.obj
  let eL := affineCechSelectedTensorDescendedIso f hf U B.obj
  let μ₀ := affineCechDescendedModuleHom f hf B.mul
  let η₀ := affineCechDescendedModuleHom f hf B.unit
  have htensor :
      affineCechDescendedModuleHom f hf
          (affineCechSelectedTensorMap f hf B.unit (𝟙 B.obj)) =
        eL.hom ≫
          affineCechDescendedTensorMap f hf B.unit (𝟙 B.obj) ≫ eT.inv := by
    exact affineCechDescendedModuleHom_of_comparison_map f hf
      (affineCechDescendedTensorMap f hf B.unit (𝟙 B.obj))
  have h := congrArg
    (fun q => affineCechDescendedModuleHom f hf q) B.unit_mul
  simp only [affineCechDescendedModuleHom_comp] at h
  rw [htensor, affineCechDescendedModuleHom_leftUnitorIso_hom] at h
  change
    (eL.hom ≫
          affineCechDescendedTensorMap f hf B.unit (𝟙 B.obj) ≫ eT.inv) ≫
        μ₀ =
      eL.hom ≫
        (affineCechSelectedTensorLeftUnitorBaseIso f hf B.obj).hom at h
  have hbase := congrArg (fun q => eL.inv ≫ q) h
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at hbase
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul r m =>
      have hp := congrArg
        (fun q => ModuleCat.Hom.hom q (eU.inv r ⊗ₜ[R] m)) hbase
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hp
      simp only [affineCechDescendedTensorMap] at hp
      rw [affineCechDescendedModuleHom_id] at hp
      have hl :
          (affineCechSelectedTensorLeftUnitorBaseIso f hf B.obj).hom
              (eU.inv r ⊗ₜ[R] m) = r • m := by
        change
          (TensorProduct.lid R _)
              ((TensorProduct.congr eU.toLinearEquiv
                (LinearEquiv.refl R _)) (eU.inv r ⊗ₜ[R] m)) = r • m
        rw [TensorProduct.congr_tmul]
        have hc : eU.toLinearEquiv (eU.inv r) = r :=
          eU.inv_hom_id_apply r
        rw [hc, LinearEquiv.refl_apply, TensorProduct.lid_tmul]
      rw [hl] at hp
      change
        ModuleCat.Hom.hom μ₀
            (eT.inv (η₀ (eU.inv r) ⊗ₜ[R] m)) = r • m at hp
      change
        ModuleCat.Hom.hom μ₀
            (eT.inv (η₀ (eU.inv r) ⊗ₜ[R] m)) = r • m
      simpa only [descendedMul, descendedUnit, ModuleCat.hom_comp,
        LinearMap.comp_apply, ModuleCat.ofHom_apply, TensorProduct.map_tmul,
        LinearMap.id_apply, TensorProduct.lid_tmul] using hp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The descended unit is a right unit for the descended multiplication. -/
theorem descendedMul_unit :
    let M := affineCechDescendedModule f hf B.obj
    ModuleCat.ofHom
          (TensorProduct.map LinearMap.id
            (ModuleCat.Hom.hom B.descendedUnit)) ≫
        B.descendedMul =
      (TensorProduct.rid R M).toModuleIso.hom := by
  dsimp only
  let U := affineCechSelectedTensorUnitDescentData f
  let eU := affineCechSelectedTensorUnitDescendedIso f hf
  let eT := affineCechSelectedTensorDescendedIso f hf B.obj B.obj
  let eR := affineCechSelectedTensorDescendedIso f hf B.obj U
  let μ₀ := affineCechDescendedModuleHom f hf B.mul
  let η₀ := affineCechDescendedModuleHom f hf B.unit
  have htensor :
      affineCechDescendedModuleHom f hf
          (affineCechSelectedTensorMap f hf (𝟙 B.obj) B.unit) =
        eR.hom ≫
          affineCechDescendedTensorMap f hf (𝟙 B.obj) B.unit ≫ eT.inv := by
    exact affineCechDescendedModuleHom_of_comparison_map f hf
      (affineCechDescendedTensorMap f hf (𝟙 B.obj) B.unit)
  have h := congrArg
    (fun q => affineCechDescendedModuleHom f hf q) B.mul_unit
  simp only [affineCechDescendedModuleHom_comp] at h
  rw [htensor, affineCechDescendedModuleHom_rightUnitorIso_hom] at h
  change
    (eR.hom ≫
          affineCechDescendedTensorMap f hf (𝟙 B.obj) B.unit ≫ eT.inv) ≫
        μ₀ =
      eR.hom ≫
        (affineCechSelectedTensorRightUnitorBaseIso f hf B.obj).hom at h
  have hbase := congrArg (fun q => eR.inv ≫ q) h
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at hbase
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul m r =>
      have hp := congrArg
        (fun q => ModuleCat.Hom.hom q (m ⊗ₜ[R] eU.inv r)) hbase
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hp
      simp only [affineCechDescendedTensorMap] at hp
      rw [affineCechDescendedModuleHom_id] at hp
      have hr :
          (affineCechSelectedTensorRightUnitorBaseIso f hf B.obj).hom
              (m ⊗ₜ[R] eU.inv r) = r • m := by
        change
          (TensorProduct.rid R _)
              ((TensorProduct.congr (LinearEquiv.refl R _)
                eU.toLinearEquiv) (m ⊗ₜ[R] eU.inv r)) = r • m
        rw [TensorProduct.congr_tmul]
        have hc : eU.toLinearEquiv (eU.inv r) = r :=
          eU.inv_hom_id_apply r
        rw [hc, LinearEquiv.refl_apply, TensorProduct.rid_tmul]
      rw [hr] at hp
      change
        ModuleCat.Hom.hom μ₀
            (eT.inv (m ⊗ₜ[R] η₀ (eU.inv r))) = r • m at hp
      change
        ModuleCat.Hom.hom μ₀
            (eT.inv (m ⊗ₜ[R] η₀ (eU.inv r))) = r • m
      simpa only [descendedMul, descendedUnit, ModuleCat.hom_comp,
        LinearMap.comp_apply, ModuleCat.ofHom_apply, TensorProduct.map_tmul,
        LinearMap.id_apply, TensorProduct.rid_tmul] using hp
  | add x y hx hy => simp only [map_add, hx, hy]

end AffineCechSelectedAlgebraObject

namespace AffineCechSelectedCommAlgebraObject

variable {R A : CommRingCat.{u}} {f : R ⟶ A}
variable {hf : f.hom.FaithfullyFlat}
variable (B : AffineCechSelectedCommAlgebraObject f hf)

/-- A commutative selected algebra object descends to a multiplication
invariant under the ordinary tensor swap over the base ring. -/
theorem descendedMul_comm :
    let M := affineCechDescendedModule f hf B.obj
    (TensorProduct.comm R M M).toModuleIso.hom ≫
        B.toAffineCechSelectedAlgebraObject.descendedMul =
      B.toAffineCechSelectedAlgebraObject.descendedMul := by
  dsimp only
  let C := B.toAffineCechSelectedAlgebraObject
  let eT := affineCechSelectedTensorDescendedIso f hf C.obj C.obj
  let μ₀ := affineCechDescendedModuleHom f hf C.mul
  have h := congrArg
    (fun q => affineCechDescendedModuleHom f hf q) B.mul_comm
  simp only [affineCechDescendedModuleHom_comp] at h
  rw [affineCechDescendedModuleHom_symmetryIso_hom] at h
  change
    (eT.hom ≫
        (affineCechSelectedTensorSymmetryBaseIso f hf C.obj C.obj).hom ≫
        eT.inv) ≫ μ₀ = μ₀ at h
  have hbase := congrArg (fun q => eT.inv ≫ q) h
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at hbase
  change
    (TensorProduct.comm R
      (affineCechDescendedModule f hf C.obj)
      (affineCechDescendedModule f hf C.obj)).toModuleIso.hom ≫
        (eT.inv ≫ μ₀) = eT.inv ≫ μ₀
  exact hbase

end AffineCechSelectedCommAlgebraObject

end RiemannResearch.AlgebraicGeometry
