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
It also transports cocommutativity to the ordinary tensor swap on the selected
descended base module.

Coassociativity and the two counit equations are retained as honest fields of
the selected coalgebra datum. Their transport to the ordinary base tensor
product, followed by bialgebra compatibility and antipode descent, remains a
separate next layer.

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
