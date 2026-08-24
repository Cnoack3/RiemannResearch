/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.AffineCechBialgebraDescent
import Mathlib.Algebra.Category.CoalgCat.ComonEquivalence
import Mathlib.CategoryTheory.Monoidal.Internal.Module
import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# Hopf objects in affine Čech module descent

This file adds an antipode to the selected bialgebra objects for affine Čech
module descent. It descends the antipode to the ordinary base module, proves
its exact recovery after scalar extension, and transports both convolution
identities to the ordinary tensor product over the base ring. A commutative
selected Hopf object is also packaged, with commutativity transported through
the existing algebra-object theorem.

The selected commutative Hopf object is also bundled on the ordinary descended
carrier as a concrete commutative ring, algebra, coalgebra, bialgebra, and Hopf
algebra. Constructing a selected object and identifying its scalar extension
with a prescribed cover Hopf algebra remain specialization-level tasks.

Source: user-provided affine Čech Hopf-descent program; the two identities are
the standard left and right convolution-inverse equations for an antipode.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory

namespace RiemannResearch.AlgebraicGeometry

/-- A Hopf algebra object for the selected symmetric tensor structure on
affine Čech module descent data. The two final fields state that the antipode
is a left and right convolution inverse to the identity. -/
structure AffineCechSelectedHopfAlgebraObject
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    extends AffineCechSelectedBialgebraObject f hf where
  antipode :
    toAffineCechSelectedBialgebraObject.toAffineCechSelectedAlgebraObject.obj ⟶
      toAffineCechSelectedBialgebraObject.toAffineCechSelectedAlgebraObject.obj
  antipode_mul_left :
    toAffineCechSelectedBialgebraObject.comul ≫
        affineCechSelectedTensorMap f hf antipode
          (𝟙 toAffineCechSelectedBialgebraObject.toAffineCechSelectedAlgebraObject.obj) ≫
        toAffineCechSelectedBialgebraObject.toAffineCechSelectedAlgebraObject.mul =
      toAffineCechSelectedBialgebraObject.counit ≫
        toAffineCechSelectedBialgebraObject.toAffineCechSelectedAlgebraObject.unit
  antipode_mul_right :
    toAffineCechSelectedBialgebraObject.comul ≫
        affineCechSelectedTensorMap f hf
          (𝟙 toAffineCechSelectedBialgebraObject.toAffineCechSelectedAlgebraObject.obj)
          antipode ≫
        toAffineCechSelectedBialgebraObject.toAffineCechSelectedAlgebraObject.mul =
      toAffineCechSelectedBialgebraObject.counit ≫
        toAffineCechSelectedBialgebraObject.toAffineCechSelectedAlgebraObject.unit

set_option linter.style.longLine false in
/-- A selected Hopf algebra object whose multiplication is commutative. -/
structure AffineCechSelectedCommHopfAlgebraObject
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    extends AffineCechSelectedHopfAlgebraObject f hf where
  mul_comm :
    (affineCechSelectedTensorSymmetryIso f hf
        toAffineCechSelectedHopfAlgebraObject.toAffineCechSelectedBialgebraObject.toAffineCechSelectedAlgebraObject.obj
        toAffineCechSelectedHopfAlgebraObject.toAffineCechSelectedBialgebraObject.toAffineCechSelectedAlgebraObject.obj).hom ≫
      toAffineCechSelectedHopfAlgebraObject.toAffineCechSelectedBialgebraObject.toAffineCechSelectedAlgebraObject.mul =
    toAffineCechSelectedHopfAlgebraObject.toAffineCechSelectedBialgebraObject.toAffineCechSelectedAlgebraObject.mul

namespace AffineCechSelectedHopfAlgebraObject

variable {R A : CommRingCat.{u}} {f : R ⟶ A}
variable {hf : f.hom.FaithfullyFlat}
variable (H : AffineCechSelectedHopfAlgebraObject f hf)

/-- Antipode on the selected descended base module. -/
noncomputable def descendedAntipode :
    affineCechDescendedModule f hf
        H.toAffineCechSelectedBialgebraObject.toAffineCechSelectedAlgebraObject.obj ⟶
      affineCechDescendedModule f hf
        H.toAffineCechSelectedBialgebraObject.toAffineCechSelectedAlgebraObject.obj :=
  affineCechDescendedModuleHom f hf H.antipode

/-- Antipode on the evaluated cover module. -/
noncomputable def coverAntipode :
    (AffineCechModuleDescentData.evaluation f).obj
        H.toAffineCechSelectedBialgebraObject.toAffineCechSelectedAlgebraObject.obj ⟶
      (AffineCechModuleDescentData.evaluation f).obj
        H.toAffineCechSelectedBialgebraObject.toAffineCechSelectedAlgebraObject.obj :=
  (AffineCechModuleDescentData.evaluation f).map H.antipode

/-- Scalar extension of the descended antipode recovers the evaluated cover
antipode through the selected module base-change comparison. -/
theorem descendedAntipode_baseChange :
    (ModuleCat.extendScalars f.hom).map H.descendedAntipode ≫
        (affineCechDescendedModuleBaseChangeIso f hf
          H.toAffineCechSelectedBialgebraObject.toAffineCechSelectedAlgebraObject.obj).hom =
      (affineCechDescendedModuleBaseChangeIso f hf
          H.toAffineCechSelectedBialgebraObject.toAffineCechSelectedAlgebraObject.obj).hom ≫
        H.coverAntipode := by
  exact affineCechDescendedModuleHom_baseChange_comp f hf H.antipode

/-- The descended antipode is a left convolution inverse to the identity for
the ordinary descended bialgebra operations. -/
theorem descendedAntipode_mul_left :
    H.toAffineCechSelectedBialgebraObject.toAffineCechSelectedCoalgebraObject.descendedComul ≫
        ModuleCat.ofHom
          (TensorProduct.map
            (ModuleCat.Hom.hom H.descendedAntipode)
            LinearMap.id) ≫
        H.toAffineCechSelectedBialgebraObject.toAffineCechSelectedAlgebraObject.descendedMul =
      H.toAffineCechSelectedBialgebraObject.toAffineCechSelectedCoalgebraObject.descendedCounit ≫
        H.toAffineCechSelectedBialgebraObject.toAffineCechSelectedAlgebraObject.descendedUnit := by
  let B := H.toAffineCechSelectedBialgebraObject
  let X := B.toAffineCechSelectedAlgebraObject.obj
  let eT := affineCechSelectedTensorDescendedIso f hf X X
  let eU := affineCechSelectedTensorUnitDescendedIso f hf
  let δ₀ := affineCechDescendedModuleHom f hf B.comul
  let μ₀ := affineCechDescendedModuleHom f hf
    B.toAffineCechSelectedAlgebraObject.mul
  let ε₀ := affineCechDescendedModuleHom f hf B.counit
  let η₀ := affineCechDescendedModuleHom f hf
    B.toAffineCechSelectedAlgebraObject.unit
  let S₀ := affineCechDescendedModuleHom f hf H.antipode
  let t := affineCechDescendedTensorMap f hf H.antipode (𝟙 X)
  have htensor :
      affineCechDescendedModuleHom f hf
          (affineCechSelectedTensorMap f hf H.antipode (𝟙 X)) =
        eT.hom ≫ t ≫ eT.inv := by
    exact affineCechDescendedModuleHom_of_comparison_map f hf t
  have h := congrArg
    (fun q => affineCechDescendedModuleHom f hf q) H.antipode_mul_left
  simp only [affineCechDescendedModuleHom_comp] at h
  rw [htensor] at h
  change δ₀ ≫ eT.hom ≫ t ≫ eT.inv ≫ μ₀ = ε₀ ≫ η₀ at h
  have ht :
      t = ModuleCat.ofHom
        (TensorProduct.map (ModuleCat.Hom.hom S₀) LinearMap.id) := by
    simp only [t, affineCechDescendedTensorMap,
      affineCechDescendedModuleHom_id]
  rw [ht] at h
  change
    (δ₀ ≫ eT.hom) ≫
        ModuleCat.ofHom
          (TensorProduct.map (ModuleCat.Hom.hom S₀) LinearMap.id) ≫
        (eT.inv ≫ μ₀) =
      (ε₀ ≫ eU.hom) ≫ (eU.inv ≫ η₀)
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  simpa only [Category.assoc] using h

/-- The descended antipode is a right convolution inverse to the identity for
the ordinary descended bialgebra operations. -/
theorem descendedAntipode_mul_right :
    H.toAffineCechSelectedBialgebraObject.toAffineCechSelectedCoalgebraObject.descendedComul ≫
        ModuleCat.ofHom
          (TensorProduct.map
            LinearMap.id
            (ModuleCat.Hom.hom H.descendedAntipode)) ≫
        H.toAffineCechSelectedBialgebraObject.toAffineCechSelectedAlgebraObject.descendedMul =
      H.toAffineCechSelectedBialgebraObject.toAffineCechSelectedCoalgebraObject.descendedCounit ≫
        H.toAffineCechSelectedBialgebraObject.toAffineCechSelectedAlgebraObject.descendedUnit := by
  let B := H.toAffineCechSelectedBialgebraObject
  let X := B.toAffineCechSelectedAlgebraObject.obj
  let eT := affineCechSelectedTensorDescendedIso f hf X X
  let eU := affineCechSelectedTensorUnitDescendedIso f hf
  let δ₀ := affineCechDescendedModuleHom f hf B.comul
  let μ₀ := affineCechDescendedModuleHom f hf
    B.toAffineCechSelectedAlgebraObject.mul
  let ε₀ := affineCechDescendedModuleHom f hf B.counit
  let η₀ := affineCechDescendedModuleHom f hf
    B.toAffineCechSelectedAlgebraObject.unit
  let S₀ := affineCechDescendedModuleHom f hf H.antipode
  let t := affineCechDescendedTensorMap f hf (𝟙 X) H.antipode
  have htensor :
      affineCechDescendedModuleHom f hf
          (affineCechSelectedTensorMap f hf (𝟙 X) H.antipode) =
        eT.hom ≫ t ≫ eT.inv := by
    exact affineCechDescendedModuleHom_of_comparison_map f hf t
  have h := congrArg
    (fun q => affineCechDescendedModuleHom f hf q) H.antipode_mul_right
  simp only [affineCechDescendedModuleHom_comp] at h
  rw [htensor] at h
  change δ₀ ≫ eT.hom ≫ t ≫ eT.inv ≫ μ₀ = ε₀ ≫ η₀ at h
  have ht :
      t = ModuleCat.ofHom
        (TensorProduct.map LinearMap.id (ModuleCat.Hom.hom S₀)) := by
    simp only [t, affineCechDescendedTensorMap,
      affineCechDescendedModuleHom_id]
  rw [ht] at h
  change
    (δ₀ ≫ eT.hom) ≫
        ModuleCat.ofHom
          (TensorProduct.map LinearMap.id (ModuleCat.Hom.hom S₀)) ≫
        (eT.inv ≫ μ₀) =
      (ε₀ ≫ eU.hom) ≫ (eU.inv ≫ η₀)
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  simpa only [Category.assoc] using h

end AffineCechSelectedHopfAlgebraObject

namespace AffineCechSelectedCommHopfAlgebraObject

variable {R A : CommRingCat.{u}} {f : R ⟶ A}
variable {hf : f.hom.FaithfullyFlat}

/-- The underlying selected commutative bialgebra object. -/
noncomputable def toAffineCechSelectedCommBialgebraObject
    (H : AffineCechSelectedCommHopfAlgebraObject f hf) :
    AffineCechSelectedCommBialgebraObject f hf where
  toAffineCechSelectedBialgebraObject :=
    H.toAffineCechSelectedHopfAlgebraObject.toAffineCechSelectedBialgebraObject
  mul_comm := H.mul_comm

set_option linter.style.longLine false in
/-- The underlying selected commutative algebra object. -/
noncomputable def toAffineCechSelectedCommAlgebraObject
    (H : AffineCechSelectedCommHopfAlgebraObject f hf) :
    AffineCechSelectedCommAlgebraObject f hf where
  toAffineCechSelectedAlgebraObject :=
    H.toAffineCechSelectedHopfAlgebraObject.toAffineCechSelectedBialgebraObject.toAffineCechSelectedAlgebraObject
  mul_comm := H.mul_comm

set_option linter.style.longLine false in
/-- A selected commutative Hopf object has commutative multiplication after
descent to the ordinary base module. -/
theorem descendedMul_comm
    (H : AffineCechSelectedCommHopfAlgebraObject f hf) :
    let M := affineCechDescendedModule f hf
      H.toAffineCechSelectedHopfAlgebraObject.toAffineCechSelectedBialgebraObject.toAffineCechSelectedAlgebraObject.obj
    (TensorProduct.comm R M M).toModuleIso.hom ≫
        H.toAffineCechSelectedHopfAlgebraObject.toAffineCechSelectedBialgebraObject.toAffineCechSelectedAlgebraObject.descendedMul =
      H.toAffineCechSelectedHopfAlgebraObject.toAffineCechSelectedBialgebraObject.toAffineCechSelectedAlgebraObject.descendedMul := by
  exact H.toAffineCechSelectedCommAlgebraObject.descendedMul_comm

/-- The ordinary descended multiplication and unit form a monoid object in
the standard tensor category of modules over the base ring. -/
@[instance_reducible]
noncomputable def descendedMonObj
    (H : AffineCechSelectedCommHopfAlgebraObject f hf) :
    MonObj (affineCechDescendedModule f hf H.obj) := by
  exact
    { one := H.descendedUnit
      mul := H.descendedMul
      one_mul := H.descendedUnit_mul
      mul_one := H.descendedMul_unit
      mul_assoc := H.descendedMul_assoc.symm }

/-- The ordinary descended comultiplication and counit form a comonoid object
in the standard tensor category of modules over the base ring. -/
@[instance_reducible]
noncomputable def descendedComonObj
    (H : AffineCechSelectedCommHopfAlgebraObject f hf) :
    ComonObj (affineCechDescendedModule f hf H.obj) := by
  let C :=
    H.toAffineCechSelectedHopfAlgebraObject.toAffineCechSelectedBialgebraObject
      |>.toAffineCechSelectedCoalgebraObject
  let M := affineCechDescendedModule f hf C.obj
  exact
    { counit := C.descendedCounit
      comul := C.descendedComul
      counit_comul := by
        apply (cancel_mono (TensorProduct.lid R M).toModuleIso.hom).mp
        change
          C.descendedComul ≫
              ModuleCat.ofHom
                (TensorProduct.map
                  (ModuleCat.Hom.hom C.descendedCounit) LinearMap.id) ≫
              (TensorProduct.lid R M).toModuleIso.hom =
            (TensorProduct.lid R M).toModuleIso.inv ≫
              (TensorProduct.lid R M).toModuleIso.hom
        rw [Iso.inv_hom_id]
        exact C.descendedCounit_left
      comul_counit := by
        apply (cancel_mono (TensorProduct.rid R M).toModuleIso.hom).mp
        change
          C.descendedComul ≫
              ModuleCat.ofHom
                (TensorProduct.map
                  LinearMap.id (ModuleCat.Hom.hom C.descendedCounit)) ≫
              (TensorProduct.rid R M).toModuleIso.hom =
            (TensorProduct.rid R M).toModuleIso.inv ≫
              (TensorProduct.rid R M).toModuleIso.hom
        rw [Iso.inv_hom_id]
        exact C.descendedCounit_right
      comul_assoc := C.descendedComul_assoc.symm }

/-- Commutative ring structure on the carrier selected by affine Čech module
descent. Its multiplication and unit are definitionally the descended maps. -/
@[instance_reducible]
noncomputable def descendedCommRing
    (H : AffineCechSelectedCommHopfAlgebraObject f hf) :
    CommRing (affineCechDescendedModule f hf H.obj) := by
  let M := affineCechDescendedModule f hf H.obj
  letI : MonObj M := H.descendedMonObj
  letI : Ring M :=
    ModuleCat.MonModuleEquivalenceAlgebra.MonObj.toRing M
  apply CommRing.mk
  intro x y
  change
    (ModuleCat.Hom.hom H.descendedMul) (x ⊗ₜ[R] y) =
      (ModuleCat.Hom.hom H.descendedMul) (y ⊗ₜ[R] x)
  have h := congrArg
    (fun q => (ModuleCat.Hom.hom q) (x ⊗ₜ[R] y))
    H.descendedMul_comm
  simpa using h.symm

/-- Base-algebra structure on the descended commutative ring. Its algebra map
is definitionally the descended unit map. -/
@[instance_reducible]
noncomputable def descendedAlgebra
    (H : AffineCechSelectedCommHopfAlgebraObject f hf) :
    let M := affineCechDescendedModule f hf H.obj
    let _ : CommRing M := H.descendedCommRing
    Algebra R M := by
  dsimp only
  let M := affineCechDescendedModule f hf H.obj
  letI : MonObj M := H.descendedMonObj
  exact ModuleCat.MonModuleEquivalenceAlgebra.Algebra_of_Mon_ M

/-- Coalgebra structure maps on the ordinary descended carrier. -/
@[instance_reducible]
noncomputable def descendedCoalgebraStruct
    (H : AffineCechSelectedCommHopfAlgebraObject f hf) :
    CoalgebraStruct R (affineCechDescendedModule f hf H.obj) where
  comul :=
    ModuleCat.Hom.hom H.toAffineCechSelectedCoalgebraObject.descendedComul
  counit :=
    ModuleCat.Hom.hom H.toAffineCechSelectedCoalgebraObject.descendedCounit

/-- The coalgebra laws on the ordinary descended carrier. -/
@[instance_reducible]
noncomputable def descendedCoalgebra
    (H : AffineCechSelectedCommHopfAlgebraObject f hf) :
    Coalgebra R (affineCechDescendedModule f hf H.obj) := by
  let M := affineCechDescendedModule f hf H.obj
  letI : ComonObj M := H.descendedComonObj
  exact CoalgCat.instCoalgebra (CoalgCat.ofComonObj M)

@[instance_reducible]
noncomputable def descendedBialgebra
    (H : AffineCechSelectedCommHopfAlgebraObject f hf) :
    let M := affineCechDescendedModule f hf H.obj
    let _ : CommRing M := H.descendedCommRing
    let _ : Algebra R M := H.descendedAlgebra
    let _ : CoalgebraStruct R M := H.descendedCoalgebraStruct
    let _ : Coalgebra R M := H.descendedCoalgebra
    Bialgebra R M := by
  dsimp only
  let M := affineCechDescendedModule f hf H.obj
  letI : CommRing M := H.descendedCommRing
  letI : Algebra R M := H.descendedAlgebra
  letI : CoalgebraStruct R M := H.descendedCoalgebraStruct
  letI : Coalgebra R M := H.descendedCoalgebra
  apply Bialgebra.mk
  · change
      (ModuleCat.Hom.hom H.toAffineCechSelectedCoalgebraObject.descendedCounit)
          ((ModuleCat.Hom.hom H.descendedUnit) 1) = 1
    have h := congrArg
      (fun q => (ModuleCat.Hom.hom q) 1) H.descendedCounit_unit
    change
      (ModuleCat.Hom.hom H.toAffineCechSelectedCoalgebraObject.descendedCounit)
          ((ModuleCat.Hom.hom H.descendedUnit) 1) = 1 at h
    exact h
  · ext x y
    change
      (ModuleCat.Hom.hom H.toAffineCechSelectedCoalgebraObject.descendedCounit)
          ((ModuleCat.Hom.hom H.descendedMul) (x ⊗ₜ[R] y)) =
        (ModuleCat.Hom.hom H.toAffineCechSelectedCoalgebraObject.descendedCounit) x *
          (ModuleCat.Hom.hom H.toAffineCechSelectedCoalgebraObject.descendedCounit) y
    have h := congrArg
      (fun q => (ModuleCat.Hom.hom q) (x ⊗ₜ[R] y))
      H.descendedCounit_mul
    calc
      (ModuleCat.Hom.hom H.toAffineCechSelectedCoalgebraObject.descendedCounit)
          ((ModuleCat.Hom.hom H.descendedMul) (x ⊗ₜ[R] y)) =
        (ModuleCat.Hom.hom
          (H.descendedMul ≫
            H.toAffineCechSelectedCoalgebraObject.descendedCounit))
          (x ⊗ₜ[R] y) := rfl
      _ = (ModuleCat.Hom.hom
          (ModuleCat.ofHom
              (TensorProduct.map
                (ModuleCat.Hom.hom H.toAffineCechSelectedCoalgebraObject.descendedCounit)
                (ModuleCat.Hom.hom H.toAffineCechSelectedCoalgebraObject.descendedCounit)) ≫
            (TensorProduct.rid R (ModuleCat.of R R)).toModuleIso.hom))
          (x ⊗ₜ[R] y) := h
      _ = (ModuleCat.Hom.hom H.toAffineCechSelectedCoalgebraObject.descendedCounit) x *
          (ModuleCat.Hom.hom H.toAffineCechSelectedCoalgebraObject.descendedCounit) y := by
            let x' : affineCechDescendedModule f hf
                H.toAffineCechSelectedCoalgebraObject.obj := x
            let y' : affineCechDescendedModule f hf
                H.toAffineCechSelectedCoalgebraObject.obj := y
            change
              (TensorProduct.rid R R)
                  ((TensorProduct.map
                    (ModuleCat.Hom.hom H.toAffineCechSelectedCoalgebraObject.descendedCounit)
                    (ModuleCat.Hom.hom H.toAffineCechSelectedCoalgebraObject.descendedCounit))
                    (x' ⊗ₜ[R] y')) =
                (ModuleCat.Hom.hom H.toAffineCechSelectedCoalgebraObject.descendedCounit) x' *
                  (ModuleCat.Hom.hom H.toAffineCechSelectedCoalgebraObject.descendedCounit) y'
            rw [TensorProduct.map_tmul, TensorProduct.rid_tmul]
            exact _root_.mul_comm _ _
  · change
      (ModuleCat.Hom.hom H.toAffineCechSelectedCoalgebraObject.descendedComul)
          ((ModuleCat.Hom.hom H.descendedUnit) 1) =
        (ModuleCat.Hom.hom H.descendedUnit) 1 ⊗ₜ[R]
          (ModuleCat.Hom.hom H.descendedUnit) 1
    have h := congrArg
      (fun q => (ModuleCat.Hom.hom q) 1) H.descendedComul_unit
    change
      (ModuleCat.Hom.hom H.toAffineCechSelectedCoalgebraObject.descendedComul)
          ((ModuleCat.Hom.hom H.descendedUnit) 1) =
        (ModuleCat.Hom.hom H.descendedUnit) 1 ⊗ₜ[R]
          (ModuleCat.Hom.hom H.descendedUnit) 1 at h
    exact h
  · ext x y
    let dx : TensorProduct R M M :=
      (ModuleCat.Hom.hom
        H.toAffineCechSelectedCoalgebraObject.descendedComul) x
    let dy : TensorProduct R M M :=
      (ModuleCat.Hom.hom
        H.toAffineCechSelectedCoalgebraObject.descendedComul) y
    change
      (ModuleCat.Hom.hom
          H.toAffineCechSelectedCoalgebraObject.descendedComul)
          ((ModuleCat.Hom.hom H.descendedMul) (x ⊗ₜ[R] y)) =
        dx * dy
    have h := congrArg
      (fun q => (ModuleCat.Hom.hom q) (x ⊗ₜ[R] y))
      H.descendedComul_mul
    change
      (ModuleCat.Hom.hom
        (H.descendedMul ≫
          H.toAffineCechSelectedCoalgebraObject.descendedComul))
        (x ⊗ₜ[R] y) = dx * dy
    rw [h]
    change
      (TensorProduct.map
          (ModuleCat.Hom.hom H.descendedMul)
          (ModuleCat.Hom.hom H.descendedMul))
          ((tensorProductMiddleFourIso R M M M M).hom
            (dx ⊗ₜ[R] dy)) =
        dx * dy
    induction dx using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      induction dy using TensorProduct.induction_on with
      | zero => simp
      | tmul c d =>
        rw [tensorProductMiddleFourIso_hom_tmul,
          TensorProduct.map_tmul,
          Algebra.TensorProduct.tmul_mul_tmul]
        rfl
      | add q₁ q₂ hq₁ hq₂ =>
        simp only [TensorProduct.tmul_add, map_add, mul_add,
          hq₁, hq₂]
    | add p₁ p₂ hp₁ hp₂ =>
      simp only [TensorProduct.add_tmul, map_add, add_mul,
        hp₁, hp₂]

/-- The descended antipode added to the descended bialgebra structure. -/
@[instance_reducible]
noncomputable def descendedHopfAlgebraStruct
    (H : AffineCechSelectedCommHopfAlgebraObject f hf) :
    let M := affineCechDescendedModule f hf H.obj
    let _ : CommRing M := H.descendedCommRing
    let _ : Algebra R M := H.descendedAlgebra
    let _ : CoalgebraStruct R M := H.descendedCoalgebraStruct
    let _ : Coalgebra R M := H.descendedCoalgebra
    let _ : Bialgebra R M := H.descendedBialgebra
    HopfAlgebraStruct R M := by
  dsimp only
  let M := affineCechDescendedModule f hf H.obj
  letI : CommRing M := H.descendedCommRing
  letI : Algebra R M := H.descendedAlgebra
  letI : CoalgebraStruct R M := H.descendedCoalgebraStruct
  letI : Coalgebra R M := H.descendedCoalgebra
  letI : Bialgebra R M := H.descendedBialgebra
  exact HopfAlgebraStruct.mk (ModuleCat.Hom.hom H.descendedAntipode)

/-- The ordinary descended carrier, with all five descended structure maps,
is a commutative Hopf algebra over the base ring. -/
@[instance_reducible]
noncomputable def descendedHopfAlgebra
    (H : AffineCechSelectedCommHopfAlgebraObject f hf) :
    let M := affineCechDescendedModule f hf H.obj
    let _ : CommRing M := H.descendedCommRing
    let _ : Algebra R M := H.descendedAlgebra
    let _ : CoalgebraStruct R M := H.descendedCoalgebraStruct
    let _ : Coalgebra R M := H.descendedCoalgebra
    let _ : Bialgebra R M := H.descendedBialgebra
    let _ : HopfAlgebraStruct R M := H.descendedHopfAlgebraStruct
    HopfAlgebra R M := by
  dsimp only
  let M := affineCechDescendedModule f hf H.obj
  letI : CommRing M := H.descendedCommRing
  letI : Algebra R M := H.descendedAlgebra
  letI : CoalgebraStruct R M := H.descendedCoalgebraStruct
  letI : Coalgebra R M := H.descendedCoalgebra
  letI : Bialgebra R M := H.descendedBialgebra
  letI : HopfAlgebraStruct R M := H.descendedHopfAlgebraStruct
  have hmul :
      LinearMap.mul' R M = ModuleCat.Hom.hom H.descendedMul := by
    ext a b
    rfl
  have hunit :
      Algebra.linearMap R M = ModuleCat.Hom.hom H.descendedUnit := by
    ext
    rfl
  have hantipode :
      (HopfAlgebraStruct.antipode R : M →ₗ[R] M) =
        ModuleCat.Hom.hom
          H.toAffineCechSelectedHopfAlgebraObject.descendedAntipode := rfl
  apply HopfAlgebra.mk
  · rw [hmul, hantipode, hunit]
    ext x
    change
      (ModuleCat.Hom.hom H.descendedMul)
          ((TensorProduct.map
            (ModuleCat.Hom.hom
              H.toAffineCechSelectedHopfAlgebraObject.descendedAntipode)
            LinearMap.id)
            ((ModuleCat.Hom.hom
              H.toAffineCechSelectedCoalgebraObject.descendedComul) x)) =
        (ModuleCat.Hom.hom H.descendedUnit)
          ((ModuleCat.Hom.hom
            H.toAffineCechSelectedCoalgebraObject.descendedCounit) x)
    have h := congrArg
      (fun q => (ModuleCat.Hom.hom q) x)
      H.toAffineCechSelectedHopfAlgebraObject.descendedAntipode_mul_left
    change
      (ModuleCat.Hom.hom H.descendedMul)
          ((TensorProduct.map
            (ModuleCat.Hom.hom
              H.toAffineCechSelectedHopfAlgebraObject.descendedAntipode)
            LinearMap.id)
            ((ModuleCat.Hom.hom
              H.toAffineCechSelectedCoalgebraObject.descendedComul) x)) =
        (ModuleCat.Hom.hom H.descendedUnit)
          ((ModuleCat.Hom.hom
            H.toAffineCechSelectedCoalgebraObject.descendedCounit) x) at h
    exact h
  · rw [hmul, hantipode, hunit]
    ext x
    change
      (ModuleCat.Hom.hom H.descendedMul)
          ((TensorProduct.map LinearMap.id
            (ModuleCat.Hom.hom
              H.toAffineCechSelectedHopfAlgebraObject.descendedAntipode))
            ((ModuleCat.Hom.hom
              H.toAffineCechSelectedCoalgebraObject.descendedComul) x)) =
        (ModuleCat.Hom.hom H.descendedUnit)
          ((ModuleCat.Hom.hom
            H.toAffineCechSelectedCoalgebraObject.descendedCounit) x)
    have h := congrArg
      (fun q => (ModuleCat.Hom.hom q) x)
      H.toAffineCechSelectedHopfAlgebraObject.descendedAntipode_mul_right
    change
      (ModuleCat.Hom.hom H.descendedMul)
          ((TensorProduct.map LinearMap.id
            (ModuleCat.Hom.hom
              H.toAffineCechSelectedHopfAlgebraObject.descendedAntipode))
            ((ModuleCat.Hom.hom
              H.toAffineCechSelectedCoalgebraObject.descendedComul) x)) =
        (ModuleCat.Hom.hom H.descendedUnit)
          ((ModuleCat.Hom.hom
            H.toAffineCechSelectedCoalgebraObject.descendedCounit) x) at h
    exact h
end AffineCechSelectedCommHopfAlgebraObject

end RiemannResearch.AlgebraicGeometry
