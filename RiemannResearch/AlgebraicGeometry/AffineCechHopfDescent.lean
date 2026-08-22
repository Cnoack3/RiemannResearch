/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.AffineCechBialgebraDescent

/-!
# Hopf objects in affine Čech module descent

This file adds an antipode to the selected bialgebra objects for affine Čech
module descent. It descends the antipode to the ordinary base module, proves
its exact recovery after scalar extension, and transports both convolution
identities to the ordinary tensor product over the base ring. A commutative
selected Hopf object is also packaged, with commutativity transported through
the existing algebra-object theorem.

This is the abstract Hopf-object layer. Producing the selected Hopf object for
the diagram-twisted D4 coordinate datum requires equivariance of the concrete
comultiplication, counit, and antipode and remains a separate specialization.

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

end AffineCechSelectedCommHopfAlgebraObject

end RiemannResearch.AlgebraicGeometry
