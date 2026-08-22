/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.AffineCechCoalgebraDescent

/-!
# Bialgebra objects in affine Čech module descent

This file supplies the four-factor middle interchange needed to formulate
bialgebra compatibility for the selected symmetric tensor structure on affine
Čech module descent data. It packages selected bialgebra and commutative
bialgebra objects, exposes their underlying coalgebra objects, and begins the
transport of the structural compatibility equations to the ordinary descended
base module.

The ordinary tensor middle interchange is defined explicitly from the
associator and symmetry. Its selected counterpart is obtained through affine
Čech comparison, with a verified pure-tensor formula and an exact formula for
the descended morphism.

Antipodes, the remaining ordinary bialgebra compatibility equations, concrete
Hopf-algebra packaging, and the D4 specialization remain separate layers.

Source: user-provided affine Čech Hopf-descent program; the formalization uses
the standard symmetric-monoidal middle-four interchange and transports the
bialgebra-object equations through the previously verified selected tensor
coherence.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory

namespace RiemannResearch.AlgebraicGeometry

/-- The ordinary middle-four interchange, assembled from tensor associativity
and the symmetry exchanging the two middle factors. -/
noncomputable def tensorProductMiddleFourIso
    (R : CommRingCat.{u}) (M N P Q : ModuleCat R) :
    ModuleCat.of R
        (TensorProduct R (TensorProduct R M N) (TensorProduct R P Q)) ≅
      ModuleCat.of R
        (TensorProduct R (TensorProduct R M P) (TensorProduct R N Q)) :=
  ((TensorProduct.assoc R M N (TensorProduct R P Q)).trans
    ((TensorProduct.congr (LinearEquiv.refl R M)
      (TensorProduct.assoc R N P Q).symm).trans
      ((TensorProduct.congr (LinearEquiv.refl R M)
        (TensorProduct.congr (TensorProduct.comm R N P)
          (LinearEquiv.refl R Q))).trans
        ((TensorProduct.congr (LinearEquiv.refl R M)
          (TensorProduct.assoc R P N Q)).trans
          (TensorProduct.assoc R M P (TensorProduct R N Q)).symm)))).toModuleIso

/-- The ordinary middle-four interchange has the expected value on pure
tensors. -/
@[simp] theorem tensorProductMiddleFourIso_hom_tmul
    (R : CommRingCat.{u}) (M N P Q : ModuleCat R)
    (m : M) (n : N) (p : P) (q : Q) :
    (tensorProductMiddleFourIso R M N P Q).hom
        ((m ⊗ₜ[R] n) ⊗ₜ[R] (p ⊗ₜ[R] q)) =
      (m ⊗ₜ[R] p) ⊗ₜ[R] (n ⊗ₜ[R] q) := by
  simp [tensorProductMiddleFourIso]

/-- The ordinary-base middle-four interchange, conjugated by the four selected
binary-tensor preimage comparisons. -/
noncomputable def affineCechSelectedMiddleFourBaseIso
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D E G H : AffineCechModuleDescentData f) :
    ModuleCat.of R
        (TensorProduct R
          (affineCechDescendedModule f hf
            (affineCechSelectedTensorDescentData f hf D E))
          (affineCechDescendedModule f hf
            (affineCechSelectedTensorDescentData f hf G H))) ≅
      ModuleCat.of R
        (TensorProduct R
          (affineCechDescendedModule f hf
            (affineCechSelectedTensorDescentData f hf D G))
          (affineCechDescendedModule f hf
            (affineCechSelectedTensorDescentData f hf E H))) :=
  (TensorProduct.congr
      (affineCechSelectedTensorDescendedIso f hf D E).toLinearEquiv
      (affineCechSelectedTensorDescendedIso f hf G H).toLinearEquiv).toModuleIso ≪≫
    tensorProductMiddleFourIso R
      (affineCechDescendedModule f hf D)
      (affineCechDescendedModule f hf E)
      (affineCechDescendedModule f hf G)
      (affineCechDescendedModule f hf H) ≪≫
    (TensorProduct.congr
      (affineCechSelectedTensorDescendedIso f hf D G).symm.toLinearEquiv
      (affineCechSelectedTensorDescendedIso f hf E H).symm.toLinearEquiv).toModuleIso

/-- The selected-base middle-four interchange has the expected value when all
four binary factors are expressed through the selected tensor comparisons. -/
theorem affineCechSelectedMiddleFourBaseIso_hom_tmul
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D E G H : AffineCechModuleDescentData f)
    (d : affineCechDescendedModule f hf D)
    (e : affineCechDescendedModule f hf E)
    (g : affineCechDescendedModule f hf G)
    (h : affineCechDescendedModule f hf H) :
    (affineCechSelectedMiddleFourBaseIso f hf D E G H).hom
      ((affineCechSelectedTensorDescendedIso f hf D E).inv
          (d ⊗ₜ[R] e) ⊗ₜ[R]
        (affineCechSelectedTensorDescendedIso f hf G H).inv
          (g ⊗ₜ[R] h)) =
      (affineCechSelectedTensorDescendedIso f hf D G).inv
          (d ⊗ₜ[R] g) ⊗ₜ[R]
        (affineCechSelectedTensorDescendedIso f hf E H).inv
          (e ⊗ₜ[R] h) := by
  let eDE := affineCechSelectedTensorDescendedIso f hf D E
  let eGH := affineCechSelectedTensorDescendedIso f hf G H
  let eDG := affineCechSelectedTensorDescendedIso f hf D G
  let eEH := affineCechSelectedTensorDescendedIso f hf E H
  change
    (TensorProduct.map (ModuleCat.Hom.hom eDG.inv)
        (ModuleCat.Hom.hom eEH.inv))
      ((tensorProductMiddleFourIso R _ _ _ _).hom
        ((TensorProduct.map (ModuleCat.Hom.hom eDE.hom)
            (ModuleCat.Hom.hom eGH.hom))
          (eDE.inv (d ⊗ₜ[R] e) ⊗ₜ[R] eGH.inv (g ⊗ₜ[R] h)))) =
      eDG.inv (d ⊗ₜ[R] g) ⊗ₜ[R] eEH.inv (e ⊗ₜ[R] h)
  rw [TensorProduct.map_tmul]
  change
    (TensorProduct.map (ModuleCat.Hom.hom eDG.inv)
        (ModuleCat.Hom.hom eEH.inv))
      ((tensorProductMiddleFourIso R _ _ _ _).hom
        (eDE.hom (eDE.inv (d ⊗ₜ[R] e)) ⊗ₜ[R]
          eGH.hom (eGH.inv (g ⊗ₜ[R] h)))) = _
  rw [eDE.inv_hom_id_apply, eGH.inv_hom_id_apply,
    tensorProductMiddleFourIso_hom_tmul, TensorProduct.map_tmul]

/-- The middle-four interchange for selected affine Čech descent data. -/
noncomputable def affineCechSelectedMiddleFourIso
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D E G H : AffineCechModuleDescentData f) :
    affineCechSelectedTensorDescentData f hf
        (affineCechSelectedTensorDescentData f hf D E)
        (affineCechSelectedTensorDescentData f hf G H) ≅
      affineCechSelectedTensorDescentData f hf
        (affineCechSelectedTensorDescentData f hf D G)
        (affineCechSelectedTensorDescentData f hf E H) :=
  (affineCechModuleDescentComparison f).mapIso
    (affineCechSelectedMiddleFourBaseIso f hf D E G H)

/-- Descending the selected middle-four interchange recovers the ordinary-base
map, conjugated by the two outer selected tensor comparisons. -/
theorem affineCechDescendedModuleHom_middleFourIso_hom
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D E G H : AffineCechModuleDescentData f) :
    affineCechDescendedModuleHom f hf
        (affineCechSelectedMiddleFourIso f hf D E G H).hom =
      (affineCechSelectedTensorDescendedIso f hf
          (affineCechSelectedTensorDescentData f hf D E)
          (affineCechSelectedTensorDescentData f hf G H)).hom ≫
        (affineCechSelectedMiddleFourBaseIso f hf D E G H).hom ≫
        (affineCechSelectedTensorDescendedIso f hf
          (affineCechSelectedTensorDescentData f hf D G)
          (affineCechSelectedTensorDescentData f hf E H)).inv := by
  exact affineCechDescendedModuleHom_of_comparison_map f hf
    (affineCechSelectedMiddleFourBaseIso f hf D E G H).hom

/-- A bialgebra object for the selected symmetric tensor structure on affine
Čech module descent data. The four final fields are the standard equations
that comultiplication and counit preserve multiplication and unit. -/
structure AffineCechSelectedBialgebraObject
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    extends AffineCechSelectedAlgebraObject f hf where
  comul :
    toAffineCechSelectedAlgebraObject.obj ⟶
      affineCechSelectedTensorDescentData f hf
        toAffineCechSelectedAlgebraObject.obj
        toAffineCechSelectedAlgebraObject.obj
  counit :
    toAffineCechSelectedAlgebraObject.obj ⟶
      affineCechSelectedTensorUnitDescentData f
  comul_assoc :
    comul ≫ affineCechSelectedTensorMap f hf comul
          (𝟙 toAffineCechSelectedAlgebraObject.obj) ≫
        (affineCechSelectedTensorAssociatorIso f hf
          toAffineCechSelectedAlgebraObject.obj
          toAffineCechSelectedAlgebraObject.obj
          toAffineCechSelectedAlgebraObject.obj).hom =
      comul ≫ affineCechSelectedTensorMap f hf
        (𝟙 toAffineCechSelectedAlgebraObject.obj) comul
  counit_left :
    comul ≫ affineCechSelectedTensorMap f hf counit
          (𝟙 toAffineCechSelectedAlgebraObject.obj) ≫
        (affineCechSelectedTensorLeftUnitorIso f hf
          toAffineCechSelectedAlgebraObject.obj).hom =
      𝟙 toAffineCechSelectedAlgebraObject.obj
  counit_right :
    comul ≫ affineCechSelectedTensorMap f hf
          (𝟙 toAffineCechSelectedAlgebraObject.obj) counit ≫
        (affineCechSelectedTensorRightUnitorIso f hf
          toAffineCechSelectedAlgebraObject.obj).hom =
      𝟙 toAffineCechSelectedAlgebraObject.obj
  comul_mul :
    toAffineCechSelectedAlgebraObject.mul ≫ comul =
      affineCechSelectedTensorMap f hf comul comul ≫
        (affineCechSelectedMiddleFourIso f hf
          toAffineCechSelectedAlgebraObject.obj
          toAffineCechSelectedAlgebraObject.obj
          toAffineCechSelectedAlgebraObject.obj
          toAffineCechSelectedAlgebraObject.obj).hom ≫
        affineCechSelectedTensorMap f hf
          toAffineCechSelectedAlgebraObject.mul
          toAffineCechSelectedAlgebraObject.mul
  comul_unit :
    toAffineCechSelectedAlgebraObject.unit ≫ comul =
      (affineCechSelectedTensorRightUnitorIso f hf
        (affineCechSelectedTensorUnitDescentData f)).inv ≫
        affineCechSelectedTensorMap f hf
          toAffineCechSelectedAlgebraObject.unit
          toAffineCechSelectedAlgebraObject.unit
  counit_mul :
    toAffineCechSelectedAlgebraObject.mul ≫ counit =
      affineCechSelectedTensorMap f hf counit counit ≫
        (affineCechSelectedTensorRightUnitorIso f hf
          (affineCechSelectedTensorUnitDescentData f)).hom
  counit_unit :
    toAffineCechSelectedAlgebraObject.unit ≫ counit =
      𝟙 (affineCechSelectedTensorUnitDescentData f)

/-- A selected bialgebra whose multiplication is commutative. -/
structure AffineCechSelectedCommBialgebraObject
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    extends AffineCechSelectedBialgebraObject f hf where
  mul_comm :
    (affineCechSelectedTensorSymmetryIso f hf
        toAffineCechSelectedBialgebraObject.toAffineCechSelectedAlgebraObject.obj
        toAffineCechSelectedBialgebraObject.toAffineCechSelectedAlgebraObject.obj).hom ≫
      toAffineCechSelectedBialgebraObject.toAffineCechSelectedAlgebraObject.mul =
    toAffineCechSelectedBialgebraObject.toAffineCechSelectedAlgebraObject.mul

namespace AffineCechSelectedBialgebraObject

variable {R A : CommRingCat.{u}} {f : R ⟶ A}
variable {hf : f.hom.FaithfullyFlat}

/-- The underlying selected coalgebra object of a selected bialgebra. -/
noncomputable def toAffineCechSelectedCoalgebraObject
    (B : AffineCechSelectedBialgebraObject f hf) :
    AffineCechSelectedCoalgebraObject f hf where
  obj := B.toAffineCechSelectedAlgebraObject.obj
  comul := B.comul
  counit := B.counit
  comul_assoc := B.comul_assoc
  counit_left := B.counit_left
  counit_right := B.counit_right

/-- The descended unit followed by the descended counit is the identity on
the ordinary base-ring tensor unit. -/
theorem descendedCounit_unit
    (B : AffineCechSelectedBialgebraObject f hf) :
    B.toAffineCechSelectedAlgebraObject.descendedUnit ≫
        B.toAffineCechSelectedCoalgebraObject.descendedCounit =
      𝟙 (ModuleCat.of R R) := by
  let eU := affineCechSelectedTensorUnitDescendedIso f hf
  let etaZero := affineCechDescendedModuleHom f hf
    B.toAffineCechSelectedAlgebraObject.unit
  let epsilonZero := affineCechDescendedModuleHom f hf B.counit
  have h := congrArg
    (fun q => affineCechDescendedModuleHom f hf q) B.counit_unit
  simp only [affineCechDescendedModuleHom_comp,
    affineCechDescendedModuleHom_id] at h
  change (eU.inv ≫ etaZero) ≫ (epsilonZero ≫ eU.hom) = 𝟙 _
  rw [Category.assoc, ← Category.assoc etaZero epsilonZero eU.hom, h]
  exact eU.inv_hom_id

end AffineCechSelectedBialgebraObject

end RiemannResearch.AlgebraicGeometry
