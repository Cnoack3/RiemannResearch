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
bialgebra objects, exposes their underlying coalgebra objects, and transports
all four structural compatibility equations to the ordinary descended
base module.

The ordinary tensor middle interchange is defined explicitly from the
associator and symmetry. Its selected counterpart is obtained through affine
Čech comparison, with a verified pure-tensor formula and an exact formula for
the descended morphism.

Antipodes, concrete Hopf-algebra packaging, and the D4 specialization remain
separate layers.

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

namespace RiemannResearch.AlgebraicGeometry
namespace AffineCechSelectedBialgebraObject
variable {R A : CommRingCat.{u}} {f : R ⟶ A}
variable {hf : f.hom.FaithfullyFlat}

/-- The descended counit preserves the ordinary descended multiplication. -/
theorem descendedCounit_mul
    (B : AffineCechSelectedBialgebraObject f hf) :
    B.toAffineCechSelectedAlgebraObject.descendedMul ≫
        B.toAffineCechSelectedCoalgebraObject.descendedCounit =
      ModuleCat.ofHom
          (TensorProduct.map
            (ModuleCat.Hom.hom
              B.toAffineCechSelectedCoalgebraObject.descendedCounit)
            (ModuleCat.Hom.hom
              B.toAffineCechSelectedCoalgebraObject.descendedCounit)) ≫
        (TensorProduct.rid R (ModuleCat.of R R)).toModuleIso.hom := by
  let X := B.toAffineCechSelectedAlgebraObject.obj
  let U := affineCechSelectedTensorUnitDescentData f
  let eX := affineCechSelectedTensorDescendedIso f hf X X
  let eU := affineCechSelectedTensorUnitDescendedIso f hf
  let eUU := affineCechSelectedTensorDescendedIso f hf U U
  let rB := affineCechSelectedTensorRightUnitorBaseIso f hf U
  let μ₀ := affineCechDescendedModuleHom f hf
    B.toAffineCechSelectedAlgebraObject.mul
  let ε₀ := affineCechDescendedModuleHom f hf B.counit
  let t := affineCechDescendedTensorMap f hf B.counit B.counit
  have htensor :
      affineCechDescendedModuleHom f hf
          (affineCechSelectedTensorMap f hf B.counit B.counit) =
        eX.hom ≫ t ≫ eUU.inv := by
    exact affineCechDescendedModuleHom_of_comparison_map f hf t
  have h := congrArg
    (fun q => affineCechDescendedModuleHom f hf q) B.counit_mul
  simp only [affineCechDescendedModuleHom_comp] at h
  rw [htensor, affineCechDescendedModuleHom_rightUnitorIso_hom] at h
  dsimp [eUU, U] at h
  have hbase :
      μ₀ ≫ ε₀ ≫ eU.hom =
        eX.hom ≫ t ≫ rB.hom ≫ eU.hom := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
      congrArg (fun q => q ≫ eU.hom) h
  change
    (eX.inv ≫ μ₀) ≫ (ε₀ ≫ eU.hom) =
      ModuleCat.ofHom
          (TensorProduct.map
            (ModuleCat.Hom.hom (ε₀ ≫ eU.hom))
            (ModuleCat.Hom.hom (ε₀ ≫ eU.hom))) ≫
        (TensorProduct.rid R (ModuleCat.of R R)).toModuleIso.hom
  simp only [Category.assoc] at hbase ⊢
  rw [hbase, Iso.inv_hom_id_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
      change
        eU.hom (eU.hom (ε₀ y) • ε₀ x) =
          eU.hom (ε₀ y) * eU.hom (ε₀ x)
      exact (ModuleCat.Hom.hom eU.hom).map_smul
        (eU.hom (ε₀ y)) (ε₀ x)
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The descended comultiplication preserves the ordinary descended unit. -/
theorem descendedComul_unit
    (B : AffineCechSelectedBialgebraObject f hf) :
    B.toAffineCechSelectedAlgebraObject.descendedUnit ≫
        B.toAffineCechSelectedCoalgebraObject.descendedComul =
      (TensorProduct.rid R (ModuleCat.of R R)).toModuleIso.inv ≫
        ModuleCat.ofHom
          (TensorProduct.map
            (ModuleCat.Hom.hom
              B.toAffineCechSelectedAlgebraObject.descendedUnit)
            (ModuleCat.Hom.hom
              B.toAffineCechSelectedAlgebraObject.descendedUnit)) := by
  let X := B.toAffineCechSelectedAlgebraObject.obj
  let U := affineCechSelectedTensorUnitDescentData f
  let eX := affineCechSelectedTensorDescendedIso f hf X X
  let eU := affineCechSelectedTensorUnitDescendedIso f hf
  let eUU := affineCechSelectedTensorDescendedIso f hf U U
  let rB := affineCechSelectedTensorRightUnitorBaseIso f hf U
  let η₀ := affineCechDescendedModuleHom f hf
    B.toAffineCechSelectedAlgebraObject.unit
  let δ₀ := affineCechDescendedModuleHom f hf B.comul
  let t := affineCechDescendedTensorMap f hf
    B.toAffineCechSelectedAlgebraObject.unit
    B.toAffineCechSelectedAlgebraObject.unit
  let rI := affineCechSelectedTensorRightUnitorIso f hf U
  have htensor :
      affineCechDescendedModuleHom f hf
          (affineCechSelectedTensorMap f hf
            B.toAffineCechSelectedAlgebraObject.unit
            B.toAffineCechSelectedAlgebraObject.unit) =
        eUU.hom ≫ t ≫ eX.inv := by
    exact affineCechDescendedModuleHom_of_comparison_map f hf t
  have hrunitor :
      affineCechDescendedModuleHom f hf rI.hom =
        eUU.hom ≫ rB.hom := by
    exact affineCechDescendedModuleHom_rightUnitorIso_hom f hf U
  have hrunitor_inv :
      affineCechDescendedModuleHom f hf rI.inv =
        rB.inv ≫ eUU.inv := by
    have hi := congrArg
      (fun q => affineCechDescendedModuleHom f hf q) rI.inv_hom_id
    simp only [affineCechDescendedModuleHom_comp,
      affineCechDescendedModuleHom_id, hrunitor] at hi
    apply (cancel_mono (eUU.hom ≫ rB.hom)).1
    rw [hi]
    simp only [Category.assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id]
  have h := congrArg
    (fun q => affineCechDescendedModuleHom f hf q) B.comul_unit
  simp only [affineCechDescendedModuleHom_comp] at h
  change η₀ ≫ δ₀ =
      affineCechDescendedModuleHom f hf rI.inv ≫
        affineCechDescendedModuleHom f hf
          (affineCechSelectedTensorMap f hf
            B.toAffineCechSelectedAlgebraObject.unit
            B.toAffineCechSelectedAlgebraObject.unit) at h
  rw [hrunitor_inv, htensor] at h
  have hbase :
      eU.inv ≫ η₀ ≫ δ₀ ≫ eX.hom =
        eU.inv ≫ rB.inv ≫ t := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id] using
      congrArg (fun q => eU.inv ≫ q ≫ eX.hom) h
  change
    (eU.inv ≫ η₀) ≫ (δ₀ ≫ eX.hom) =
      (TensorProduct.rid R (ModuleCat.of R R)).toModuleIso.inv ≫
        ModuleCat.ofHom
          (TensorProduct.map
            (ModuleCat.Hom.hom (eU.inv ≫ η₀))
            (ModuleCat.Hom.hom (eU.inv ≫ η₀)))
  simp only [Category.assoc] at hbase ⊢
  rw [hbase]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  have hr :
      rB.inv (eU.inv r) =
        eU.inv r ⊗ₜ[R] eU.inv 1 := by
    apply rB.toLinearEquiv.injective
    change rB.toLinearEquiv (rB.toLinearEquiv.symm (eU.inv r)) =
      rB.toLinearEquiv (eU.inv r ⊗ₜ[R] eU.inv 1)
    rw [rB.toLinearEquiv.apply_symm_apply]
    change eU.inv r = eU.hom (eU.inv 1) • eU.inv r
    have hu : eU.hom (eU.inv (1 : R)) = 1 :=
      eU.toLinearEquiv.apply_symm_apply 1
    rw [hu, one_smul]
  rw [hr]
  change
    (TensorProduct.map (ModuleCat.Hom.hom η₀)
      (ModuleCat.Hom.hom η₀))
      (eU.inv r ⊗ₜ[R] eU.inv 1) =
      η₀ (eU.inv r) ⊗ₜ[R] η₀ (eU.inv 1)
  rw [TensorProduct.map_tmul]

/-- The descended comultiplication preserves the ordinary descended
multiplication through the ordinary middle-four interchange. -/
theorem descendedComul_mul
    (B : AffineCechSelectedBialgebraObject f hf) :
    let M := affineCechDescendedModule f hf
      B.toAffineCechSelectedAlgebraObject.obj
    B.toAffineCechSelectedAlgebraObject.descendedMul ≫
        B.toAffineCechSelectedCoalgebraObject.descendedComul =
      ModuleCat.ofHom
          (TensorProduct.map
            (ModuleCat.Hom.hom
              B.toAffineCechSelectedCoalgebraObject.descendedComul)
            (ModuleCat.Hom.hom
              B.toAffineCechSelectedCoalgebraObject.descendedComul)) ≫
        (tensorProductMiddleFourIso R M M M M).hom ≫
        ModuleCat.ofHom
          (TensorProduct.map
            (ModuleCat.Hom.hom
              B.toAffineCechSelectedAlgebraObject.descendedMul)
            (ModuleCat.Hom.hom
              B.toAffineCechSelectedAlgebraObject.descendedMul)) := by
  dsimp only
  let X := B.toAffineCechSelectedAlgebraObject.obj
  let M := affineCechDescendedModule f hf X
  let T := affineCechSelectedTensorDescentData f hf X X
  let eT := affineCechSelectedTensorDescendedIso f hf X X
  let eTT := affineCechSelectedTensorDescendedIso f hf T T
  let mB := affineCechSelectedMiddleFourBaseIso f hf X X X X
  let μ₀ := affineCechDescendedModuleHom f hf
    B.toAffineCechSelectedAlgebraObject.mul
  let δ₀ := affineCechDescendedModuleHom f hf B.comul
  let tc := affineCechDescendedTensorMap f hf B.comul B.comul
  let tm := affineCechDescendedTensorMap f hf
    B.toAffineCechSelectedAlgebraObject.mul
    B.toAffineCechSelectedAlgebraObject.mul
  have htc :
      affineCechDescendedModuleHom f hf
          (affineCechSelectedTensorMap f hf B.comul B.comul) =
        eT.hom ≫ tc ≫ eTT.inv := by
    exact affineCechDescendedModuleHom_of_comparison_map f hf tc
  have htm :
      affineCechDescendedModuleHom f hf
          (affineCechSelectedTensorMap f hf
            B.toAffineCechSelectedAlgebraObject.mul
            B.toAffineCechSelectedAlgebraObject.mul) =
        eTT.hom ≫ tm ≫ eT.inv := by
    exact affineCechDescendedModuleHom_of_comparison_map f hf tm
  have hm :
      affineCechDescendedModuleHom f hf
          (affineCechSelectedMiddleFourIso f hf X X X X).hom =
        eTT.hom ≫ mB.hom ≫ eTT.inv := by
    exact affineCechDescendedModuleHom_middleFourIso_hom f hf X X X X
  have h := congrArg
    (fun q => affineCechDescendedModuleHom f hf q) B.comul_mul
  simp only [affineCechDescendedModuleHom_comp] at h
  rw [htc, hm, htm] at h
  have hbase :
      eT.inv ≫ μ₀ ≫ δ₀ ≫ eT.hom =
        tc ≫ mB.hom ≫ tm := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id] using
      congrArg (fun q => eT.inv ≫ q ≫ eT.hom) h
  change
    (eT.inv ≫ μ₀) ≫ (δ₀ ≫ eT.hom) =
      ModuleCat.ofHom
          (TensorProduct.map
            (ModuleCat.Hom.hom (δ₀ ≫ eT.hom))
            (ModuleCat.Hom.hom (δ₀ ≫ eT.hom))) ≫
        (tensorProductMiddleFourIso R M M M M).hom ≫
        ModuleCat.ofHom
          (TensorProduct.map
            (ModuleCat.Hom.hom (eT.inv ≫ μ₀))
            (ModuleCat.Hom.hom (eT.inv ≫ μ₀)))
  simp only [Category.assoc] at hbase ⊢
  rw [hbase]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
      dsimp [tc, tm, affineCechDescendedTensorMap]
      rw [← eT.hom_inv_id_apply (δ₀ x),
        ← eT.hom_inv_id_apply (δ₀ y)]
      generalize eT.hom (δ₀ x) = w
      generalize eT.hom (δ₀ y) = v
      induction w using TensorProduct.induction_on with
      | zero => simp only [map_zero, TensorProduct.zero_tmul]
      | tmul a b =>
          induction v using TensorProduct.induction_on with
          | zero => simp only [map_zero, TensorProduct.tmul_zero]
          | tmul c d =>
              rw [affineCechSelectedMiddleFourBaseIso_hom_tmul]
              rw [eT.inv_hom_id_apply, eT.inv_hom_id_apply,
                tensorProductMiddleFourIso_hom_tmul,
                TensorProduct.map_tmul, TensorProduct.map_tmul]
              rfl
          | add v₁ v₂ hv₁ hv₂ =>
              simp only [map_add, TensorProduct.tmul_add, hv₁, hv₂]
      | add w₁ w₂ hw₁ hw₂ =>
          simp only [map_add, TensorProduct.add_tmul, hw₁, hw₂]
  | add x y hx hy => simp only [map_add, hx, hy]

end AffineCechSelectedBialgebraObject

end RiemannResearch.AlgebraicGeometry
