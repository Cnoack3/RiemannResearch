/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.FpqcModuleDescent
import Mathlib.RingTheory.IsTensorProduct

/-!
# The affine Čech module base-change isomorphism

This file constructs the tensor-product isomorphism underlying the comparison
between affine Čech descent data and coalgebras for the extension--restriction
comonad. For an `A`-module `M`, it identifies

`(A ⊗[R] A) ⊗[A, left] M`, restricted along the right inclusion, with
`A ⊗[R] M`.

The construction is an application of Mathlib's
`Algebra.IsPushout.cancelBaseChange`. In particular, the ordering of the two
tensor factors records the convention that the right inclusion supplies the
output `A`-module structure.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory
open scoped ChangeOfRings

namespace RiemannResearch.AlgebraicGeometry

private theorem leftAlgebra_eq
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] :
    Algebra.TensorProduct.includeLeftRingHom.toAlgebra =
      (Algebra.TensorProduct.leftAlgebra :
        Algebra A (TensorProduct R A A)) := by
  apply Algebra.algebra_ext
  intro a
  change Algebra.TensorProduct.includeLeftRingHom a = a ⊗ₜ[R] 1
  exact Algebra.TensorProduct.includeLeftRingHom_apply a

private theorem pushoutWithLeftAlg
    {R A : Type u} [CommRing R] [CommRing A] [algRA : Algebra R A]
    (leftAlg : Algebra A (TensorProduct R A A))
    (hleft : leftAlg =
      (Algebra.TensorProduct.leftAlgebra :
        Algebra A (TensorProduct R A A)))
    (towerLeft : @IsScalarTower R A (TensorProduct R A A)
      algRA.toSMul leftAlg.toSMul
      Algebra.TensorProduct.instAlgebra.toSMul) :
    @Algebra.IsPushout R A _ _ algRA A (TensorProduct R A A) _ _
      algRA Algebra.TensorProduct.rightAlgebra leftAlg
      Algebra.TensorProduct.instAlgebra towerLeft
      Algebra.TensorProduct.right_isScalarTower := by
  subst leftAlg
  exact @TensorProduct.isPushout' R A A _ _ _ algRA algRA

private theorem cancelBaseChange_symm_natural
    (R S A B : Type u)
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra R B]
    [Algebra A B] [Algebra S B]
    [IsScalarTower R A B] [IsScalarTower R S B]
    [Algebra.IsPushout R S A B]
    (M N : Type u) [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module A M] [IsScalarTower R A M]
    [Module R N] [Module A N] [IsScalarTower R A N]
    (g : M →ₗ[A] N) :
    (LinearMap.baseChange B g).restrictScalars S ∘ₗ
        (Algebra.IsPushout.cancelBaseChange R S A B M).symm.toLinearMap =
      (Algebra.IsPushout.cancelBaseChange R S A B N).symm.toLinearMap ∘ₗ
        LinearMap.baseChange S (g.restrictScalars R) := by
  ext s
  simp [LinearMap.baseChange_tmul,
    Algebra.IsPushout.cancelBaseChange_symm_tmul]

private noncomputable def affineTensorCechBaseChangeLinearEquiv
    {R A : CommRingCat.{u}} (f : R ⟶ A) (M : ModuleCat A) :
    letI : Algebra R A := f.hom.toAlgebra
    let X :=
      ((ModuleCat.extendScalars
          (Algebra.TensorProduct.includeLeftRingHom :
            A →+* TensorProduct R A A) ⋙
        ModuleCat.restrictScalars
          (Algebra.TensorProduct.includeRight.toRingHom :
            A →+* TensorProduct R A A)).obj M)
    let Y :=
      ((ModuleCat.restrictScalars f.hom ⋙
        ModuleCat.extendScalars f.hom).obj M)
    (X : Type u) ≃ₗ[A] (Y : Type u) := by
  letI algRA : Algebra R A := f.hom.toAlgebra
  let X :=
    ((ModuleCat.extendScalars
        (Algebra.TensorProduct.includeLeftRingHom :
          A →+* TensorProduct R A A) ⋙
      ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight.toRingHom :
          A →+* TensorProduct R A A)).obj M)
  let Y :=
    ((ModuleCat.restrictScalars f.hom ⋙
      ModuleCat.extendScalars f.hom).obj M)
  letI modRM : Module R M := Module.compHom M f.hom
  letI towerRAM : IsScalarTower R A M :=
    IsScalarTower.of_algebraMap_smul (by intro r m; rfl)
  let leftAlg : Algebra A (TensorProduct R A A) :=
    Algebra.TensorProduct.includeLeftRingHom.toAlgebra
  have hleft : leftAlg =
      (Algebra.TensorProduct.leftAlgebra :
        Algebra A (TensorProduct R A A)) :=
    leftAlgebra_eq
  let towerLeft : @IsScalarTower R A (TensorProduct R A A)
      algRA.toSMul leftAlg.toSMul
      Algebra.TensorProduct.instAlgebra.toSMul := by
    rw [hleft]
    infer_instance
  let pushout := pushoutWithLeftAlg leftAlg hleft towerLeft
  let e :=
    @Algebra.IsPushout.cancelBaseChange R A _ _ algRA A
      (TensorProduct R A A) _ _ algRA
      Algebra.TensorProduct.instAlgebra leftAlg
      Algebra.TensorProduct.rightAlgebra towerLeft
      Algebra.TensorProduct.right_isScalarTower pushout
      M _ modRM (inferInstance : Module A M) towerRAM
  dsimp [X, Y, ModuleCat.extendScalars, ModuleCat.restrictScalars,
    ModuleCat.ExtendScalars.obj', ModuleCat.RestrictScalars.obj',
    CategoryTheory.Functor.comp]
  exact e

/-- The objectwise tensor-product base-change isomorphism on the double overlap.

The source extends an `A`-module along the left inclusion into `A ⊗[R] A` and
then restricts along the right inclusion. The target first restricts to `R`
and then extends back to `A`. -/
noncomputable def affineTensorCechBaseChangeApp
    {R A : CommRingCat.{u}} (f : R ⟶ A) (M : ModuleCat A) :
    letI : Algebra R A := f.hom.toAlgebra
    ((ModuleCat.extendScalars
        (Algebra.TensorProduct.includeLeftRingHom :
          A →+* TensorProduct R A A) ⋙
      ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight.toRingHom :
          A →+* TensorProduct R A A)).obj M) ≅
    ((ModuleCat.restrictScalars f.hom ⋙
      ModuleCat.extendScalars f.hom).obj M) := by
  letI : Algebra R A := f.hom.toAlgebra
  let X :=
    ((ModuleCat.extendScalars
        (Algebra.TensorProduct.includeLeftRingHom :
          A →+* TensorProduct R A A) ⋙
      ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight.toRingHom :
          A →+* TensorProduct R A A)).obj M)
  let Y :=
    ((ModuleCat.restrictScalars f.hom ⋙
      ModuleCat.extendScalars f.hom).obj M)
  let e : (X : Type u) ≃ₗ[A] (Y : Type u) :=
    affineTensorCechBaseChangeLinearEquiv f M
  let eAdd :
      (CategoryTheory.forget₂ (ModuleCat A) AddCommGrpCat).obj X ≅
        (CategoryTheory.forget₂ (ModuleCat A) AddCommGrpCat).obj Y :=
    AddEquiv.toAddCommGrpIso e.toAddEquiv
  refine ModuleCat.isoMk eAdd ?_
  intro a
  ext x
  change AddCommGrpCat.Hom.hom (Y.smul a) (e x) =
    e (AddCommGrpCat.Hom.hom (X.smul a) x)
  exact (e.map_smul a x).symm

private theorem affineTensorCechBaseChangeLinearEquiv_symm_natural
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    {M N : ModuleCat A} (g : M ⟶ N) :
    letI : Algebra R A := f.hom.toAlgebra
    (affineTensorCechBaseChangeLinearEquiv f N).symm.toLinearMap.comp
        (ModuleCat.Hom.hom
          ((ModuleCat.restrictScalars f.hom ⋙
            ModuleCat.extendScalars f.hom).map g)) =
      (ModuleCat.Hom.hom
        ((ModuleCat.extendScalars
            (Algebra.TensorProduct.includeLeftRingHom :
              A →+* TensorProduct R A A) ⋙
          ModuleCat.restrictScalars
            (Algebra.TensorProduct.includeRight.toRingHom :
              A →+* TensorProduct R A A)).map g)).comp
        (affineTensorCechBaseChangeLinearEquiv f M).symm.toLinearMap := by
  let algRA : Algebra R A := f.hom.toAlgebra
  let modRM : Module R M := Module.compHom M f.hom
  let towerRAM : IsScalarTower R A M :=
    IsScalarTower.of_algebraMap_smul (by intro r m; rfl)
  let modRN : Module R N := Module.compHom N f.hom
  let towerRAN : IsScalarTower R A N :=
    IsScalarTower.of_algebraMap_smul (by intro r n; rfl)
  let leftAlg : Algebra A (TensorProduct R A A) :=
    Algebra.TensorProduct.includeLeftRingHom.toAlgebra
  have hleft : leftAlg =
      (Algebra.TensorProduct.leftAlgebra :
        Algebra A (TensorProduct R A A)) :=
    leftAlgebra_eq
  let towerLeft : @IsScalarTower R A (TensorProduct R A A)
      algRA.toSMul leftAlg.toSMul
      Algebra.TensorProduct.instAlgebra.toSMul := by
    rw [hleft]
    infer_instance
  let pushout := pushoutWithLeftAlg leftAlg hleft towerLeft
  let eM :=
    @Algebra.IsPushout.cancelBaseChange R A _ _ algRA A
      (TensorProduct R A A) _ _ algRA
      Algebra.TensorProduct.instAlgebra leftAlg
      Algebra.TensorProduct.rightAlgebra towerLeft
      Algebra.TensorProduct.right_isScalarTower pushout
      M _ modRM (inferInstance : Module A M) towerRAM
  let eN :=
    @Algebra.IsPushout.cancelBaseChange R A _ _ algRA A
      (TensorProduct R A A) _ _ algRA
      Algebra.TensorProduct.instAlgebra leftAlg
      Algebra.TensorProduct.rightAlgebra towerLeft
      Algebra.TensorProduct.right_isScalarTower pushout
      N _ modRN (inferInstance : Module A N) towerRAN
  let ag :=
    @LinearMap.baseChange R A M N _ _ algRA _ _
      modRM modRN ((ModuleCat.Hom.hom g).restrictScalars R)
  let bg :=
    @LinearMap.baseChange A (TensorProduct R A A) M N _ _ leftAlg _ _
      (inferInstance : Module A M) (inferInstance : Module A N)
      (ModuleCat.Hom.hom g)
  apply LinearMap.ext
  intro x
  change eN.symm (ag x) = bg (eM.symm x)
  have hx := congrArg (fun q => q x)
    (@cancelBaseChange_symm_natural R A A (TensorProduct R A A)
      _ _ _ _ algRA algRA Algebra.TensorProduct.instAlgebra
      leftAlg Algebra.TensorProduct.rightAlgebra towerLeft
      Algebra.TensorProduct.right_isScalarTower pushout
      M N _ _ modRM (inferInstance : Module A M) towerRAM
      modRN (inferInstance : Module A N) towerRAN
      (ModuleCat.Hom.hom g)).symm
  exact hx

/-- The tensor-product base-change isomorphism on the double overlap, natural
in the module. -/
noncomputable def affineTensorCechBaseChangeIso
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    letI : Algebra R A := f.hom.toAlgebra
    (ModuleCat.extendScalars
        (Algebra.TensorProduct.includeLeftRingHom :
          A →+* TensorProduct R A A) ⋙
      ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight.toRingHom :
          A →+* TensorProduct R A A)) ≅
    (ModuleCat.restrictScalars f.hom ⋙
      ModuleCat.extendScalars f.hom) := by
  letI : Algebra R A := f.hom.toAlgebra
  refine (NatIso.ofComponents
    (fun M => (affineTensorCechBaseChangeApp f M).symm) ?_).symm
  intro M N g
  apply ModuleCat.hom_ext
  change
    (affineTensorCechBaseChangeLinearEquiv f N).symm.toLinearMap.comp
        (ModuleCat.Hom.hom
          ((ModuleCat.restrictScalars f.hom ⋙
            ModuleCat.extendScalars f.hom).map g)) =
      (ModuleCat.Hom.hom
        ((ModuleCat.extendScalars
            (Algebra.TensorProduct.includeLeftRingHom :
              A →+* TensorProduct R A A) ⋙
          ModuleCat.restrictScalars
            (Algebra.TensorProduct.includeRight.toRingHom :
              A →+* TensorProduct R A A)).map g)).comp
        (affineTensorCechBaseChangeLinearEquiv f M).symm.toLinearMap
  exact affineTensorCechBaseChangeLinearEquiv_symm_natural f g


@[simp]
theorem affineTensorCechBaseChangeIso_hom_app
    {R A : CommRingCat.{u}} (f : R ⟶ A) (M : ModuleCat A) :
    letI : Algebra R A := f.hom.toAlgebra
    (affineTensorCechBaseChangeIso f).hom.app M =
      (affineTensorCechBaseChangeApp f M).hom := by
  rfl

@[simp]
theorem affineTensorCechBaseChangeIso_inv_app
    {R A : CommRingCat.{u}} (f : R ⟶ A) (M : ModuleCat A) :
    letI : Algebra R A := f.hom.toAlgebra
    (affineTensorCechBaseChangeIso f).inv.app M =
      (affineTensorCechBaseChangeApp f M).inv := by
  rfl

set_option linter.style.haveILetI false in
/-- The inverse Čech base-change isomorphism sends the standard
extension--restriction generator to the corresponding double-overlap
generator. -/
@[simp]
theorem affineTensorCechBaseChangeIso_inv_app_one_tmul
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (M : ModuleCat A) (m : M) :
    letI : Algebra R A := f.hom.toAlgebra
    let mR : (ModuleCat.restrictScalars f.hom).obj M := m
    (affineTensorCechBaseChangeIso f).inv.app M
        ((1 : A) ⊗ₜ[R, f.hom] mR) =
      (1 : TensorProduct R A A) ⊗ₜ[A,
        (Algebra.TensorProduct.includeLeftRingHom :
          A →+* TensorProduct R A A)] m := by
  letI algRA : Algebra R A := f.hom.toAlgebra
  let mR : (ModuleCat.restrictScalars f.hom).obj M := m
  rw [affineTensorCechBaseChangeIso_inv_app]
  change
    (affineTensorCechBaseChangeLinearEquiv f M).symm
        ((1 : A) ⊗ₜ[R, f.hom] mR) =
      (1 : TensorProduct R A A) ⊗ₜ[A,
        (Algebra.TensorProduct.includeLeftRingHom :
          A →+* TensorProduct R A A)] m
  let modRM : Module R M := Module.compHom M f.hom
  let towerRAM : IsScalarTower R A M :=
    IsScalarTower.of_algebraMap_smul (by intro r m'; rfl)
  let leftAlg : Algebra A (TensorProduct R A A) :=
    Algebra.TensorProduct.includeLeftRingHom.toAlgebra
  have hleft : leftAlg =
      (Algebra.TensorProduct.leftAlgebra :
        Algebra A (TensorProduct R A A)) :=
    leftAlgebra_eq
  let towerLeft : @IsScalarTower R A (TensorProduct R A A)
      algRA.toSMul leftAlg.toSMul
      Algebra.TensorProduct.instAlgebra.toSMul := by
    rw [hleft]
    infer_instance
  let pushout := pushoutWithLeftAlg leftAlg hleft towerLeft
  exact @Algebra.IsPushout.cancelBaseChange_symm_tmul
    R A _ _ algRA A (TensorProduct R A A) _ _ algRA
    Algebra.TensorProduct.instAlgebra leftAlg
    Algebra.TensorProduct.rightAlgebra towerLeft
    Algebra.TensorProduct.right_isScalarTower pushout
    M _ modRM (inferInstance : Module A M) towerRAM (1 : A) m

/-- The two tensor-product inclusions agree after composition with the base
ring map. This is the compatibility used to specialize generic comonadic
transport to the canonical Čech pair. -/
theorem affineTensorPair_comp_eq
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    letI : Algebra R A := f.hom.toAlgebra
    (Algebra.TensorProduct.includeRight.toRingHom :
      A →+* TensorProduct R A A).comp f.hom =
    (Algebra.TensorProduct.includeLeftRingHom :
      A →+* TensorProduct R A A).comp f.hom := by
  let algRA : Algebra R A := f.hom.toAlgebra
  ext r
  change 1 ⊗ₜ[R] (algebraMap R A) r = (algebraMap R A) r ⊗ₜ[R] 1
  simpa [Algebra.smul_def] using
    (TensorProduct.smul_tmul (R := R) (R' := R)
      r (1 : A) (1 : A)).symm

/-- The candidate extension--restriction coaction associated to choice-free
affine module descent data. It transposes the canonical double-overlap map
along the right-inclusion adjunction and then applies tensor base change. -/
noncomputable def affineModuleDescentCoaction
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (D : AffineModuleDescentData f) :
    D.obj PUnit.unit ⟶
      ((ModuleCat.restrictScalars f.hom ⋙
        ModuleCat.extendScalars f.hom).obj (D.obj PUnit.unit)) := by
  letI : Algebra R A := f.hom.toAlgebra
  let M : ModuleCat A := D.obj PUnit.unit
  let pair := affineCechPair f
  let θ :
      (ModuleCat.extendScalars
        (Algebra.TensorProduct.includeRight.toRingHom :
          A →+* TensorProduct R A A)).obj M ⟶
      (ModuleCat.extendScalars
        (Algebra.TensorProduct.includeLeftRingHom :
          A →+* TensorProduct R A A)).obj M :=
    D.hom pair.p
      (i₁ := PUnit.unit) (i₂ := PUnit.unit)
      pair.p₁ pair.p₂
  exact
    (ModuleCat.extendRestrictScalarsAdj
      (Algebra.TensorProduct.includeRight.toRingHom :
        A →+* TensorProduct R A A)).homEquiv _ _ θ ≫
      (affineTensorCechBaseChangeIso f).hom.app M

/-- The candidate coactions commute with morphisms of choice-free affine
module descent data. -/
theorem affineModuleDescentCoaction_natural
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    {D₁ D₂ : AffineModuleDescentData f} (φ : D₁ ⟶ D₂) :
    affineModuleDescentCoaction f D₁ ≫
        (ModuleCat.restrictScalars f.hom ⋙
          ModuleCat.extendScalars f.hom).map (φ.hom PUnit.unit) =
      φ.hom PUnit.unit ≫ affineModuleDescentCoaction f D₂ := by
  let algRA : Algebra R A := f.hom.toAlgebra
  let M₁ : ModuleCat A := D₁.obj PUnit.unit
  let M₂ : ModuleCat A := D₂.obj PUnit.unit
  let φ₀ : M₁ ⟶ M₂ := φ.hom PUnit.unit
  let pair := affineCechPair f
  let θ₁ :
      (ModuleCat.extendScalars
        (Algebra.TensorProduct.includeRight.toRingHom :
          A →+* TensorProduct R A A)).obj M₁ ⟶
      (ModuleCat.extendScalars
        (Algebra.TensorProduct.includeLeftRingHom :
          A →+* TensorProduct R A A)).obj M₁ :=
    D₁.hom pair.p
      (i₁ := PUnit.unit) (i₂ := PUnit.unit)
      pair.p₁ pair.p₂
  let θ₂ :
      (ModuleCat.extendScalars
        (Algebra.TensorProduct.includeRight.toRingHom :
          A →+* TensorProduct R A A)).obj M₂ ⟶
      (ModuleCat.extendScalars
        (Algebra.TensorProduct.includeLeftRingHom :
          A →+* TensorProduct R A A)).obj M₂ :=
    D₂.hom pair.p
      (i₁ := PUnit.unit) (i₂ := PUnit.unit)
      pair.p₁ pair.p₂
  let adj :=
    ModuleCat.extendRestrictScalarsAdj
      (Algebra.TensorProduct.includeRight.toRingHom :
        A →+* TensorProduct R A A)
  let e := affineTensorCechBaseChangeIso f
  have hθ :
      (ModuleCat.extendScalars
        (Algebra.TensorProduct.includeRight.toRingHom :
          A →+* TensorProduct R A A)).map φ₀ ≫ θ₂ =
        θ₁ ≫
          (ModuleCat.extendScalars
            (Algebra.TensorProduct.includeLeftRingHom :
              A →+* TensorProduct R A A)).map φ₀ := by
    exact φ.comm pair.p
      (i₁ := PUnit.unit) (i₂ := PUnit.unit)
      pair.p₁ pair.p₂ pair.hp₁ pair.hp₂
  have hAdj :
      φ₀ ≫ adj.homEquiv _ _ θ₂ =
        adj.homEquiv _ _ θ₁ ≫
          (ModuleCat.restrictScalars
            (Algebra.TensorProduct.includeRight.toRingHom :
              A →+* TensorProduct R A A)).map
            ((ModuleCat.extendScalars
              (Algebra.TensorProduct.includeLeftRingHom :
                A →+* TensorProduct R A A)).map φ₀) := by
    calc
      _ = adj.homEquiv _ _
          ((ModuleCat.extendScalars
            (Algebra.TensorProduct.includeRight.toRingHom :
              A →+* TensorProduct R A A)).map φ₀ ≫ θ₂) :=
        (adj.homEquiv_naturality_left φ₀ θ₂).symm
      _ = adj.homEquiv _ _
          (θ₁ ≫
            (ModuleCat.extendScalars
              (Algebra.TensorProduct.includeLeftRingHom :
                A →+* TensorProduct R A A)).map φ₀) := congrArg _ hθ
      _ = _ := adj.homEquiv_naturality_right θ₁ _
  change
    (adj.homEquiv _ _ θ₁ ≫ e.hom.app M₁) ≫
        (ModuleCat.restrictScalars f.hom ⋙
          ModuleCat.extendScalars f.hom).map φ₀ =
      φ₀ ≫ (adj.homEquiv _ _ θ₂ ≫ e.hom.app M₂)
  rw [Category.assoc, ← e.hom.naturality φ₀]
  simp only [Functor.comp_map]
  rw [← Category.assoc, hAdj.symm, Category.assoc]

end RiemannResearch.AlgebraicGeometry
