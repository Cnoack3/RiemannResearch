/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.FpqcModuleDescent
import Mathlib.RingTheory.IsTensorProduct

/-!
# The affine Čech module base-change isomorphism

This file constructs the objectwise tensor-product isomorphism underlying the
comparison between affine Čech descent data and coalgebras for the
extension--restriction comonad.  For an `A`-module `M`, it identifies

`(A ⊗[R] A) ⊗[A, left] M`, restricted along the right inclusion, with
`A ⊗[R] M`.

The construction is an application of Mathlib's
`Algebra.IsPushout.cancelBaseChange`.  In particular, the ordering of the two
tensor factors records the convention that the right inclusion supplies the
output `A`-module structure.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory

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

/-- The objectwise tensor-product base-change isomorphism on the double overlap.

The source extends an `A`-module along the left inclusion into `A ⊗[R] A` and
then restricts along the right inclusion.  The target first restricts to `R`
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
  let e' : X ≃ₗ[A] Y := by
    dsimp [X, Y, ModuleCat.extendScalars, ModuleCat.restrictScalars,
      ModuleCat.ExtendScalars.obj', ModuleCat.RestrictScalars.obj',
      CategoryTheory.Functor.comp]
    exact e
  let eAdd :
      (CategoryTheory.forget₂ (ModuleCat A) AddCommGrpCat).obj X ≅
        (CategoryTheory.forget₂ (ModuleCat A) AddCommGrpCat).obj Y :=
    AddEquiv.toAddCommGrpIso e'.toAddEquiv
  refine ModuleCat.isoMk eAdd ?_
  intro a
  ext x
  change AddCommGrpCat.Hom.hom (Y.smul a) (e' x) =
    e' (AddCommGrpCat.Hom.hom (X.smul a) x)
  exact (e'.map_smul a x).symm

end RiemannResearch.AlgebraicGeometry
