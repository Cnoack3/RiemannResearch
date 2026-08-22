/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.AffineCechModuleBaseChange
import RiemannResearch.AlgebraicGeometry.AffineModuleComonadicTransport

/-!
# The affine module descent--comonadic bridge

This file identifies choice-free singleton affine module descent data with
coalgebras for the extension--restriction comonad. The construction is
unconditional in the ring map. Its comparison compatibility specializes
faithfully flat comonadicity to effective affine Čech descent and the
singleton stack condition.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace RiemannResearch.AlgebraicGeometry

private theorem extendRestrictScalars_unit_apply
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (M : ModuleCat R) (m : M) :
    ModuleCat.Hom.hom ((ModuleCat.extendRestrictScalarsAdj f).unit.app M) m =
      (show ↑((ModuleCat.restrictScalars f).obj (ModuleCat.of S S))
        from (1 : S)) ⊗ₜ[R] m := by
  rfl

private theorem extendScalars_smul_tmul
    {S T : Type u} [CommRing S] [CommRing T]
    (g : S →+* T) (N : ModuleCat S) (t s : T) (n : N) :
    t • (show ↑((ModuleCat.extendScalars g).obj N) from
      (show ↑((ModuleCat.restrictScalars g).obj (ModuleCat.of T T))
        from s) ⊗ₜ[S] n) =
    (show ↑((ModuleCat.extendScalars g).obj N) from
      (show ↑((ModuleCat.restrictScalars g).obj (ModuleCat.of T T))
        from t * s) ⊗ₜ[S] n) := by
  rfl

private theorem extendRestrictScalars_linearMap_ext_one_tmul
    {R A Z : Type u} [CommRing R] [CommRing A]
    [AddCommGroup Z] [Module A Z]
    (f : R →+* A) (M : ModuleCat A)
    (L K : ↑((ModuleCat.restrictScalars f ⋙
      ModuleCat.extendScalars f).obj M) →ₗ[A] Z)
    (hgen : ∀ m : M,
      L ((1 : A) ⊗ₜ[R, f] m) = K ((1 : A) ⊗ₜ[R, f] m)) :
    L = K := by
  apply LinearMap.ext
  intro x
  let x' : TensorProduct R
      ↑((ModuleCat.restrictScalars f).obj (ModuleCat.of A A))
      ↑((ModuleCat.restrictScalars f).obj M) := x
  change L (show ↑((ModuleCat.restrictScalars f ⋙
      ModuleCat.extendScalars f).obj M) from x') =
    K (show ↑((ModuleCat.restrictScalars f ⋙
      ModuleCat.extendScalars f).obj M) from x')
  refine TensorProduct.induction_on x' ?_ ?_ ?_
  · change L 0 = K 0
    rw [map_zero, map_zero]
  · intro a m
    let aA : A := a
    let mM : M := m
    let one : ↑((ModuleCat.restrictScalars f ⋙
        ModuleCat.extendScalars f).obj M) :=
      (show ↑((ModuleCat.restrictScalars f).obj (ModuleCat.of A A))
        from (1 : A)) ⊗ₜ[R]
      (show ↑((ModuleCat.restrictScalars f).obj M) from mM)
    have ha := extendScalars_smul_tmul f
      ((ModuleCat.restrictScalars f).obj M)
      aA 1 (show ↑((ModuleCat.restrictScalars f).obj M) from mM)
    rw [mul_one] at ha
    change L (show ↑((ModuleCat.restrictScalars f ⋙
        ModuleCat.extendScalars f).obj M) from a ⊗ₜ[R] m) =
      K (show ↑((ModuleCat.restrictScalars f ⋙
        ModuleCat.extendScalars f).obj M) from a ⊗ₜ[R] m)
    rw [← ha]
    rw [map_smul, map_smul]
    exact congrArg (fun z => aA • z) (hgen mM)
  · intro p q hp hq
    change L ((show ↑((ModuleCat.restrictScalars f ⋙
        ModuleCat.extendScalars f).obj M) from p) +
      (show ↑((ModuleCat.restrictScalars f ⋙
        ModuleCat.extendScalars f).obj M) from q)) =
      K ((show ↑((ModuleCat.restrictScalars f ⋙
        ModuleCat.extendScalars f).obj M) from p) +
      (show ↑((ModuleCat.restrictScalars f ⋙
        ModuleCat.extendScalars f).obj M) from q))
    rw [map_add, map_add, hp, hq]

private theorem extendScalarsComp_inv_app_one_tmul
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T)
    (M : ModuleCat.{u} R) (m : M) :
    (ModuleCat.extendScalarsComp f g).inv.app M
        ((1 : T) ⊗ₜ[S, g] ((1 : S) ⊗ₜ[R, f] m)) =
      (1 : T) ⊗ₜ[R, g.comp f] m := by
  let x : ↑((ModuleCat.extendScalars (g.comp f)).obj M) :=
    (1 : T) ⊗ₜ[R, g.comp f] m
  let y : ↑((ModuleCat.extendScalars g).obj
      ((ModuleCat.extendScalars f).obj M)) :=
    (1 : T) ⊗ₜ[S, g] ((1 : S) ⊗ₜ[R, f] m)
  have hhom :
      (ModuleCat.extendScalarsComp f g).hom.app M x = y := by
    exact ModuleCat.extendScalarsComp_hom_app_one_tmul f g M m
  calc
    (ModuleCat.extendScalarsComp f g).inv.app M y =
        (ModuleCat.extendScalarsComp f g).inv.app M
          ((ModuleCat.extendScalarsComp f g).hom.app M x) := by
      rw [hhom]
    _ = x := by
      have hi := (ModuleCat.extendScalarsComp f g).hom_inv_id_app M
      have hi' := congrArg (fun q => ModuleCat.Hom.hom q x) hi
      exact hi'

private theorem extendScalars_map_one_tmul
    {A C : Type u} [CommRing A] [CommRing C]
    (g : A →+* C) {M N : ModuleCat.{u} A}
    (q : M ⟶ N) (m : M) :
    (ModuleCat.extendScalars g).map q
        (show ↑((ModuleCat.extendScalars g).obj M) from
          (show ↑((ModuleCat.restrictScalars g).obj
            (ModuleCat.of C C)) from (1 : C)) ⊗ₜ[A] m) =
      (show ↑((ModuleCat.extendScalars g).obj N) from
        (show ↑((ModuleCat.restrictScalars g).obj
          (ModuleCat.of C C)) from (1 : C)) ⊗ₜ[A] q m) := by
  let _ : Algebra A C := g.toAlgebra
  change (LinearMap.baseChange C (ModuleCat.Hom.hom q))
    ((1 : C) ⊗ₜ[A] m) = _
  exact LinearMap.baseChange_tmul _ _ _

private theorem affineModuleComonadicCompatibleComp
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    {Y : CommRingCat.{u}ᵒᵖ} (q : Y ⟶ Opposite.op R)
    (f₁ f₂ : Y ⟶ Opposite.op A)
    (hf₁ : f₁ ≫ f.op = q) (hf₂ : f₂ ≫ f.op = q) :
    f₁.unop.hom.comp f.hom = f₂.unop.hom.comp f.hom := by
  ext r
  have h₁ := congrArg
    (fun k : Y ⟶ Opposite.op R => k.unop.hom r) hf₁
  have h₂ := congrArg
    (fun k : Y ⟶ Opposite.op R => k.unop.hom r) hf₂
  exact h₁.trans h₂.symm

private theorem affineModuleComonadicRawCompat
    {R A B C : Type u} [CommRing R] [CommRing A]
    [CommRing B] [CommRing C]
    (f : R →+* A) (g₁ g₂ : A →+* B) (k : B →+* C)
    (h : g₁.comp f = g₂.comp f) :
    (k.comp g₁).comp f = (k.comp g₂).comp f :=
  (RingHom.comp_assoc f g₁ k).trans <|
    (congrArg (fun q => k.comp q) h).trans <|
      (RingHom.comp_assoc f g₂ k).symm

set_option maxRecDepth 10000 in
set_option linter.style.haveILetI false in
/-- Generic comonadic transport is stable under postcomposition of compatible
algebra maps. -/
theorem affineModuleComonadicTransport_postcomp
    {R A B C : Type u} [CommRing R] [CommRing A]
    [CommRing B] [CommRing C]
    (f : R →+* A) (g₁ g₂ : A →+* B) (k : B →+* C)
    (h : g₁.comp f = g₂.comp f) (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalarsComp g₁ k).hom.app
        ((ModuleCat.extendRestrictScalarsAdj f).toComonad.obj M) ≫
      (ModuleCat.extendScalars k).map
        ((affineModuleComonadicTransport f g₁ g₂ h).app M) ≫
      (ModuleCat.extendScalarsComp g₂ k).inv.app M =
    (affineModuleComonadicTransport f (k.comp g₁) (k.comp g₂)
      (affineModuleComonadicRawCompat f g₁ g₂ k h)).app M := by
  let G := (ModuleCat.extendRestrictScalarsAdj f).toComonad
  let adj := ModuleCat.extendRestrictScalarsAdj (k.comp g₁)
  let Z := (ModuleCat.restrictScalars (k.comp g₁)).obj
    ((ModuleCat.extendScalars (k.comp g₂)).obj M)
  let L : ↑((ModuleCat.restrictScalars f ⋙
      ModuleCat.extendScalars f).obj M) →ₗ[A] ↑Z :=
    ModuleCat.Hom.hom (adj.homEquiv (G.obj M)
      ((ModuleCat.extendScalars (k.comp g₂)).obj M)
      ((ModuleCat.extendScalarsComp g₁ k).hom.app (G.obj M) ≫
        (ModuleCat.extendScalars k).map
          ((affineModuleComonadicTransport f g₁ g₂ h).app M) ≫
        (ModuleCat.extendScalarsComp g₂ k).inv.app M))
  let K : ↑((ModuleCat.restrictScalars f ⋙
      ModuleCat.extendScalars f).obj M) →ₗ[A] ↑Z :=
    ModuleCat.Hom.hom (adj.homEquiv (G.obj M)
      ((ModuleCat.extendScalars (k.comp g₂)).obj M)
      ((affineModuleComonadicTransport f (k.comp g₁) (k.comp g₂)
        (affineModuleComonadicRawCompat f g₁ g₂ k h)).app M))
  apply (adj.homEquiv (G.obj M)
    ((ModuleCat.extendScalars (k.comp g₂)).obj M)).injective
  apply ModuleCat.hom_ext
  change L = K
  refine extendRestrictScalars_linearMap_ext_one_tmul
    (Z := ↑Z) f M L K ?_
  intro m
  dsimp only [L, K]
  rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply]
  let x : G.obj M := (1 : A) ⊗ₜ[R, f] m
  let z₀ : (ModuleCat.extendScalars (k.comp g₁)).obj (G.obj M) :=
    (1 : C) ⊗ₜ[A, k.comp g₁] x
  let z₁ : (ModuleCat.extendScalars k).obj
      ((ModuleCat.extendScalars g₁).obj (G.obj M)) :=
    (1 : C) ⊗ₜ[B, k]
      ((1 : B) ⊗ₜ[A, g₁] x)
  let z₂ : (ModuleCat.extendScalars k).obj
      ((ModuleCat.extendScalars g₂).obj M) :=
    (1 : C) ⊗ₜ[B, k]
      ((1 : B) ⊗ₜ[A, g₂] m)
  let z₃ : (ModuleCat.extendScalars (k.comp g₂)).obj M :=
    (1 : C) ⊗ₜ[A, k.comp g₂] m
  have hu := extendRestrictScalars_unit_apply
    (k.comp g₁) (G.obj M) x
  change (ModuleCat.extendRestrictScalarsAdj
    (k.comp g₁)).unit.app (G.obj M) x = z₀ at hu
  change
    ((ModuleCat.extendScalarsComp g₁ k).hom.app (G.obj M) ≫
      (ModuleCat.extendScalars k).map
        ((affineModuleComonadicTransport f g₁ g₂ h).app M) ≫
      (ModuleCat.extendScalarsComp g₂ k).inv.app M)
        ((ModuleCat.extendRestrictScalarsAdj
          (k.comp g₁)).unit.app (G.obj M) x) =
      (affineModuleComonadicTransport f (k.comp g₁) (k.comp g₂)
        (affineModuleComonadicRawCompat f g₁ g₂ k h)).app M
        ((ModuleCat.extendRestrictScalarsAdj
          (k.comp g₁)).unit.app (G.obj M) x)
  rw [hu]
  have hc₁ :
      (ModuleCat.extendScalarsComp g₁ k).hom.app (G.obj M) z₀ = z₁ := by
    exact ModuleCat.extendScalarsComp_hom_app_one_tmul g₁ k (G.obj M) x
  change
    (ModuleCat.extendScalarsComp g₂ k).inv.app M
        ((ModuleCat.extendScalars k).map
          ((affineModuleComonadicTransport f g₁ g₂ h).app M)
          ((ModuleCat.extendScalarsComp g₁ k).hom.app (G.obj M) z₀)) =
      (affineModuleComonadicTransport f (k.comp g₁) (k.comp g₂)
        (affineModuleComonadicRawCompat f g₁ g₂ k h)).app M z₀
  rw [hc₁]
  have hm := extendScalars_map_one_tmul k
    ((affineModuleComonadicTransport f g₁ g₂ h).app M)
    ((1 : B) ⊗ₜ[A, g₁] x)
  change (ModuleCat.extendScalars k).map
      ((affineModuleComonadicTransport f g₁ g₂ h).app M) z₁ =
    (1 : C) ⊗ₜ[B, k]
      ((affineModuleComonadicTransport f g₁ g₂ h).app M
        ((1 : B) ⊗ₜ[A, g₁] x)) at hm
  rw [hm]
  have ht := affineModuleComonadicTransport_app_one_tmul
    f g₁ g₂ h M m
  change (affineModuleComonadicTransport f g₁ g₂ h).app M
      ((1 : B) ⊗ₜ[A, g₁] x) =
    (1 : B) ⊗ₜ[A, g₂] m at ht
  rw [ht]
  have hc₂ := extendScalarsComp_inv_app_one_tmul g₂ k M m
  change (ModuleCat.extendScalarsComp g₂ k).inv.app M z₂ = z₃ at hc₂
  change
    (ModuleCat.extendScalarsComp g₂ k).inv.app M z₂ =
      (affineModuleComonadicTransport f (k.comp g₁) (k.comp g₂)
        (affineModuleComonadicRawCompat f g₁ g₂ k h)).app M z₀
  rw [hc₂]
  exact (affineModuleComonadicTransport_app_one_tmul
    f (k.comp g₁) (k.comp g₂)
      (affineModuleComonadicRawCompat f g₁ g₂ k h) M m).symm

set_option linter.style.haveILetI false in
/-- Generic comonadic transport on the canonical tensor-square pair is the
inverse of the affine Čech base-change isomorphism under adjunction. -/
theorem affineModuleComonadicTransport_canonicalPair
    {R A : CommRingCat.{u}} (f : R ⟶ A) (M : ModuleCat A) :
    letI : Algebra R A := f.hom.toAlgebra
    ((ModuleCat.extendRestrictScalarsAdj
        (Algebra.TensorProduct.includeRight.toRingHom :
          A →+* TensorProduct R A A)).homEquiv
      ((ModuleCat.extendRestrictScalarsAdj f.hom).toComonad.obj M)
      ((ModuleCat.extendScalars
        (Algebra.TensorProduct.includeLeftRingHom :
          A →+* TensorProduct R A A)).obj M))
      ((affineModuleComonadicTransport f.hom
        (Algebra.TensorProduct.includeRight.toRingHom :
          A →+* TensorProduct R A A)
        (Algebra.TensorProduct.includeLeftRingHom :
          A →+* TensorProduct R A A)
        (affineTensorPair_comp_eq f)).app M)
      = (affineTensorCechBaseChangeIso f).inv.app M := by
  letI : Algebra R A := f.hom.toAlgebra
  rw [Adjunction.homEquiv_apply]
  apply ModuleCat.hom_ext
  apply extendRestrictScalars_linearMap_ext_one_tmul f.hom M
  intro m
  let x : ↑((ModuleCat.extendRestrictScalarsAdj f.hom).toComonad.obj M) :=
    (1 : A) ⊗ₜ[R, f.hom] m
  let y : ↑((ModuleCat.extendScalars
      (Algebra.TensorProduct.includeRight.toRingHom :
        A →+* TensorProduct R A A)).obj
      ((ModuleCat.extendRestrictScalarsAdj f.hom).toComonad.obj M)) :=
    (1 : TensorProduct R A A) ⊗ₜ[A,
      Algebra.TensorProduct.includeRight.toRingHom] x
  change
    ModuleCat.Hom.hom
      ((affineModuleComonadicTransport f.hom
        (Algebra.TensorProduct.includeRight.toRingHom :
          A →+* TensorProduct R A A)
        (Algebra.TensorProduct.includeLeftRingHom :
          A →+* TensorProduct R A A)
        (affineTensorPair_comp_eq f)).app M)
      (ModuleCat.Hom.hom
        ((ModuleCat.extendRestrictScalarsAdj
          (Algebra.TensorProduct.includeRight.toRingHom :
            A →+* TensorProduct R A A)).unit.app
              ((ModuleCat.extendRestrictScalarsAdj f.hom).toComonad.obj M)) x) =
    ModuleCat.Hom.hom ((affineTensorCechBaseChangeIso f).inv.app M) x
  have hu := extendRestrictScalars_unit_apply
    (Algebra.TensorProduct.includeRight.toRingHom :
      A →+* TensorProduct R A A)
    ((ModuleCat.extendRestrictScalarsAdj f.hom).toComonad.obj M) x
  change ModuleCat.Hom.hom
      ((ModuleCat.extendRestrictScalarsAdj
        (Algebra.TensorProduct.includeRight.toRingHom :
          A →+* TensorProduct R A A)).unit.app
          ((ModuleCat.extendRestrictScalarsAdj f.hom).toComonad.obj M)) x = y at hu
  rw [hu]
  have hk := affineModuleComonadicTransport_app_one_tmul f.hom
    (Algebra.TensorProduct.includeRight.toRingHom :
      A →+* TensorProduct R A A)
    (Algebra.TensorProduct.includeLeftRingHom :
      A →+* TensorProduct R A A)
    (affineTensorPair_comp_eq f) M m
  change ModuleCat.Hom.hom
      ((affineModuleComonadicTransport f.hom
        (Algebra.TensorProduct.includeRight.toRingHom :
          A →+* TensorProduct R A A)
        (Algebra.TensorProduct.includeLeftRingHom :
          A →+* TensorProduct R A A)
        (affineTensorPair_comp_eq f)).app M) y =
    (1 : TensorProduct R A A) ⊗ₜ[A,
      Algebra.TensorProduct.includeLeftRingHom] m at hk
  rw [hk]
  have hb := affineTensorCechBaseChangeIso_inv_app_one_tmul f M m
  change ModuleCat.Hom.hom
      ((affineTensorCechBaseChangeIso f).inv.app M) x =
    (1 : TensorProduct R A A) ⊗ₜ[A,
      Algebra.TensorProduct.includeLeftRingHom] m at hb
  exact hb.symm

private theorem rawCompat
    {R A B C : Type u} [CommRing R] [CommRing A]
    [CommRing B] [CommRing C]
    (f : R →+* A) (g₁ g₂ : A →+* B) (k : B →+* C)
    (h : g₁.comp f = g₂.comp f) :
    (k.comp g₁).comp f = (k.comp g₂).comp f :=
  affineModuleComonadicRawCompat f g₁ g₂ k h

private theorem compatibleComp
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    {Y : CommRingCat.{u}ᵒᵖ} (q : Y ⟶ Opposite.op R)
    (f₁ f₂ : Y ⟶ Opposite.op A)
    (hf₁ : f₁ ≫ f.op = q) (hf₂ : f₂ ≫ f.op = q) :
    f₁.unop.hom.comp f.hom = f₂.unop.hom.comp f.hom :=
  affineModuleComonadicCompatibleComp f q f₁ f₂ hf₁ hf₂

/-- The raw transported coaction between two compatible scalar extensions. -/
noncomputable def rawT
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g₁ g₂ : A →+* B)
    (h : g₁.comp f = g₂.comp f) (M : ModuleCat.{u} A)
    (a : M ⟶ (ModuleCat.extendRestrictScalarsAdj f).toComonad.obj M) :
    (ModuleCat.extendScalars g₁).obj M ⟶
      (ModuleCat.extendScalars g₂).obj M :=
  (ModuleCat.extendScalars g₁).map a ≫
    (affineModuleComonadicTransport f g₁ g₂ h).app M

theorem rawT_postcomp
    {R A B C : Type u} [CommRing R] [CommRing A]
    [CommRing B] [CommRing C]
    (f : R →+* A) (g₁ g₂ : A →+* B) (k : B →+* C)
    (h : g₁.comp f = g₂.comp f) (M : ModuleCat A)
    (a : M ⟶ (ModuleCat.extendRestrictScalarsAdj f).toComonad.obj M) :
    (ModuleCat.extendScalarsComp g₁ k).hom.app M ≫
      (ModuleCat.extendScalars k).map (rawT f g₁ g₂ h M a) ≫
      (ModuleCat.extendScalarsComp g₂ k).inv.app M =
    rawT f (k.comp g₁) (k.comp g₂) (rawCompat f g₁ g₂ k h) M a := by
  dsimp only [rawT]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (ModuleCat.extendScalarsComp g₁ k).hom.naturality a
  dsimp at hn
  slice_lhs 1 2 => exact hn.symm
  slice_lhs 2 4 =>
    exact affineModuleComonadicTransport_postcomp f g₁ g₂ k h M

theorem rawT_pullHom
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (M : ModuleCat A)
    (a : M ⟶ (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad.obj M)
    {Y' Y : CommRingCat.{u}ᵒᵖ} (g : Y' ⟶ Y)
    (f₁ f₂ : Y ⟶ Opposite.op A)
    (gf₁ gf₂ : Y' ⟶ Opposite.op A)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    (h : f₁.unop.hom.comp f.hom = f₂.unop.hom.comp f.hom)
    (h' : gf₁.unop.hom.comp f.hom = gf₂.unop.hom.comp f.hom) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (F := affineModulePseudofunctor)
      (rawT f.hom f₁.unop.hom f₂.unop.hom h M a)
      g gf₁ gf₂ hgf₁ hgf₂ =
    rawT f.hom gf₁.unop.hom gf₂.unop.hom h' M a := by
  subst gf₁
  subst gf₂
  simp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  have hmc₁ :
      affineModulePseudofunctor.mapComp'
        f₁.op.toLoc g.op.toLoc (g ≫ f₁).op.toLoc =
      affineModulePseudofunctor.mapComp f₁.op.toLoc g.op.toLoc := by
    apply Pseudofunctor.mapComp'_eq_mapComp
  have hmc₂ :
      affineModulePseudofunctor.mapComp'
        f₂.op.toLoc g.op.toLoc (g ≫ f₂).op.toLoc =
      affineModulePseudofunctor.mapComp f₂.op.toLoc g.op.toLoc := by
    apply Pseudofunctor.mapComp'_eq_mapComp
  rw [hmc₁, hmc₂]
  change
    (ModuleCat.extendScalarsComp f₁.unop.hom g.unop.hom).hom.app M ≫
      (ModuleCat.extendScalars g.unop.hom).map
        (rawT f.hom f₁.unop.hom f₂.unop.hom h M a) ≫
      (ModuleCat.extendScalarsComp f₂.unop.hom g.unop.hom).inv.app M =
    rawT f.hom
      (g.unop.hom.comp f₁.unop.hom)
      (g.unop.hom.comp f₂.unop.hom) h' M a
  exact rawT_postcomp f.hom f₁.unop.hom f₂.unop.hom
    g.unop.hom h M a

set_option linter.style.haveILetI false in
private theorem rawT_eq_descentHom_canonical
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (D : AffineModuleDescentData f) :
    letI : Algebra R A := f.hom.toAlgebra
    let pair := affineCechPair f
    rawT f.hom pair.p₁.unop.hom pair.p₂.unop.hom
        (affineTensorPair_comp_eq f) (D.obj PUnit.unit)
        (affineModuleDescentCoaction f D) =
      D.hom pair.p (i₁ := PUnit.unit) (i₂ := PUnit.unit)
        pair.p₁ pair.p₂ pair.hp₁ pair.hp₂ := by
  letI : Algebra R A := f.hom.toAlgebra
  let M : ModuleCat A := D.obj PUnit.unit
  let GM : ModuleCat A :=
    (ModuleCat.restrictScalars f.hom ⋙ ModuleCat.extendScalars f.hom).obj M
  let pair := affineCechPair f
  let gR : A →+* TensorProduct R A A :=
    Algebra.TensorProduct.includeRight.toRingHom
  let gL : A →+* TensorProduct R A A :=
    Algebra.TensorProduct.includeLeftRingHom
  let θ : (ModuleCat.extendScalars gR).obj M ⟶
      (ModuleCat.extendScalars gL).obj M :=
    D.hom pair.p (i₁ := PUnit.unit) (i₂ := PUnit.unit)
      pair.p₁ pair.p₂ pair.hp₁ pair.hp₂
  let adj := ModuleCat.extendRestrictScalarsAdj gR
  let e := affineTensorCechBaseChangeIso f
  let κ : (ModuleCat.extendScalars gR).obj GM ⟶
      (ModuleCat.extendScalars gL).obj M :=
    (affineModuleComonadicTransport f.hom gR gL
      (affineTensorPair_comp_eq f)).app M
  have hcanonical :
      adj.homEquiv GM ((ModuleCat.extendScalars gL).obj M) κ =
        e.inv.app M := by
    exact affineModuleComonadicTransport_canonicalPair f M
  change (ModuleCat.extendScalars gR).map
      (adj.homEquiv M ((ModuleCat.extendScalars gL).obj M) θ ≫
        e.hom.app M) ≫ κ = θ
  apply (adj.homEquiv M ((ModuleCat.extendScalars gL).obj M)).injective
  rw [adj.homEquiv_naturality_left]
  change (adj.homEquiv M ((ModuleCat.extendScalars gL).obj M) θ ≫
      e.hom.app M) ≫
    adj.homEquiv GM ((ModuleCat.extendScalars gL).obj M) κ =
      adj.homEquiv M ((ModuleCat.extendScalars gL).obj M) θ
  rw [hcanonical, Category.assoc, Iso.hom_inv_id_app]
  exact Category.comp_id _

set_option linter.style.haveILetI false in
private theorem rawT_eq_descentHom
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (D : AffineModuleDescentData f)
    (a : D.obj PUnit.unit ⟶
      (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad.obj
        (D.obj PUnit.unit))
    (hcanonical :
      letI : Algebra R A := f.hom.toAlgebra
      let pair := affineCechPair f
      rawT f.hom pair.p₁.unop.hom pair.p₂.unop.hom
          (affineTensorPair_comp_eq f) (D.obj PUnit.unit) a =
        D.hom pair.p (i₁ := PUnit.unit) (i₂ := PUnit.unit)
          pair.p₁ pair.p₂ pair.hp₁ pair.hp₂)
    {Y : CommRingCat.{u}ᵒᵖ} (q : Y ⟶ Opposite.op R)
    (f₁ f₂ : Y ⟶ Opposite.op A)
    (hf₁ : f₁ ≫ f.op = q) (hf₂ : f₂ ≫ f.op = q) :
    rawT f.hom f₁.unop.hom f₂.unop.hom
        (compatibleComp f q f₁ f₂ hf₁ hf₂)
        (D.obj PUnit.unit) a =
      D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit)
        f₁ f₂ hf₁ hf₂ := by
  letI : Algebra R A := f.hom.toAlgebra
  let pair := affineCechPair f
  change rawT f.hom pair.p₁.unop.hom pair.p₂.unop.hom
      (affineTensorPair_comp_eq f) (D.obj PUnit.unit) a =
    D.hom pair.p (i₁ := PUnit.unit) (i₂ := PUnit.unit)
      pair.p₁ pair.p₂ pair.hp₁ pair.hp₂ at hcanonical
  let lk := PullbackCone.IsLimit.lift' pair.isLimit f₁ f₂
    (hf₁.trans hf₂.symm)
  let k : Y ⟶ pair.pullback := lk.1
  have hk₁ : k ≫ pair.p₁ = f₁ := lk.2.1
  have hk₂ : k ≫ pair.p₂ = f₂ := lk.2.2
  have hkq : k ≫ pair.p = q := by
    calc
      k ≫ pair.p = k ≫ (pair.p₁ ≫ f.op) := by rw [pair.hp₁]
      _ = (k ≫ pair.p₁) ≫ f.op := (Category.assoc _ _ _).symm
      _ = q := by rw [hk₁, hf₁]
  calc
    _ = Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := affineModulePseudofunctor)
        (rawT f.hom pair.p₁.unop.hom pair.p₂.unop.hom
          (affineTensorPair_comp_eq f) (D.obj PUnit.unit) a)
        k f₁ f₂ hk₁ hk₂ := by
      symm
      exact rawT_pullHom f (D.obj PUnit.unit) a k
        pair.p₁ pair.p₂ f₁ f₂ hk₁ hk₂
        (affineTensorPair_comp_eq f)
        (compatibleComp f q f₁ f₂ hf₁ hf₂)
    _ = Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := affineModulePseudofunctor)
        (D.hom pair.p (i₁ := PUnit.unit) (i₂ := PUnit.unit)
          pair.p₁ pair.p₂ pair.hp₁ pair.hp₂)
        k f₁ f₂ hk₁ hk₂ := by
      exact congrArg
        (fun z => Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := affineModulePseudofunctor) z k f₁ f₂ hk₁ hk₂)
        hcanonical
    _ = _ := D.pullHom_hom k pair.p q hkq
      (i₁ := PUnit.unit) (i₂ := PUnit.unit)
      pair.p₁ pair.p₂ pair.hp₁ pair.hp₂
      f₁ f₂ hk₁ hk₂

private theorem extendScalarsId_map_injective
    {A : Type u} [CommRing A] {M N : ModuleCat.{u} A}
    {p q : M ⟶ N}
    (h : (ModuleCat.extendScalars.{u, u, u} (RingHom.id A)).map p =
      (ModuleCat.extendScalars.{u, u, u} (RingHom.id A)).map q) :
    p = q := by
  rw [← (cancel_epi ((ModuleCat.extendScalarsId A).hom.app M))]
  have hp := (ModuleCat.extendScalarsId A).hom.naturality p
  have hq := (ModuleCat.extendScalarsId A).hom.naturality q
  dsimp at hp hq
  rw [← hp, ← hq, h]

private theorem candidateCoalgebra_counit_of_transport_self
    {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (M : ModuleCat.{u} A)
    (a : M ⟶ (ModuleCat.extendRestrictScalarsAdj f).toComonad.obj M)
    (hself :
      (ModuleCat.extendScalars (RingHom.id A)).map a ≫
          (affineModuleComonadicTransport f
            (RingHom.id A) (RingHom.id A) rfl).app M =
        𝟙 ((ModuleCat.extendScalars (RingHom.id A)).obj M)) :
    a ≫ (ModuleCat.extendRestrictScalarsAdj f).toComonad.ε.app M =
      𝟙 M := by
  rw [affineModuleComonadicTransport_self] at hself
  apply extendScalarsId_map_injective
  rw [Functor.map_comp]
  exact hself.trans
    ((ModuleCat.extendScalars (RingHom.id A)).map_id M).symm

private theorem affineModuleDescentCoaction_identityAgreement
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (D : AffineModuleDescentData f) :
    let M : ModuleCat A := D.obj PUnit.unit
    rawT f.hom (RingHom.id A) (RingHom.id A) rfl M
        (affineModuleDescentCoaction f D) =
      𝟙 ((ModuleCat.extendScalars (RingHom.id A)).obj M) := by
  let M : ModuleCat A := D.obj PUnit.unit
  let a := affineModuleDescentCoaction f D
  have ha := rawT_eq_descentHom f D a
    (rawT_eq_descentHom_canonical f D)
    f.op (𝟙 (Opposite.op A)) (𝟙 (Opposite.op A))
    (Category.id_comp _) (Category.id_comp _)
  change rawT f.hom (RingHom.id A) (RingHom.id A) rfl M a =
    D.hom f.op (i₁ := PUnit.unit) (i₂ := PUnit.unit)
      (𝟙 (Opposite.op A)) (𝟙 (Opposite.op A))
      (Category.id_comp _) (Category.id_comp _) at ha
  have hs := D.hom_self f.op
    (i := PUnit.unit) (𝟙 (Opposite.op A)) (Category.id_comp _)
  change D.hom f.op (i₁ := PUnit.unit) (i₂ := PUnit.unit)
      (𝟙 (Opposite.op A)) (𝟙 (Opposite.op A))
      (Category.id_comp _) (Category.id_comp _) =
    𝟙 ((ModuleCat.extendScalars (RingHom.id A)).obj M) at hs
  exact ha.trans hs

/-- The canonical coaction satisfies the comonad counit law. -/
theorem affineModuleDescentCoaction_counit
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (D : AffineModuleDescentData f) :
    affineModuleDescentCoaction f D ≫
        (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad.ε.app
          (D.obj PUnit.unit) =
      𝟙 (D.obj PUnit.unit) := by
  apply candidateCoalgebra_counit_of_transport_self f.hom
    (D.obj PUnit.unit) (affineModuleDescentCoaction f D)
  exact affineModuleDescentCoaction_identityAgreement f D

private theorem outer_leftAlgebra_eq
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] :
    (Algebra.TensorProduct.includeLeftRingHom :
      S →+* TensorProduct R S T).toAlgebra =
      (Algebra.TensorProduct.leftAlgebra :
        Algebra S (TensorProduct R S T)) := by
  apply Algebra.algebra_ext
  intro s
  change Algebra.TensorProduct.includeLeftRingHom s = s ⊗ₜ[R] 1
  exact Algebra.TensorProduct.includeLeftRingHom_apply s

private theorem outer_rightAlgebra_eq
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] :
    (Algebra.TensorProduct.includeRight.toRingHom :
      T →+* TensorProduct R S T).toAlgebra =
      (Algebra.TensorProduct.rightAlgebra :
        Algebra T (TensorProduct R S T)) := by
  apply Algebra.algebra_ext
  intro t
  change Algebra.TensorProduct.includeRight t = 1 ⊗ₜ[R] t
  exact Algebra.TensorProduct.includeRight_apply t

private theorem outer_pushout
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [algRS : Algebra R S] [algRT : Algebra R T]
    (leftAlg : Algebra S (TensorProduct R S T))
    (hleft : leftAlg = Algebra.TensorProduct.leftAlgebra)
    (rightAlg : Algebra T (TensorProduct R S T))
    (hright : rightAlg = Algebra.TensorProduct.rightAlgebra)
    (towerLeft : @IsScalarTower R S (TensorProduct R S T)
      algRS.toSMul leftAlg.toSMul
      Algebra.TensorProduct.instAlgebra.toSMul)
    (towerRight : @IsScalarTower R T (TensorProduct R S T)
      algRT.toSMul rightAlg.toSMul
      Algebra.TensorProduct.instAlgebra.toSMul) :
    @Algebra.IsPushout R S _ _ algRS T (TensorProduct R S T) _ _
      algRT leftAlg rightAlg Algebra.TensorProduct.instAlgebra
      towerRight towerLeft := by
  subst leftAlg
  subst rightAlg
  exact @TensorProduct.isPushout R S T _ _ _ algRS algRT

set_option linter.style.haveILetI false in
private noncomputable def outerCancelLinearEquiv
    {R A : CommRingCat.{u}} (f : R ⟶ A) (M : ModuleCat.{u} A) :
    letI algRA : Algebra R A := f.hom.toAlgebra
    let B := TensorProduct R A A
    let iL : A →+* B := Algebra.TensorProduct.includeLeftRingHom
    letI algRB : Algebra R B := (iL.comp f.hom).toAlgebra
    let C := @TensorProduct R _ B A _ _ algRB.toModule algRA.toModule
    let oL : B →+* C :=
      @Algebra.TensorProduct.includeLeftRingHom R B A _ _ algRB _ algRA
    let oR : A →+* C :=
      (@Algebra.TensorProduct.includeRight R B A _ _ algRB _ algRA).toRingHom
    let X := (ModuleCat.extendScalars (iL.comp f.hom)).obj
        ((ModuleCat.restrictScalars f.hom).obj M)
    let Y := (ModuleCat.restrictScalars oL).obj
        ((ModuleCat.extendScalars oR).obj M)
    (X : Type u) ≃ₗ[B] (Y : Type u) := by
  letI algRA : Algebra R A := f.hom.toAlgebra
  let B := TensorProduct R A A
  let iL : A →+* B := Algebra.TensorProduct.includeLeftRingHom
  letI algRB : Algebra R B := (iL.comp f.hom).toAlgebra
  let C := @TensorProduct R _ B A _ _ algRB.toModule algRA.toModule
  let oL : B →+* C :=
    @Algebra.TensorProduct.includeLeftRingHom R B A _ _ algRB _ algRA
  let oR : A →+* C :=
    (@Algebra.TensorProduct.includeRight R B A _ _ algRB _ algRA).toRingHom
  let X := (ModuleCat.extendScalars (iL.comp f.hom)).obj
      ((ModuleCat.restrictScalars f.hom).obj M)
  let Y := (ModuleCat.restrictScalars oL).obj
      ((ModuleCat.extendScalars oR).obj M)
  letI modRM : Module R M := Module.compHom M f.hom
  letI towerRAM : IsScalarTower R A M :=
    IsScalarTower.of_algebraMap_smul (by intro r m; rfl)
  let leftAlg : Algebra B C := oL.toAlgebra
  have hleft : leftAlg =
      (Algebra.TensorProduct.leftAlgebra : Algebra B C) := by
    dsimp [leftAlg, oL, C]
    exact @outer_leftAlgebra_eq R B A _ _ _ algRB algRA
  let rightAlg : Algebra A C := oR.toAlgebra
  have hright : rightAlg =
      (Algebra.TensorProduct.rightAlgebra : Algebra A C) := by
    dsimp [rightAlg, oR, C]
    exact @outer_rightAlgebra_eq R B A _ _ _ algRB algRA
  let towerLeft : @IsScalarTower R B C
      algRB.toSMul leftAlg.toSMul
      Algebra.TensorProduct.instAlgebra.toSMul := by
    rw [hleft]
    infer_instance
  let towerRight : @IsScalarTower R A C
      algRA.toSMul rightAlg.toSMul
      Algebra.TensorProduct.instAlgebra.toSMul := by
    rw [hright]
    infer_instance
  let pushout := @outer_pushout R B A _ _ _ algRB algRA
    leftAlg hleft rightAlg hright towerLeft towerRight
  let e := @Algebra.IsPushout.cancelBaseChange R B _ _ algRB
    A C _ _ algRA Algebra.TensorProduct.instAlgebra
    rightAlg leftAlg towerRight towerLeft pushout
    M _ modRM (inferInstance : Module A M) towerRAM
  dsimp [X, Y, ModuleCat.extendScalars, ModuleCat.restrictScalars,
    ModuleCat.ExtendScalars.obj', ModuleCat.RestrictScalars.obj',
    CategoryTheory.Functor.comp]
  exact e.symm

set_option linter.style.haveILetI false in
private noncomputable def outerCancelApp
    {R A : CommRingCat.{u}} (f : R ⟶ A) (M : ModuleCat.{u} A) :
    letI algRA : Algebra R A := f.hom.toAlgebra
    let B := TensorProduct R A A
    let iL : A →+* B := Algebra.TensorProduct.includeLeftRingHom
    letI algRB : Algebra R B := (iL.comp f.hom).toAlgebra
    let C := @TensorProduct R _ B A _ _ algRB.toModule algRA.toModule
    let oL : B →+* C :=
      @Algebra.TensorProduct.includeLeftRingHom R B A _ _ algRB _ algRA
    let oR : A →+* C :=
      (@Algebra.TensorProduct.includeRight R B A _ _ algRB _ algRA).toRingHom
    (ModuleCat.extendScalars (iL.comp f.hom)).obj
        ((ModuleCat.restrictScalars f.hom).obj M) ≅
      (ModuleCat.restrictScalars oL).obj
        ((ModuleCat.extendScalars oR).obj M) := by
  letI algRA : Algebra R A := f.hom.toAlgebra
  let B := TensorProduct R A A
  let iL : A →+* B := Algebra.TensorProduct.includeLeftRingHom
  letI algRB : Algebra R B := (iL.comp f.hom).toAlgebra
  let C := @TensorProduct R _ B A _ _ algRB.toModule algRA.toModule
  let oL : B →+* C :=
    @Algebra.TensorProduct.includeLeftRingHom R B A _ _ algRB _ algRA
  let oR : A →+* C :=
    (@Algebra.TensorProduct.includeRight R B A _ _ algRB _ algRA).toRingHom
  let X := (ModuleCat.extendScalars (iL.comp f.hom)).obj
      ((ModuleCat.restrictScalars f.hom).obj M)
  let Y := (ModuleCat.restrictScalars oL).obj
      ((ModuleCat.extendScalars oR).obj M)
  let e : (X : Type u) ≃ₗ[B] (Y : Type u) :=
    outerCancelLinearEquiv f M
  let eAdd :
      (CategoryTheory.forget₂ (ModuleCat B) AddCommGrpCat).obj X ≅
        (CategoryTheory.forget₂ (ModuleCat B) AddCommGrpCat).obj Y :=
    AddEquiv.toAddCommGrpIso e.toAddEquiv
  refine ModuleCat.isoMk eAdd ?_
  intro b
  ext x
  change AddCommGrpCat.Hom.hom (Y.smul b) (e x) =
    e (AddCommGrpCat.Hom.hom (X.smul b) x)
  exact (e.map_smul b x).symm

set_option linter.style.haveILetI false in
private theorem innerCompInv_one_tmul
    {R A : CommRingCat.{u}} (f : R ⟶ A) (M : ModuleCat.{u} A)
    (m : M) :
    letI : Algebra R A := f.hom.toAlgebra
    let B := TensorProduct R A A
    let iL : A →+* B := Algebra.TensorProduct.includeLeftRingHom
    let mR : (ModuleCat.restrictScalars f.hom).obj M := m
    (ModuleCat.extendScalarsComp f.hom iL).inv.app
        ((ModuleCat.restrictScalars f.hom).obj M)
        ((1 : B) ⊗ₜ[A, iL] ((1 : A) ⊗ₜ[R, f.hom] mR)) =
      (1 : B) ⊗ₜ[R, iL.comp f.hom] mR := by
  letI : Algebra R A := f.hom.toAlgebra
  let B := TensorProduct R A A
  let iL : A →+* B := Algebra.TensorProduct.includeLeftRingHom
  let mR : (ModuleCat.restrictScalars f.hom).obj M := m
  exact extendScalarsComp_inv_app_one_tmul f.hom iL
    ((ModuleCat.restrictScalars f.hom).obj M) mR

set_option linter.style.haveILetI false in
private theorem outerCancelApp_hom_one_tmul
    {R A : CommRingCat.{u}} (f : R ⟶ A) (M : ModuleCat.{u} A)
    (m : M) :
    letI algRA : Algebra R A := f.hom.toAlgebra
    let B := TensorProduct R A A
    let iL : A →+* B := Algebra.TensorProduct.includeLeftRingHom
    letI algRB : Algebra R B := (iL.comp f.hom).toAlgebra
    let C := @TensorProduct R _ B A _ _ algRB.toModule algRA.toModule
    let oR : A →+* C :=
      (@Algebra.TensorProduct.includeRight R B A _ _ algRB _ algRA).toRingHom
    let mR : (ModuleCat.restrictScalars f.hom).obj M := m
    (outerCancelApp f M).hom
        ((1 : B) ⊗ₜ[R, iL.comp f.hom] mR) =
      (1 : C) ⊗ₜ[A, oR] m := by
  letI algRA : Algebra R A := f.hom.toAlgebra
  let B := TensorProduct R A A
  let iL : A →+* B := Algebra.TensorProduct.includeLeftRingHom
  letI algRB : Algebra R B := (iL.comp f.hom).toAlgebra
  let C := @TensorProduct R _ B A _ _ algRB.toModule algRA.toModule
  let oL : B →+* C :=
    @Algebra.TensorProduct.includeLeftRingHom R B A _ _ algRB _ algRA
  let oR : A →+* C :=
    (@Algebra.TensorProduct.includeRight R B A _ _ algRB _ algRA).toRingHom
  let mR : (ModuleCat.restrictScalars f.hom).obj M := m
  change (outerCancelLinearEquiv f M)
      ((1 : B) ⊗ₜ[R, iL.comp f.hom] mR) =
    (1 : C) ⊗ₜ[A, oR] m
  let algRA' : Algebra R A := f.hom.toAlgebra
  let modRM : Module R M := Module.compHom M f.hom
  let towerRAM : IsScalarTower R A M :=
    IsScalarTower.of_algebraMap_smul (by intro r m'; rfl)
  let leftAlg : Algebra B C := oL.toAlgebra
  have hleft : leftAlg =
      (Algebra.TensorProduct.leftAlgebra : Algebra B C) := by
    dsimp [leftAlg, oL, C]
    exact @outer_leftAlgebra_eq R B A _ _ _ algRB algRA'
  let rightAlg : Algebra A C := oR.toAlgebra
  have hright : rightAlg =
      (Algebra.TensorProduct.rightAlgebra : Algebra A C) := by
    dsimp [rightAlg, oR, C]
    exact @outer_rightAlgebra_eq R B A _ _ _ algRB algRA'
  let towerLeft : @IsScalarTower R B C
      algRB.toSMul leftAlg.toSMul
      Algebra.TensorProduct.instAlgebra.toSMul := by
    rw [hleft]
    infer_instance
  let towerRight : @IsScalarTower R A C
      algRA'.toSMul rightAlg.toSMul
      Algebra.TensorProduct.instAlgebra.toSMul := by
    rw [hright]
    infer_instance
  let pushout := @outer_pushout R B A _ _ _
    algRB algRA' leftAlg hleft rightAlg hright towerLeft towerRight
  exact @Algebra.IsPushout.cancelBaseChange_symm_tmul
    R B _ _ algRB A C _ _ algRA'
    Algebra.TensorProduct.instAlgebra rightAlg leftAlg
    towerRight towerLeft pushout M _ modRM
    (inferInstance : Module A M) towerRAM (1 : B) m

set_option linter.style.haveILetI false in
private noncomputable def higherBaseChangeApp
    {R A : CommRingCat.{u}} (f : R ⟶ A) (M : ModuleCat.{u} A) :
    letI algRA : Algebra R A := f.hom.toAlgebra
    let B := TensorProduct R A A
    let iL : A →+* B := Algebra.TensorProduct.includeLeftRingHom
    letI algRB : Algebra R B := (iL.comp f.hom).toAlgebra
    let C := @TensorProduct R _ B A _ _ algRB.toModule algRA.toModule
    let oL : B →+* C :=
      @Algebra.TensorProduct.includeLeftRingHom R B A _ _ algRB _ algRA
    let oR : A →+* C :=
      (@Algebra.TensorProduct.includeRight R B A _ _ algRB _ algRA).toRingHom
    (ModuleCat.extendScalars iL).obj
        ((ModuleCat.extendRestrictScalarsAdj f.hom).toComonad.obj M) ≅
      (ModuleCat.restrictScalars oL).obj
        ((ModuleCat.extendScalars oR).obj M) := by
  letI algRA : Algebra R A := f.hom.toAlgebra
  let B := TensorProduct R A A
  let iL : A →+* B := Algebra.TensorProduct.includeLeftRingHom
  letI algRB : Algebra R B := (iL.comp f.hom).toAlgebra
  let C := @TensorProduct R _ B A _ _ algRB.toModule algRA.toModule
  let oL : B →+* C :=
    @Algebra.TensorProduct.includeLeftRingHom R B A _ _ algRB _ algRA
  let oR : A →+* C :=
    (@Algebra.TensorProduct.includeRight R B A _ _ algRB _ algRA).toRingHom
  exact (ModuleCat.extendScalarsComp f.hom iL).symm.app
      ((ModuleCat.restrictScalars f.hom).obj M) ≪≫
    outerCancelApp f M

set_option linter.style.haveILetI false in
@[simp] theorem higherBaseChangeApp_hom_one_tmul
    {R A : CommRingCat.{u}} (f : R ⟶ A) (M : ModuleCat.{u} A) (m : M) :
    letI algRA : Algebra R A := f.hom.toAlgebra
    let B := TensorProduct R A A
    let iL : A →+* B := Algebra.TensorProduct.includeLeftRingHom
    letI algRB : Algebra R B := (iL.comp f.hom).toAlgebra
    let C := @TensorProduct R _ B A _ _ algRB.toModule algRA.toModule
    let oR : A →+* C :=
      (@Algebra.TensorProduct.includeRight R B A _ _ algRB _ algRA).toRingHom
    let mR : (ModuleCat.restrictScalars f.hom).obj M := m
    (higherBaseChangeApp f M).hom
        ((1 : B) ⊗ₜ[A, iL] ((1 : A) ⊗ₜ[R, f.hom] mR)) =
      (1 : C) ⊗ₜ[A, oR] m := by
  letI algRA : Algebra R A := f.hom.toAlgebra
  let B := TensorProduct R A A
  let iL : A →+* B := Algebra.TensorProduct.includeLeftRingHom
  have hc := innerCompInv_one_tmul f M m
  letI algRB : Algebra R B := (iL.comp f.hom).toAlgebra
  let C := @TensorProduct R _ B A _ _ algRB.toModule algRA.toModule
  let oL : B →+* C :=
    @Algebra.TensorProduct.includeLeftRingHom R B A _ _ algRB _ algRA
  let oR : A →+* C :=
    (@Algebra.TensorProduct.includeRight R B A _ _ algRB _ algRA).toRingHom
  let mR : (ModuleCat.restrictScalars f.hom).obj M := m
  change (outerCancelApp f M).hom
      ((ModuleCat.extendScalarsComp f.hom iL).inv.app
        ((ModuleCat.restrictScalars f.hom).obj M)
        ((1 : B) ⊗ₜ[A, iL] ((1 : A) ⊗ₜ[R, f.hom] mR))) =
    (1 : C) ⊗ₜ[A, oR] m
  rw [hc]
  exact outerCancelApp_hom_one_tmul f M m

set_option linter.style.haveILetI false in
@[simp] theorem comonad_delta_baseChange_inv_one_tmul
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (M : ModuleCat A) (m : M) :
    letI : Algebra R A := f.hom.toAlgebra
    let G := (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad
    let mR : (ModuleCat.restrictScalars f.hom).obj M := m
    (G.δ.app M ≫ (affineTensorCechBaseChangeIso f).inv.app (G.obj M))
        ((1 : A) ⊗ₜ[R, f.hom] mR) =
      (1 : TensorProduct R A A) ⊗ₜ[A,
        (Algebra.TensorProduct.includeLeftRingHom :
          A →+* TensorProduct R A A)]
        ((1 : A) ⊗ₜ[R, f.hom] mR) := by
  letI : Algebra R A := f.hom.toAlgebra
  let G := (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad
  let mR : (ModuleCat.restrictScalars f.hom).obj M := m
  change
    (affineTensorCechBaseChangeIso f).inv.app (G.obj M)
        ((1 : A) ⊗ₜ[R, f.hom]
          ((1 : A) ⊗ₜ[R, f.hom] mR)) =
      (1 : TensorProduct R A A) ⊗ₜ[A,
        (Algebra.TensorProduct.includeLeftRingHom :
          A →+* TensorProduct R A A)]
        ((1 : A) ⊗ₜ[R, f.hom] mR)
  exact affineTensorCechBaseChangeIso_inv_app_one_tmul f
    (G.obj M) ((1 : A) ⊗ₜ[R, f.hom] mR)

private theorem extendScalars_hom_ext_one_tmul
    {A C : Type u} [CommRing A] [CommRing C]
    (g : A →+* C) (M : ModuleCat.{u} A) (N : ModuleCat.{u} C)
    (L K : (ModuleCat.extendScalars g).obj M ⟶ N)
    (h : ∀ m : M,
      L ((1 : C) ⊗ₜ[A, g] m) =
        K ((1 : C) ⊗ₜ[A, g] m)) :
    L = K := by
  let adj := ModuleCat.extendRestrictScalarsAdj g
  apply (adj.homEquiv M N).injective
  rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply]
  apply ModuleCat.hom_ext
  ext m
  exact h m

private theorem homEquiv_symm_one_tmul
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (M : ModuleCat A) (N : ModuleCat B)
    (p : M ⟶ (ModuleCat.restrictScalars g).obj N) (m : M) :
    ((ModuleCat.extendRestrictScalarsAdj g).homEquiv M N).symm p
      ((1 : B) ⊗ₜ[A, g] m) = p m := by
  rw [Adjunction.homEquiv_symm_apply]
  change (1 : B) • p m = p m
  simp

private theorem comp_homEquiv_symm_one_tmul
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (i : A →+* B) (o : B →+* C)
    (M : ModuleCat A) (N : ModuleCat C)
    (p : (ModuleCat.extendScalars i).obj M ⟶
      (ModuleCat.restrictScalars o).obj N)
    (m : M) :
    ((ModuleCat.extendScalarsComp i o).hom.app M ≫
      ((ModuleCat.extendRestrictScalarsAdj o).homEquiv
        ((ModuleCat.extendScalars i).obj M) N).symm p)
        (show ↑((ModuleCat.extendScalars (o.comp i)).obj M) from
          (show ↑((ModuleCat.restrictScalars (o.comp i)).obj
              (ModuleCat.of C C)) from (1 : C)) ⊗ₜ[A] m) =
      p (show ↑((ModuleCat.extendScalars i).obj M) from
        (show ↑((ModuleCat.restrictScalars i).obj
            (ModuleCat.of B B)) from (1 : B)) ⊗ₜ[A] m) := by
  change
    ((ModuleCat.extendRestrictScalarsAdj o).homEquiv
      ((ModuleCat.extendScalars i).obj M) N).symm p
        ((ModuleCat.extendScalarsComp i o).hom.app M
          (show ↑((ModuleCat.extendScalars (o.comp i)).obj M) from
            (show ↑((ModuleCat.restrictScalars (o.comp i)).obj
                (ModuleCat.of C C)) from (1 : C)) ⊗ₜ[A] m)) = _
  rw [ModuleCat.extendScalarsComp_hom_app_one_tmul]
  rw [Adjunction.homEquiv_symm_apply]
  change (1 : C) • p (show ↑((ModuleCat.extendScalars i).obj M) from
    (show ↑((ModuleCat.restrictScalars i).obj
      (ModuleCat.of B B)) from (1 : B)) ⊗ₜ[A] m) = _
  simp

set_option maxRecDepth 10000 in
set_option linter.style.haveILetI false in
private theorem delta_higher_eq_transport
    {R A : CommRingCat.{u}} (f : R ⟶ A) (M : ModuleCat.{u} A) :
    letI algRA : Algebra R A := f.hom.toAlgebra
    let G := (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad
    let B := TensorProduct R A A
    let iL : A →+* B := Algebra.TensorProduct.includeLeftRingHom
    let iR : A →+* B := Algebra.TensorProduct.includeRight.toRingHom
    letI algRB : Algebra R B := (iL.comp f.hom).toAlgebra
    let C := @TensorProduct R _ B A _ _ algRB.toModule algRA.toModule
    let oL : B →+* C :=
      @Algebra.TensorProduct.includeLeftRingHom R B A _ _ algRB _ algRA
    let oR : A →+* C :=
      (@Algebra.TensorProduct.includeRight R B A _ _ algRB _ algRA).toRingHom
    let j₂ := oL.comp iR
    let h₂₃ : j₂.comp f.hom = oR.comp f.hom := by
      change (oL.comp iR).comp f.hom = oR.comp f.hom
      rw [RingHom.comp_assoc, affineTensorPair_comp_eq f]
      exact @Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
        R B A _ _ algRB _ algRA
    G.δ.app M ≫ (affineTensorCechBaseChangeIso f).inv.app (G.obj M) ≫
        (ModuleCat.restrictScalars iR).map (higherBaseChangeApp f M).hom =
      (ModuleCat.extendRestrictScalarsAdj j₂).homEquiv (G.obj M)
          ((ModuleCat.extendScalars oR).obj M)
          ((affineModuleComonadicTransport f.hom j₂ oR h₂₃).app M) ≫
        (ModuleCat.restrictScalarsComp iR oL).hom.app
          ((ModuleCat.extendScalars oR).obj M) := by
  letI algRA : Algebra R A := f.hom.toAlgebra
  let G := (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad
  let B := TensorProduct R A A
  let iL : A →+* B := Algebra.TensorProduct.includeLeftRingHom
  let iR : A →+* B := Algebra.TensorProduct.includeRight.toRingHom
  letI algRB : Algebra R B := (iL.comp f.hom).toAlgebra
  let C := @TensorProduct R _ B A _ _ algRB.toModule algRA.toModule
  let oL : B →+* C :=
    @Algebra.TensorProduct.includeLeftRingHom R B A _ _ algRB _ algRA
  let oR : A →+* C :=
    (@Algebra.TensorProduct.includeRight R B A _ _ algRB _ algRA).toRingHom
  let j₂ := oL.comp iR
  let h₂₃ : j₂.comp f.hom = oR.comp f.hom := by
    change (oL.comp iR).comp f.hom = oR.comp f.hom
    rw [RingHom.comp_assoc, affineTensorPair_comp_eq f]
    exact @Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      R B A _ _ algRB _ algRA
  apply ModuleCat.hom_ext
  apply extendRestrictScalars_linearMap_ext_one_tmul f.hom M
  intro m
  let mR : (ModuleCat.restrictScalars f.hom).obj M := m
  let x : G.obj M := (1 : A) ⊗ₜ[R, f.hom] mR
  let y : (ModuleCat.extendScalars oR).obj M :=
    (1 : C) ⊗ₜ[A, oR] m
  have hd := comonad_delta_baseChange_inv_one_tmul f M m
  change
    (higherBaseChangeApp f M).hom
      ((G.δ.app M ≫ (affineTensorCechBaseChangeIso f).inv.app (G.obj M)) x) =
    (ModuleCat.restrictScalarsComp iR oL).hom.app
      ((ModuleCat.extendScalars oR).obj M)
      ((ModuleCat.extendRestrictScalarsAdj j₂).homEquiv (G.obj M)
        ((ModuleCat.extendScalars oR).obj M)
        ((affineModuleComonadicTransport f.hom j₂ oR h₂₃).app M) x)
  have hleft :
      (higherBaseChangeApp f M).hom
        ((G.δ.app M ≫ (affineTensorCechBaseChangeIso f).inv.app (G.obj M)) x) =
      y := by
    rw [hd]
    exact higherBaseChangeApp_hom_one_tmul f M m
  have hright :
      (ModuleCat.extendRestrictScalarsAdj j₂).homEquiv (G.obj M)
        ((ModuleCat.extendScalars oR).obj M)
        ((affineModuleComonadicTransport f.hom j₂ oR h₂₃).app M) x =
      y := by
    rw [Adjunction.homEquiv_apply]
    change (affineModuleComonadicTransport f.hom j₂ oR h₂₃).app M
      ((1 : C) ⊗ₜ[A, j₂] x) = y
    exact affineModuleComonadicTransport_app_one_tmul
      f.hom j₂ oR h₂₃ M m
  rw [hleft, hright]
  rfl

set_option maxRecDepth 10000 in
set_option linter.style.haveILetI false in
private theorem unit_higher_eq_transport13
    {R A : CommRingCat.{u}} (f : R ⟶ A) (M : ModuleCat.{u} A) :
    letI algRA : Algebra R A := f.hom.toAlgebra
    let G := (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad
    let B := TensorProduct R A A
    let iL : A →+* B := Algebra.TensorProduct.includeLeftRingHom
    letI algRB : Algebra R B := (iL.comp f.hom).toAlgebra
    let C := @TensorProduct R _ B A _ _ algRB.toModule algRA.toModule
    let oL : B →+* C :=
      @Algebra.TensorProduct.includeLeftRingHom R B A _ _ algRB _ algRA
    let oR : A →+* C :=
      (@Algebra.TensorProduct.includeRight R B A _ _ algRB _ algRA).toRingHom
    let j₁ := oL.comp iL
    let h₁₃ : j₁.comp f.hom = oR.comp f.hom := by
      change (oL.comp iL).comp f.hom = oR.comp f.hom
      rw [RingHom.comp_assoc]
      change oL.comp (algebraMap R B) = oR.comp f.hom
      exact @Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
        R B A _ _ algRB _ algRA
    (ModuleCat.extendRestrictScalarsAdj iL).unit.app (G.obj M) ≫
        (ModuleCat.restrictScalars iL).map (higherBaseChangeApp f M).hom =
      (ModuleCat.extendRestrictScalarsAdj j₁).homEquiv (G.obj M)
          ((ModuleCat.extendScalars oR).obj M)
          ((affineModuleComonadicTransport f.hom j₁ oR h₁₃).app M) ≫
        (ModuleCat.restrictScalarsComp iL oL).hom.app
          ((ModuleCat.extendScalars oR).obj M) := by
  letI algRA : Algebra R A := f.hom.toAlgebra
  let G := (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad
  let B := TensorProduct R A A
  let iL : A →+* B := Algebra.TensorProduct.includeLeftRingHom
  letI algRB : Algebra R B := (iL.comp f.hom).toAlgebra
  let C := @TensorProduct R _ B A _ _ algRB.toModule algRA.toModule
  let oL : B →+* C :=
    @Algebra.TensorProduct.includeLeftRingHom R B A _ _ algRB _ algRA
  let oR : A →+* C :=
    (@Algebra.TensorProduct.includeRight R B A _ _ algRB _ algRA).toRingHom
  let j₁ := oL.comp iL
  let h₁₃ : j₁.comp f.hom = oR.comp f.hom := by
    change (oL.comp iL).comp f.hom = oR.comp f.hom
    rw [RingHom.comp_assoc]
    change oL.comp (algebraMap R B) = oR.comp f.hom
    exact @Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      R B A _ _ algRB _ algRA
  apply ModuleCat.hom_ext
  apply extendRestrictScalars_linearMap_ext_one_tmul f.hom M
  intro m
  let mR : (ModuleCat.restrictScalars f.hom).obj M := m
  let x : G.obj M := (1 : A) ⊗ₜ[R, f.hom] mR
  let xB : (ModuleCat.extendScalars iL).obj (G.obj M) :=
    (1 : B) ⊗ₜ[A, iL] x
  let y : (ModuleCat.extendScalars oR).obj M :=
    (1 : C) ⊗ₜ[A, oR] m
  change
    (higherBaseChangeApp f M).hom
        ((ModuleCat.extendRestrictScalarsAdj iL).unit.app (G.obj M) x) =
      (ModuleCat.restrictScalarsComp iL oL).hom.app
        ((ModuleCat.extendScalars oR).obj M)
        ((ModuleCat.extendRestrictScalarsAdj j₁).homEquiv
          (G.obj M) ((ModuleCat.extendScalars oR).obj M)
          ((affineModuleComonadicTransport f.hom j₁ oR h₁₃).app M) x)
  have hu := extendRestrictScalars_unit_apply iL (G.obj M) x
  change (ModuleCat.extendRestrictScalarsAdj iL).unit.app
    (G.obj M) x = xB at hu
  have hleft :
      (higherBaseChangeApp f M).hom
          ((ModuleCat.extendRestrictScalarsAdj iL).unit.app (G.obj M) x) =
        y := by
    rw [hu]
    exact higherBaseChangeApp_hom_one_tmul f M m
  have hright :
      (ModuleCat.extendRestrictScalarsAdj j₁).homEquiv
          (G.obj M) ((ModuleCat.extendScalars oR).obj M)
          ((affineModuleComonadicTransport f.hom j₁ oR h₁₃).app M) x =
        y := by
    rw [Adjunction.homEquiv_apply]
    change (affineModuleComonadicTransport f.hom j₁ oR h₁₃).app M
      ((1 : C) ⊗ₜ[A, j₁] x) = y
    exact affineModuleComonadicTransport_app_one_tmul
      f.hom j₁ oR h₁₃ M m
  rw [hleft, hright]
  rfl

private theorem qL_direct_of_delta_higher
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (iR iL : A →+* B) (oL : B →+* C) (oR : A →+* C)
    (M GM : ModuleCat.{u} A) (a : M ⟶ GM)
    (d : GM ⟶ (ModuleCat.restrictScalars iR).obj
      ((ModuleCat.extendScalars iL).obj GM))
    (β : (ModuleCat.extendScalars iL).obj GM ≅
      (ModuleCat.restrictScalars oL).obj
        ((ModuleCat.extendScalars oR).obj M))
    (k : (ModuleCat.extendScalars (oL.comp iR)).obj GM ⟶
      (ModuleCat.extendScalars oR).obj M)
    (hd : d ≫ (ModuleCat.restrictScalars iR).map β.hom =
      (ModuleCat.extendRestrictScalarsAdj (oL.comp iR)).homEquiv
          GM ((ModuleCat.extendScalars oR).obj M) k ≫
        (ModuleCat.restrictScalarsComp iR oL).hom.app
          ((ModuleCat.extendScalars oR).obj M)) :
    (ModuleCat.extendScalarsComp iR oL).hom.app M ≫
        ((ModuleCat.extendRestrictScalarsAdj oL).homEquiv
          ((ModuleCat.extendScalars iR).obj M)
          ((ModuleCat.extendScalars oR).obj M)).symm
          (((ModuleCat.extendRestrictScalarsAdj iR).homEquiv M
            ((ModuleCat.extendScalars iL).obj GM)).symm
              (a ≫ d) ≫ β.hom) =
      (ModuleCat.extendScalars (oL.comp iR)).map a ≫ k := by
  apply extendScalars_hom_ext_one_tmul (oL.comp iR) M
    ((ModuleCat.extendScalars oR).obj M)
  intro m
  let p :=
    ((ModuleCat.extendRestrictScalarsAdj iR).homEquiv M
      ((ModuleCat.extendScalars iL).obj GM)).symm (a ≫ d) ≫ β.hom
  have hc := comp_homEquiv_symm_one_tmul iR oL M
    ((ModuleCat.extendScalars oR).obj M) p m
  have hi := homEquiv_symm_one_tmul iR M
    ((ModuleCat.extendScalars iL).obj GM) (a ≫ d) m
  change
    ((ModuleCat.extendRestrictScalarsAdj iR).homEquiv M
      ((ModuleCat.extendScalars iL).obj GM)).symm (a ≫ d)
        (show ↑((ModuleCat.extendScalars iR).obj M) from
          (show ↑((ModuleCat.restrictScalars iR).obj
            (ModuleCat.of B B)) from (1 : B)) ⊗ₜ[A] m) =
      (a ≫ d) m at hi
  have hm := extendScalars_map_one_tmul (oL.comp iR) a m
  have hdapp := congrArg
    (fun q => q (a m)) (congrArg ConcreteCategory.hom hd)
  change
    ((ModuleCat.extendScalarsComp iR oL).hom.app M ≫
      ((ModuleCat.extendRestrictScalarsAdj oL).homEquiv
        ((ModuleCat.extendScalars iR).obj M)
        ((ModuleCat.extendScalars oR).obj M)).symm p)
        (show ↑((ModuleCat.extendScalars (oL.comp iR)).obj M) from
          (show ↑((ModuleCat.restrictScalars (oL.comp iR)).obj
            (ModuleCat.of C C)) from (1 : C)) ⊗ₜ[A] m) =
      ((ModuleCat.extendScalars (oL.comp iR)).map a ≫ k)
        (show ↑((ModuleCat.extendScalars (oL.comp iR)).obj M) from
          (show ↑((ModuleCat.restrictScalars (oL.comp iR)).obj
            (ModuleCat.of C C)) from (1 : C)) ⊗ₜ[A] m)
  rw [hc]
  change β.hom
      (((ModuleCat.extendRestrictScalarsAdj iR).homEquiv M
        ((ModuleCat.extendScalars iL).obj GM)).symm (a ≫ d)
          (show ↑((ModuleCat.extendScalars iR).obj M) from
            (show ↑((ModuleCat.restrictScalars iR).obj
              (ModuleCat.of B B)) from (1 : B)) ⊗ₜ[A] m)) =
    k ((ModuleCat.extendScalars (oL.comp iR)).map a
      (show ↑((ModuleCat.extendScalars (oL.comp iR)).obj M) from
        (show ↑((ModuleCat.restrictScalars (oL.comp iR)).obj
          (ModuleCat.of C C)) from (1 : C)) ⊗ₜ[A] m))
  rw [hi, hm]
  rw [Adjunction.homEquiv_apply] at hdapp
  change β.hom (d (a m)) =
    k (show ↑((ModuleCat.extendScalars (oL.comp iR)).obj GM) from
      (show ↑((ModuleCat.restrictScalars (oL.comp iR)).obj
        (ModuleCat.of C C)) from (1 : C)) ⊗ₜ[A] a m)
  change β.hom (d (a m)) =
    k (show ↑((ModuleCat.extendScalars (oL.comp iR)).obj GM) from
      (show ↑((ModuleCat.restrictScalars (oL.comp iR)).obj
        (ModuleCat.of C C)) from (1 : C)) ⊗ₜ[A] a m) at hdapp
  exact hdapp

private theorem q13_direct_of_unit_higher
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (i : A →+* B) (o : B →+* C) (oR : A →+* C)
    (M GM : ModuleCat.{u} A) (a : M ⟶ GM)
    (β : (ModuleCat.extendScalars i).obj GM ≅
      (ModuleCat.restrictScalars o).obj
        ((ModuleCat.extendScalars oR).obj M))
    (k : (ModuleCat.extendScalars (o.comp i)).obj GM ⟶
      (ModuleCat.extendScalars oR).obj M)
    (hd : (ModuleCat.extendRestrictScalarsAdj i).unit.app GM ≫
          (ModuleCat.restrictScalars i).map β.hom =
        (ModuleCat.extendRestrictScalarsAdj (o.comp i)).homEquiv
            GM ((ModuleCat.extendScalars oR).obj M) k ≫
          (ModuleCat.restrictScalarsComp i o).hom.app
            ((ModuleCat.extendScalars oR).obj M)) :
    (ModuleCat.extendScalarsComp i o).hom.app M ≫
        ((ModuleCat.extendRestrictScalarsAdj o).homEquiv
          ((ModuleCat.extendScalars i).obj M)
          ((ModuleCat.extendScalars oR).obj M)).symm
          ((ModuleCat.extendScalars i).map a ≫ β.hom) =
      (ModuleCat.extendScalars (o.comp i)).map a ≫ k := by
  let adj := ModuleCat.extendRestrictScalarsAdj i
  let d := adj.unit.app GM
  have hq := qL_direct_of_delta_higher i i o oR M GM a d β k hd
  have ha : (adj.homEquiv M ((ModuleCat.extendScalars i).obj GM)).symm
          (a ≫ d) = (ModuleCat.extendScalars i).map a := by
    calc
      _ = (ModuleCat.extendScalars i).map a ≫
          (adj.homEquiv GM ((ModuleCat.extendScalars i).obj GM)).symm d :=
        adj.homEquiv_naturality_left_symm a d
      _ = _ := by
        dsimp only [d]
        rw [adj.homEquiv_symm_unit]
        simp
  rw [← ha]
  exact hq

set_option linter.style.haveILetI false in
private theorem qR_inner_eq
    {R A : CommRingCat.{u}} (f : R ⟶ A) (M : ModuleCat.{u} A)
    (a : M ⟶
      (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad.obj M) :
    letI : Algebra R A := f.hom.toAlgebra
    let G := (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad
    let iR : A →+* TensorProduct R A A :=
      Algebra.TensorProduct.includeRight.toRingHom
    let iL : A →+* TensorProduct R A A :=
      Algebra.TensorProduct.includeLeftRingHom
    let adj := ModuleCat.extendRestrictScalarsAdj iR
    let e := affineTensorCechBaseChangeIso f
    (adj.homEquiv M
      ((ModuleCat.extendScalars iL).obj (G.obj M))).symm
        ((a ≫ G.map a) ≫ e.inv.app (G.obj M)) =
      rawT f.hom iR iL (affineTensorPair_comp_eq f) M a ≫
        (ModuleCat.extendScalars iL).map a := by
  letI : Algebra R A := f.hom.toAlgebra
  let G := (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad
  let iR : A →+* TensorProduct R A A :=
    Algebra.TensorProduct.includeRight.toRingHom
  let iL : A →+* TensorProduct R A A :=
    Algebra.TensorProduct.includeLeftRingHom
  let adj := ModuleCat.extendRestrictScalarsAdj iR
  let e := affineTensorCechBaseChangeIso f
  apply (adj.homEquiv M
    ((ModuleCat.extendScalars iL).obj (G.obj M))).injective
  rw [Equiv.apply_symm_apply]
  rw [adj.homEquiv_naturality_right]
  dsimp only [rawT]
  rw [adj.homEquiv_naturality_left]
  rw [affineModuleComonadicTransport_canonicalPair f M]
  have hn := e.inv.naturality a
  change G.map a ≫ e.inv.app (G.obj M) =
    e.inv.app M ≫ (ModuleCat.restrictScalars iR).map
      ((ModuleCat.extendScalars iL).map a) at hn
  have hn' := congrArg (fun k => a ≫ k) hn
  change
    (a ≫ G.map a) ≫ e.inv.app (G.obj M) =
      (a ≫ e.inv.app M) ≫
        (ModuleCat.restrictScalars iR).map
          ((ModuleCat.extendScalars iL).map a)
  calc
    (a ≫ G.map a) ≫ e.inv.app (G.obj M) =
        a ≫ (G.map a ≫ e.inv.app (G.obj M)) := Category.assoc _ _ _
    _ = a ≫ (e.inv.app M ≫
        (ModuleCat.restrictScalars iR).map
          ((ModuleCat.extendScalars iL).map a)) := hn'
    _ = (a ≫ e.inv.app M) ≫
        (ModuleCat.restrictScalars iR).map
          ((ModuleCat.extendScalars iL).map a) :=
      (Category.assoc _ _ _).symm

private theorem outer_symm_factor
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (iR iL : A →+* B) (oL : B →+* C)
    (M : ModuleCat.{u} A) (N : ModuleCat.{u} C)
    (θ : (ModuleCat.extendScalars iR).obj M ⟶
      (ModuleCat.extendScalars iL).obj M)
    (l : (ModuleCat.extendScalars iL).obj M ⟶
      (ModuleCat.restrictScalars oL).obj N) :
    (ModuleCat.extendScalarsComp iR oL).hom.app M ≫
        ((ModuleCat.extendRestrictScalarsAdj oL).homEquiv
          ((ModuleCat.extendScalars iR).obj M) N).symm (θ ≫ l) =
      ((ModuleCat.extendScalarsComp iR oL).hom.app M ≫
          (ModuleCat.extendScalars oL).map θ ≫
          (ModuleCat.extendScalarsComp iL oL).inv.app M) ≫
        ((ModuleCat.extendScalarsComp iL oL).hom.app M ≫
          ((ModuleCat.extendRestrictScalarsAdj oL).homEquiv
            ((ModuleCat.extendScalars iL).obj M) N).symm l) := by
  rw [(ModuleCat.extendRestrictScalarsAdj oL).homEquiv_naturality_left_symm]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_app_assoc]

set_option maxRecDepth 10000 in
set_option linter.style.haveILetI false in
private theorem qL_direct_eq_rawT23
    {R A : CommRingCat.{u}} (f : R ⟶ A) (M : ModuleCat.{u} A)
    (a : M ⟶
      (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad.obj M) :
    letI algRA : Algebra R A := f.hom.toAlgebra
    let G := (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad
    let B := TensorProduct R A A
    let iL : A →+* B := Algebra.TensorProduct.includeLeftRingHom
    let iR : A →+* B := Algebra.TensorProduct.includeRight.toRingHom
    letI algRB : Algebra R B := (iL.comp f.hom).toAlgebra
    let C := @TensorProduct R _ B A _ _ algRB.toModule algRA.toModule
    let oL : B →+* C :=
      @Algebra.TensorProduct.includeLeftRingHom R B A _ _ algRB _ algRA
    let oR : A →+* C :=
      (@Algebra.TensorProduct.includeRight R B A _ _ algRB _ algRA).toRingHom
    let j₂ := oL.comp iR
    let h₂₃ : j₂.comp f.hom = oR.comp f.hom := by
      change (oL.comp iR).comp f.hom = oR.comp f.hom
      rw [RingHom.comp_assoc, affineTensorPair_comp_eq f]
      exact @Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
        R B A _ _ algRB _ algRA
    (ModuleCat.extendScalarsComp iR oL).hom.app M ≫
        ((ModuleCat.extendRestrictScalarsAdj oL).homEquiv
          ((ModuleCat.extendScalars iR).obj M)
          ((ModuleCat.extendScalars oR).obj M)).symm
          (((ModuleCat.extendRestrictScalarsAdj iR).homEquiv M
            ((ModuleCat.extendScalars iL).obj (G.obj M))).symm
              ((a ≫ G.δ.app M) ≫
                (affineTensorCechBaseChangeIso f).inv.app (G.obj M)) ≫
            (higherBaseChangeApp f M).hom) =
      rawT f.hom j₂ oR h₂₃ M a := by
  letI algRA : Algebra R A := f.hom.toAlgebra
  let G := (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad
  let B := TensorProduct R A A
  let iL : A →+* B := Algebra.TensorProduct.includeLeftRingHom
  let iR : A →+* B := Algebra.TensorProduct.includeRight.toRingHom
  letI algRB : Algebra R B := (iL.comp f.hom).toAlgebra
  let C := @TensorProduct R _ B A _ _ algRB.toModule algRA.toModule
  let oL : B →+* C :=
    @Algebra.TensorProduct.includeLeftRingHom R B A _ _ algRB _ algRA
  let oR : A →+* C :=
    (@Algebra.TensorProduct.includeRight R B A _ _ algRB _ algRA).toRingHom
  let j₂ := oL.comp iR
  let h₂₃ : j₂.comp f.hom = oR.comp f.hom := by
    change (oL.comp iR).comp f.hom = oR.comp f.hom
    rw [RingHom.comp_assoc, affineTensorPair_comp_eq f]
    exact @Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      R B A _ _ algRB _ algRA
  let e := affineTensorCechBaseChangeIso f
  let d := G.δ.app M ≫ e.inv.app (G.obj M)
  let β := higherBaseChangeApp f M
  let k := (affineModuleComonadicTransport f.hom j₂ oR h₂₃).app M
  have hd : d ≫ (ModuleCat.restrictScalars iR).map β.hom =
      (ModuleCat.extendRestrictScalarsAdj j₂).homEquiv
          (G.obj M) ((ModuleCat.extendScalars oR).obj M) k ≫
        (ModuleCat.restrictScalarsComp iR oL).hom.app
          ((ModuleCat.extendScalars oR).obj M) := by
    exact delta_higher_eq_transport f M
  have hq := qL_direct_of_delta_higher
    iR iL oL oR M (G.obj M) a d β k hd
  have ha :
      (a ≫ G.δ.app M) ≫ e.inv.app (G.obj M) = a ≫ d := by
    change
      (a ≫ G.δ.app M) ≫ e.inv.app (G.obj M) =
        a ≫ (G.δ.app M ≫ e.inv.app (G.obj M))
    exact Category.assoc _ _ _
  change
    (ModuleCat.extendScalarsComp iR oL).hom.app M ≫
        ((ModuleCat.extendRestrictScalarsAdj oL).homEquiv
          ((ModuleCat.extendScalars iR).obj M)
          ((ModuleCat.extendScalars oR).obj M)).symm
          (((ModuleCat.extendRestrictScalarsAdj iR).homEquiv M
            ((ModuleCat.extendScalars iL).obj (G.obj M))).symm
              ((a ≫ G.δ.app M) ≫ e.inv.app (G.obj M)) ≫ β.hom) =
      (ModuleCat.extendScalars j₂).map a ≫ k
  rw [ha]
  exact hq

set_option maxRecDepth 10000 in
set_option linter.style.haveILetI false in
private theorem qR_direct_eq_rawTcomp
    {R A : CommRingCat.{u}} (f : R ⟶ A) (M : ModuleCat.{u} A)
    (a : M ⟶ (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad.obj M) :
    letI algRA : Algebra R A := f.hom.toAlgebra
    let G := (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad
    let B := TensorProduct R A A
    let iL : A →+* B := Algebra.TensorProduct.includeLeftRingHom
    let iR : A →+* B := Algebra.TensorProduct.includeRight.toRingHom
    letI algRB : Algebra R B := (iL.comp f.hom).toAlgebra
    let C := @TensorProduct R _ B A _ _ algRB.toModule algRA.toModule
    let oL : B →+* C :=
      @Algebra.TensorProduct.includeLeftRingHom R B A _ _ algRB _ algRA
    let oR : A →+* C :=
      (@Algebra.TensorProduct.includeRight R B A _ _ algRB _ algRA).toRingHom
    let j₁ := oL.comp iL
    let j₂ := oL.comp iR
    let h₁₃ : j₁.comp f.hom = oR.comp f.hom := by
      change (oL.comp iL).comp f.hom = oR.comp f.hom
      rw [RingHom.comp_assoc]
      change oL.comp (algebraMap R B) = oR.comp f.hom
      exact @Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
        R B A _ _ algRB _ algRA
    let h₂₁ : j₂.comp f.hom = j₁.comp f.hom :=
      rawCompat f.hom iR iL oL (affineTensorPair_comp_eq f)
    let adjI := ModuleCat.extendRestrictScalarsAdj iR
    let adjO := ModuleCat.extendRestrictScalarsAdj oL
    let e := affineTensorCechBaseChangeIso f
    (ModuleCat.extendScalarsComp iR oL).hom.app M ≫
        (adjO.homEquiv ((ModuleCat.extendScalars iR).obj M)
          ((ModuleCat.extendScalars oR).obj M)).symm
          ((adjI.homEquiv M ((ModuleCat.extendScalars iL).obj (G.obj M))).symm
              ((a ≫ G.map a) ≫ e.inv.app (G.obj M)) ≫
            (higherBaseChangeApp f M).hom) =
      rawT f.hom j₂ j₁ h₂₁ M a ≫ rawT f.hom j₁ oR h₁₃ M a := by
  letI algRA : Algebra R A := f.hom.toAlgebra
  let G := (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad
  let B := TensorProduct R A A
  let iL : A →+* B := Algebra.TensorProduct.includeLeftRingHom
  let iR : A →+* B := Algebra.TensorProduct.includeRight.toRingHom
  letI algRB : Algebra R B := (iL.comp f.hom).toAlgebra
  let C := @TensorProduct R _ B A _ _ algRB.toModule algRA.toModule
  let oL : B →+* C :=
    @Algebra.TensorProduct.includeLeftRingHom R B A _ _ algRB _ algRA
  let oR : A →+* C :=
    (@Algebra.TensorProduct.includeRight R B A _ _ algRB _ algRA).toRingHom
  let j₁ := oL.comp iL
  let j₂ := oL.comp iR
  let h₁₃ : j₁.comp f.hom = oR.comp f.hom := by
    change (oL.comp iL).comp f.hom = oR.comp f.hom
    rw [RingHom.comp_assoc]
    change oL.comp (algebraMap R B) = oR.comp f.hom
    exact @Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      R B A _ _ algRB _ algRA
  let h₂₁ : j₂.comp f.hom = j₁.comp f.hom :=
    rawCompat f.hom iR iL oL (affineTensorPair_comp_eq f)
  let adjI := ModuleCat.extendRestrictScalarsAdj iR
  let adjO := ModuleCat.extendRestrictScalarsAdj oL
  let e := affineTensorCechBaseChangeIso f
  let θ := rawT f.hom iR iL (affineTensorPair_comp_eq f) M a
  let β := higherBaseChangeApp f M
  let l := (ModuleCat.extendScalars iL).map a ≫ β.hom
  let k₁₃ := (affineModuleComonadicTransport f.hom j₁ oR h₁₃).app M
  have hi := qR_inner_eq f M a
  have hf := outer_symm_factor iR iL oL M
    ((ModuleCat.extendScalars oR).obj M) θ l
  have hp := rawT_postcomp f.hom iR iL oL
    (affineTensorPair_comp_eq f) M a
  have h13map := q13_direct_of_unit_higher iL oL oR M (G.obj M)
    a β k₁₃ (unit_higher_eq_transport13 f M)
  change
    (ModuleCat.extendScalarsComp iR oL).hom.app M ≫
        (adjO.homEquiv ((ModuleCat.extendScalars iR).obj M)
          ((ModuleCat.extendScalars oR).obj M)).symm
          ((adjI.homEquiv M ((ModuleCat.extendScalars iL).obj (G.obj M))).symm
              ((a ≫ G.map a) ≫ e.inv.app (G.obj M)) ≫ β.hom) =
      rawT f.hom j₂ j₁ h₂₁ M a ≫ rawT f.hom j₁ oR h₁₃ M a
  rw [hi]
  change
    (ModuleCat.extendScalarsComp iR oL).hom.app M ≫
        (adjO.homEquiv ((ModuleCat.extendScalars iR).obj M)
          ((ModuleCat.extendScalars oR).obj M)).symm
          ((θ ≫ (ModuleCat.extendScalars iL).map a) ≫ β.hom) =
      rawT f.hom j₂ j₁ h₂₁ M a ≫ rawT f.hom j₁ oR h₁₃ M a
  rw [Category.assoc]
  change
    (ModuleCat.extendScalarsComp iR oL).hom.app M ≫
        (adjO.homEquiv ((ModuleCat.extendScalars iR).obj M)
          ((ModuleCat.extendScalars oR).obj M)).symm (θ ≫ l) =
      rawT f.hom j₂ j₁ h₂₁ M a ≫ rawT f.hom j₁ oR h₁₃ M a
  rw [hf, hp, h13map]
  dsimp only [rawT]

set_option linter.style.haveILetI false in
private theorem rawT_cocycle_of_canonical
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (D : AffineModuleDescentData f)
    (a : D.obj PUnit.unit ⟶
      (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad.obj
        (D.obj PUnit.unit))
    (hcanonical :
      letI : Algebra R A := f.hom.toAlgebra
      let pair := affineCechPair f
      rawT f.hom pair.p₁.unop.hom pair.p₂.unop.hom
          (affineTensorPair_comp_eq f) (D.obj PUnit.unit) a =
        D.hom pair.p (i₁ := PUnit.unit) (i₂ := PUnit.unit)
          pair.p₁ pair.p₂ pair.hp₁ pair.hp₂)
    {Y : CommRingCat.{u}ᵒᵖ} (q : Y ⟶ Opposite.op R)
    (u₁ u₂ u₃ : Y ⟶ Opposite.op A)
    (h₁ : u₁ ≫ f.op = q) (h₂ : u₂ ≫ f.op = q)
    (h₃ : u₃ ≫ f.op = q) :
    rawT f.hom u₂.unop.hom u₃.unop.hom
        (compatibleComp f q u₂ u₃ h₂ h₃)
        (D.obj PUnit.unit) a =
      rawT f.hom u₂.unop.hom u₁.unop.hom
          (compatibleComp f q u₂ u₁ h₂ h₁)
          (D.obj PUnit.unit) a ≫
        rawT f.hom u₁.unop.hom u₃.unop.hom
          (compatibleComp f q u₁ u₃ h₁ h₃)
          (D.obj PUnit.unit) a := by
  rw [rawT_eq_descentHom f D a hcanonical q u₂ u₃ h₂ h₃]
  rw [rawT_eq_descentHom f D a hcanonical q u₂ u₁ h₂ h₁]
  rw [rawT_eq_descentHom f D a hcanonical q u₁ u₃ h₁ h₃]
  exact (D.hom_comp q u₂ u₁ u₃ h₂ h₁ h₃).symm

set_option linter.style.haveILetI false in
private theorem coassoc_of_transposed_eq
    {R A : CommRingCat.{u}} (f : R ⟶ A) (M : ModuleCat A)
    (a : M ⟶ (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad.obj M)
    (h :
      letI : Algebra R A := f.hom.toAlgebra
      let gR : A →+* TensorProduct R A A :=
        Algebra.TensorProduct.includeRight.toRingHom
      let gL : A →+* TensorProduct R A A :=
        Algebra.TensorProduct.includeLeftRingHom
      let adj := ModuleCat.extendRestrictScalarsAdj gR
      let G := (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad
      let e := affineTensorCechBaseChangeIso f
      (adj.homEquiv M ((ModuleCat.extendScalars gL).obj (G.obj M))).symm
          ((a ≫ G.δ.app M) ≫ e.inv.app (G.obj M)) =
        (adj.homEquiv M ((ModuleCat.extendScalars gL).obj (G.obj M))).symm
          ((a ≫ G.map a) ≫ e.inv.app (G.obj M))) :
    a ≫ (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad.δ.app M =
      a ≫ (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad.map a := by
  letI : Algebra R A := f.hom.toAlgebra
  let gR : A →+* TensorProduct R A A :=
    Algebra.TensorProduct.includeRight.toRingHom
  let gL : A →+* TensorProduct R A A :=
    Algebra.TensorProduct.includeLeftRingHom
  let adj := ModuleCat.extendRestrictScalarsAdj gR
  let G := (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad
  let e := affineTensorCechBaseChangeIso f
  change a ≫ G.δ.app M = a ≫ G.map a
  apply (cancel_mono (e.inv.app (G.obj M))).mp
  exact (adj.homEquiv M
    ((ModuleCat.extendScalars gL).obj (G.obj M))).symm.injective h

set_option maxRecDepth 10000 in
set_option linter.style.haveILetI false in
/-- The coaction reconstructed from choice-free affine descent data is
coassociative. -/
theorem affineModuleDescentCoaction_coassoc
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (D : AffineModuleDescentData f) :
    let M := D.obj PUnit.unit
    let G := (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad
    affineModuleDescentCoaction f D ≫ G.δ.app M =
      affineModuleDescentCoaction f D ≫ G.map
        (affineModuleDescentCoaction f D) := by
  letI algRA : Algebra R A := f.hom.toAlgebra
  let M : ModuleCat A := D.obj PUnit.unit
  let G := (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad
  let a := affineModuleDescentCoaction f D
  let B := TensorProduct R A A
  let iL : A →+* B := Algebra.TensorProduct.includeLeftRingHom
  let iR : A →+* B := Algebra.TensorProduct.includeRight.toRingHom
  letI algRB : Algebra R B := (iL.comp f.hom).toAlgebra
  let C := @TensorProduct R _ B A _ _ algRB.toModule algRA.toModule
  let oL : B →+* C :=
    @Algebra.TensorProduct.includeLeftRingHom R B A _ _ algRB _ algRA
  let oR : A →+* C :=
    (@Algebra.TensorProduct.includeRight R B A _ _ algRB _ algRA).toRingHom
  let j₁ := oL.comp iL
  let j₂ := oL.comp iR
  let h₁₃ : j₁.comp f.hom = oR.comp f.hom := by
    change (oL.comp iL).comp f.hom = oR.comp f.hom
    rw [RingHom.comp_assoc]
    change oL.comp (algebraMap R B) = oR.comp f.hom
    exact @Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      R B A _ _ algRB _ algRA
  let h₂₃ : j₂.comp f.hom = oR.comp f.hom := by
    change (oL.comp iR).comp f.hom = oR.comp f.hom
    rw [RingHom.comp_assoc, affineTensorPair_comp_eq f]
    exact @Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      R B A _ _ algRB _ algRA
  let β := higherBaseChangeApp f M
  let adjR := ModuleCat.extendRestrictScalarsAdj iR
  let adjO := ModuleCat.extendRestrictScalarsAdj oL
  let e := affineTensorCechBaseChangeIso f
  let Lδ := (adjR.homEquiv M
    ((ModuleCat.extendScalars iL).obj (G.obj M))).symm
      ((a ≫ G.δ.app M) ≫ e.inv.app (G.obj M))
  let LR := (adjR.homEquiv M
    ((ModuleCat.extendScalars iL).obj (G.obj M))).symm
      ((a ≫ G.map a) ≫ e.inv.app (G.obj M))
  let Y := Opposite.op (CommRingCat.of C)
  let q : Y ⟶ Opposite.op R :=
    (CommRingCat.ofHom (oR.comp f.hom)).op
  let u₁ : Y ⟶ Opposite.op A := (CommRingCat.ofHom j₁).op
  let u₂ : Y ⟶ Opposite.op A := (CommRingCat.ofHom j₂).op
  let u₃ : Y ⟶ Opposite.op A := (CommRingCat.ofHom oR).op
  have h₁ : u₁ ≫ f.op = q := by
    change (CommRingCat.ofHom (j₁.comp f.hom)).op =
      (CommRingCat.ofHom (oR.comp f.hom)).op
    exact congrArg (fun z : R →+* C => (CommRingCat.ofHom z).op) h₁₃
  have h₂ : u₂ ≫ f.op = q := by
    change (CommRingCat.ofHom (j₂.comp f.hom)).op =
      (CommRingCat.ofHom (oR.comp f.hom)).op
    exact congrArg (fun z : R →+* C => (CommRingCat.ofHom z).op) h₂₃
  have h₃ : u₃ ≫ f.op = q := by rfl
  have hcanonical := rawT_eq_descentHom_canonical f D
  have hc := rawT_cocycle_of_canonical f D a hcanonical
    q u₁ u₂ u₃ h₁ h₂ h₃
  have hc' :
      rawT f.hom j₂ oR h₂₃ M a =
        rawT f.hom j₂ j₁
            (rawCompat f.hom iR iL oL
              (affineTensorPair_comp_eq f)) M a ≫
          rawT f.hom j₁ oR h₁₃ M a := by
    change rawT f.hom j₂ oR _ M a =
      rawT f.hom j₂ j₁ _ M a ≫ rawT f.hom j₁ oR _ M a at hc
    exact hc
  apply coassoc_of_transposed_eq f M a
  change Lδ = LR
  apply (cancel_mono β.hom).mp
  apply (adjO.homEquiv ((ModuleCat.extendScalars iR).obj M)
    ((ModuleCat.extendScalars oR).obj M)).symm.injective
  apply (cancel_epi ((ModuleCat.extendScalarsComp iR oL).hom.app M)).mp
  calc
    _ = rawT f.hom j₂ oR h₂₃ M a := qL_direct_eq_rawT23 f M a
    _ = rawT f.hom j₂ j₁
          (rawCompat f.hom iR iL oL
            (affineTensorPair_comp_eq f)) M a ≫
        rawT f.hom j₁ oR h₁₃ M a := hc'
    _ = _ := (qR_direct_eq_rawTcomp f M a).symm

/-- Coalgebra transport commutes with choice-free descent reindexing. -/
theorem comonadicModuleDescentTransportMap_pullHom
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (Q : ComonadicModuleDescentData f.hom)
    {Y' Y : CommRingCat.{u}ᵒᵖ} (g : Y' ⟶ Y)
    (f₁ f₂ : Y ⟶ Opposite.op A)
    (gf₁ gf₂ : Y' ⟶ Opposite.op A)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    (h : f₁.unop.hom.comp f.hom = f₂.unop.hom.comp f.hom)
    (h' : gf₁.unop.hom.comp f.hom = gf₂.unop.hom.comp f.hom) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (F := affineModulePseudofunctor)
      (comonadicModuleDescentTransportMap f.hom
        f₁.unop.hom f₂.unop.hom h Q)
      g gf₁ gf₂ hgf₁ hgf₂ =
    comonadicModuleDescentTransportMap f.hom
      gf₁.unop.hom gf₂.unop.hom h' Q := by
  change
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (F := affineModulePseudofunctor)
      (rawT f.hom f₁.unop.hom f₂.unop.hom h Q.A Q.a)
      g gf₁ gf₂ hgf₁ hgf₂ =
    rawT f.hom gf₁.unop.hom gf₂.unop.hom h' Q.A Q.a
  exact rawT_pullHom f Q.A Q.a g f₁ f₂ gf₁ gf₂ hgf₁ hgf₂ h h'

/-- An extension--restriction coalgebra determines choice-free affine
descent data. -/
noncomputable def comonadicModuleDescentToAffineObj
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (Q : ComonadicModuleDescentData f.hom) :
    AffineModuleDescentData f where
  obj := fun _ => Q.A
  hom := fun {Y} q {i₁ i₂} f₁ f₂ hf₁ hf₂ =>
    comonadicModuleDescentTransportMap f.hom
      f₁.unop.hom f₂.unop.hom
      (compatibleComp f q f₁ f₂ hf₁ hf₂) Q
  pullHom_hom := by
    intro Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
    have hgf₁' : gf₁ ≫ f.op = q' := by
      calc
        gf₁ ≫ f.op = (g ≫ f₁) ≫ f.op := by rw [hgf₁]
        _ = g ≫ (f₁ ≫ f.op) := Category.assoc _ _ _
        _ = g ≫ q := by rw [hf₁]
        _ = q' := hq
    have hgf₂' : gf₂ ≫ f.op = q' := by
      calc
        gf₂ ≫ f.op = (g ≫ f₂) ≫ f.op := by rw [hgf₂]
        _ = g ≫ (f₂ ≫ f.op) := Category.assoc _ _ _
        _ = g ≫ q := by rw [hf₂]
        _ = q' := hq
    exact comonadicModuleDescentTransportMap_pullHom
      f Q g f₁ f₂ gf₁ gf₂ hgf₁ hgf₂
      (compatibleComp f q f₁ f₂ hf₁ hf₂)
      (compatibleComp f q' gf₁ gf₂ hgf₁' hgf₂')
  hom_self := by
    intro Y q i g x
    change comonadicModuleDescentTransportMap f.hom
      g.unop.hom g.unop.hom rfl Q =
        𝟙 ((ModuleCat.extendScalars g.unop.hom).obj Q.A)
    exact comonadicModuleDescentTransportMap_self f.hom g.unop.hom Q
  hom_comp := by
    intro Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃
    change
      comonadicModuleDescentTransportMap f.hom
          f₁.unop.hom f₂.unop.hom _ Q ≫
        comonadicModuleDescentTransportMap f.hom
          f₂.unop.hom f₃.unop.hom _ Q =
      comonadicModuleDescentTransportMap f.hom
        f₁.unop.hom f₃.unop.hom _ Q
    exact comonadicModuleDescentTransportMap_comp
      f.hom f₁.unop.hom f₂.unop.hom f₃.unop.hom
      (compatibleComp f q f₁ f₂ hf₁ hf₂)
      (compatibleComp f q f₂ f₃ hf₂ hf₃)
      (compatibleComp f q f₁ f₃ hf₁ hf₃) Q

noncomputable def comonadicModuleDescentToAffineMap
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    {Q Q' : ComonadicModuleDescentData f.hom} (q : Q ⟶ Q') :
    comonadicModuleDescentToAffineObj f Q ⟶
      comonadicModuleDescentToAffineObj f Q' where
  hom := fun _ => q.f
  comm := by
    intro Y r i₁ i₂ f₁ f₂ hf₁ hf₂
    exact (comonadicModuleDescentTransportMap_natural f.hom
      f₁.unop.hom f₂.unop.hom
      (compatibleComp f r f₁ f₂ hf₁ hf₂) q).symm

/-- The functor from extension--restriction coalgebras to choice-free affine
descent data. -/
noncomputable def comonadicModuleDescentToAffine
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    ComonadicModuleDescentData f.hom ⥤ AffineModuleDescentData f where
  obj Q := comonadicModuleDescentToAffineObj f Q
  map q := comonadicModuleDescentToAffineMap f q
  map_id Q := by
    apply Pseudofunctor.DescentData.Hom.ext
    rfl
  map_comp q r := by
    apply Pseudofunctor.DescentData.Hom.ext
    rfl
/-- A choice-free affine descent datum determines a coalgebra. -/
noncomputable def affineModuleDescentToComonadicObj
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (D : AffineModuleDescentData f) :
    ComonadicModuleDescentData f.hom :=
  Comonad.Coalgebra.mk (D.obj PUnit.unit)
    (affineModuleDescentCoaction f D)
    (affineModuleDescentCoaction_counit f D)
    (affineModuleDescentCoaction_coassoc f D)

/-- A morphism of affine descent data induces a coalgebra morphism. -/
noncomputable def affineModuleDescentToComonadicMap
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    {D₁ D₂ : AffineModuleDescentData f} (φ : D₁ ⟶ D₂) :
    affineModuleDescentToComonadicObj f D₁ ⟶
      affineModuleDescentToComonadicObj f D₂ :=
  Comonad.Coalgebra.Hom.mk (φ.hom PUnit.unit)
    (affineModuleDescentCoaction_natural f φ)

/-- The functor from choice-free affine descent data to coalgebras. -/
noncomputable def affineModuleDescentToComonadic
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    AffineModuleDescentData f ⥤ ComonadicModuleDescentData f.hom where
  obj D := affineModuleDescentToComonadicObj f D
  map φ := affineModuleDescentToComonadicMap f φ
  map_id D := by
    apply Comonad.Coalgebra.Hom.ext
    rfl
  map_comp φ ψ := by
    apply Comonad.Coalgebra.Hom.ext
    rfl

set_option linter.style.haveILetI false in
theorem affineModuleDescentCoaction_toAffine
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (Q : ComonadicModuleDescentData f.hom) :
    affineModuleDescentCoaction f
        (comonadicModuleDescentToAffineObj f Q) = Q.a := by
  letI : Algebra R A := f.hom.toAlgebra
  let M : ModuleCat A := Q.A
  let H := ModuleCat.restrictScalars f.hom ⋙ ModuleCat.extendScalars f.hom
  let a : M ⟶ H.obj M := Q.a
  let gR : A →+* TensorProduct R A A :=
    Algebra.TensorProduct.includeRight.toRingHom
  let gL : A →+* TensorProduct R A A :=
    Algebra.TensorProduct.includeLeftRingHom
  let adj := ModuleCat.extendRestrictScalarsAdj gR
  let e := affineTensorCechBaseChangeIso f
  let κ : (ModuleCat.extendScalars gR).obj (H.obj M) ⟶
      (ModuleCat.extendScalars gL).obj M :=
    (affineModuleComonadicTransport f.hom gR gL
      (affineTensorPair_comp_eq f)).app M
  have hκ :
      adj.homEquiv (H.obj M) ((ModuleCat.extendScalars gL).obj M) κ =
        e.inv.app M :=
    affineModuleComonadicTransport_canonicalPair f M
  change adj.homEquiv M ((ModuleCat.extendScalars gL).obj M)
      ((ModuleCat.extendScalars gR).map a ≫ κ) ≫ e.hom.app M = a
  rw [adj.homEquiv_naturality_left, hκ]
  calc
    (a ≫ e.inv.app M) ≫ e.hom.app M =
        a ≫ (e.inv.app M ≫ e.hom.app M) := Category.assoc _ _ _
    _ = a := by rw [Iso.inv_hom_id_app]; exact Category.comp_id _

private theorem affineModuleDescentRoundtrip_hom
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (D : AffineModuleDescentData f)
    {Y : CommRingCat.{u}ᵒᵖ} (q : Y ⟶ Opposite.op R)
    (f₁ f₂ : Y ⟶ Opposite.op A)
    (hf₁ : f₁ ≫ f.op = q) (hf₂ : f₂ ≫ f.op = q) :
    (comonadicModuleDescentToAffineObj f
      (affineModuleDescentToComonadicObj f D)).hom q
        (i₁ := PUnit.unit) (i₂ := PUnit.unit)
        f₁ f₂ hf₁ hf₂ =
      D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit)
        f₁ f₂ hf₁ hf₂ := by
  change rawT f.hom f₁.unop.hom f₂.unop.hom
      (compatibleComp f q f₁ f₂ hf₁ hf₂)
      (D.obj PUnit.unit) (affineModuleDescentCoaction f D) =
    D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit)
      f₁ f₂ hf₁ hf₂
  exact rawT_eq_descentHom f D
    (affineModuleDescentCoaction f D)
    (rawT_eq_descentHom_canonical f D)
    q f₁ f₂ hf₁ hf₂

/-- The affine-descent roundtrip is canonically isomorphic to the identity. -/
noncomputable def affineModuleDescentRoundtripIso
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (D : AffineModuleDescentData f) :
    D ≅ comonadicModuleDescentToAffineObj f
      (affineModuleDescentToComonadicObj f D) := by
  let M : ModuleCat A := D.obj PUnit.unit
  let D' := comonadicModuleDescentToAffineObj f
    (affineModuleDescentToComonadicObj f D)
  let toComp : (i : PUnit) → D.obj i ⟶ D'.obj i :=
    PUnit.rec (𝟙 M)
  let fromComp : (i : PUnit) → D'.obj i ⟶ D.obj i :=
    PUnit.rec (𝟙 M)
  let hom : D ⟶ D' :=
    { hom := toComp
      comm := by
        intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
        cases i₁
        cases i₂
        let t :
            (affineModulePseudofunctor.map f₁.op.toLoc).toFunctor.obj
                (D.obj PUnit.unit) ⟶
              (affineModulePseudofunctor.map f₂.op.toLoc).toFunctor.obj
                (D.obj PUnit.unit) :=
          rawT f.hom f₁.unop.hom f₂.unop.hom
            (compatibleComp f q f₁ f₂ hf₁ hf₂) M
            (affineModuleDescentCoaction f D)
        let d :
            (affineModulePseudofunctor.map f₁.op.toLoc).toFunctor.obj
                (D.obj PUnit.unit) ⟶
              (affineModulePseudofunctor.map f₂.op.toLoc).toFunctor.obj
                (D.obj PUnit.unit) :=
          D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit)
            f₁ f₂ hf₁ hf₂
        have htd : t = d := by
          exact affineModuleDescentRoundtrip_hom f D
            q f₁ f₂ hf₁ hf₂
        dsimp only [toComp]
        change
          (affineModulePseudofunctor.map f₁.op.toLoc).toFunctor.map
                (𝟙 (D.obj PUnit.unit)) ≫ t =
            d ≫ (affineModulePseudofunctor.map f₂.op.toLoc).toFunctor.map
                (𝟙 (D.obj PUnit.unit))
        rw [(affineModulePseudofunctor.map f₁.op.toLoc).toFunctor.map_id,
          (affineModulePseudofunctor.map f₂.op.toLoc).toFunctor.map_id]
        exact (Category.id_comp t).trans
          (htd.trans (Category.comp_id d).symm) }
  let inv : D' ⟶ D :=
    { hom := fromComp
      comm := by
        intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
        cases i₁
        cases i₂
        let t :
            (affineModulePseudofunctor.map f₁.op.toLoc).toFunctor.obj
                (D.obj PUnit.unit) ⟶
              (affineModulePseudofunctor.map f₂.op.toLoc).toFunctor.obj
                (D.obj PUnit.unit) :=
          rawT f.hom f₁.unop.hom f₂.unop.hom
            (compatibleComp f q f₁ f₂ hf₁ hf₂) M
            (affineModuleDescentCoaction f D)
        let d :
            (affineModulePseudofunctor.map f₁.op.toLoc).toFunctor.obj
                (D.obj PUnit.unit) ⟶
              (affineModulePseudofunctor.map f₂.op.toLoc).toFunctor.obj
                (D.obj PUnit.unit) :=
          D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit)
            f₁ f₂ hf₁ hf₂
        have htd : t = d := by
          exact affineModuleDescentRoundtrip_hom f D
            q f₁ f₂ hf₁ hf₂
        dsimp only [fromComp]
        change
          (affineModulePseudofunctor.map f₁.op.toLoc).toFunctor.map
                (𝟙 (D.obj PUnit.unit)) ≫ d =
            t ≫ (affineModulePseudofunctor.map f₂.op.toLoc).toFunctor.map
                (𝟙 (D.obj PUnit.unit))
        rw [(affineModulePseudofunctor.map f₁.op.toLoc).toFunctor.map_id,
          (affineModulePseudofunctor.map f₂.op.toLoc).toFunctor.map_id]
        exact (Category.id_comp d).trans
          (htd.symm.trans (Category.comp_id t).symm) }
  exact Iso.mk hom inv
    (by
      apply Pseudofunctor.DescentData.Hom.ext
      funext i
      cases i
      change (𝟙 M) ≫ 𝟙 M = 𝟙 M
      exact Category.id_comp _)
    (by
      apply Pseudofunctor.DescentData.Hom.ext
      funext i
      cases i
      change (𝟙 M) ≫ 𝟙 M = 𝟙 M
      exact Category.id_comp _)

/-- The unit natural isomorphism for the affine/comonadic roundtrip. -/
noncomputable def affineModuleDescentRoundtripNatIso
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    𝟭 (AffineModuleDescentData f) ≅
      affineModuleDescentToComonadic f ⋙
        comonadicModuleDescentToAffine f :=
  NatIso.ofComponents (fun D => affineModuleDescentRoundtripIso f D) <| by
    intro D₁ D₂ φ
    apply Pseudofunctor.DescentData.Hom.ext
    funext i
    cases i
    change
      φ.hom PUnit.unit ≫ 𝟙 (D₂.obj PUnit.unit) =
        𝟙 (D₁.obj PUnit.unit) ≫ φ.hom PUnit.unit
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- The coalgebra roundtrip is canonically isomorphic to the original coalgebra. -/
noncomputable def comonadicModuleDescentRoundtripIso
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (Q : ComonadicModuleDescentData f.hom) :
    affineModuleDescentToComonadicObj f
        (comonadicModuleDescentToAffineObj f Q) ≅ Q := by
  refine Comonad.Coalgebra.isoMk
    (A := affineModuleDescentToComonadicObj f
      (comonadicModuleDescentToAffineObj f Q)) (B := Q)
    (Iso.refl Q.A) ?_
  let G := (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad
  let a' : Q.A ⟶ G.obj Q.A :=
    affineModuleDescentCoaction f
      (comonadicModuleDescentToAffineObj f Q)
  have ha : a' = Q.a := by
    exact affineModuleDescentCoaction_toAffine f Q
  have hm : G.map (𝟙 Q.A) = 𝟙 (G.obj Q.A) := G.map_id Q.A
  change a' ≫ G.map (𝟙 Q.A) = 𝟙 Q.A ≫ Q.a
  calc
    a' ≫ G.map (𝟙 Q.A) = a' ≫ 𝟙 (G.obj Q.A) := by rw [hm]
    _ = a' := Category.comp_id _
    _ = Q.a := ha
    _ = 𝟙 Q.A ≫ Q.a := (Category.id_comp _).symm

/-- The counit natural isomorphism for the affine/comonadic roundtrip. -/
noncomputable def comonadicModuleDescentRoundtripNatIso
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    comonadicModuleDescentToAffine f ⋙
        affineModuleDescentToComonadic f ≅
      𝟭 (ComonadicModuleDescentData f.hom) :=
  NatIso.ofComponents (fun Q => comonadicModuleDescentRoundtripIso f Q) <| by
    intro Q₁ Q₂ q
    apply Comonad.Coalgebra.Hom.ext
    dsimp only [Functor.comp_map, Functor.id_map,
      comonadicModuleDescentToAffine, comonadicModuleDescentToAffineMap,
      affineModuleDescentToComonadic, affineModuleDescentToComonadicMap,
      comonadicModuleDescentRoundtripIso]
    change q.f ≫ 𝟙 Q₂.A = 𝟙 Q₁.A ≫ q.f
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- Choice-free affine module descent data are equivalent to
extension--restriction coalgebras. -/
noncomputable def affineModuleComonadicEquivalence
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    AffineModuleDescentData f ≌ ComonadicModuleDescentData f.hom :=
  CategoryTheory.Equivalence.mk
    (affineModuleDescentToComonadic f)
    (comonadicModuleDescentToAffine f)
    (affineModuleDescentRoundtripNatIso f)
    (comonadicModuleDescentRoundtripNatIso f)

private noncomputable def affineMapComp'App
    {R A B : CommRingCat.{u}} (f : R ⟶ A) (g : A ⟶ B) (q : R ⟶ B)
    (h : f ≫ g = q) (N : ModuleCat.{u} R) :
    (ModuleCat.extendScalars q.hom).obj N ⟶
      (ModuleCat.extendScalars g.hom).obj
        ((ModuleCat.extendScalars f.hom).obj N) :=
  (affineModulePseudofunctor.mapComp' f.op.op.toLoc g.op.op.toLoc
    q.op.op.toLoc
    (by simpa using congrArg (fun z => z.op.op.toLoc) h)).hom.toNatTrans.app N

private theorem affineMapComp'App_one_tmul
    {R A B : CommRingCat.{u}} (f : R ⟶ A) (g : A ⟶ B) (q : R ⟶ B)
    (h : f ≫ g = q) (N : ModuleCat.{u} R) (n : N) :
    affineMapComp'App f g q h N
        (show ↑((ModuleCat.extendScalars q.hom).obj N) from
          (1 : B) ⊗ₜ[R, q.hom] n) =
      (show ↑((ModuleCat.extendScalars g.hom).obj
          ((ModuleCat.extendScalars f.hom).obj N)) from
        (1 : B) ⊗ₜ[A, g.hom]
          (show ↑((ModuleCat.extendScalars f.hom).obj N) from
            (1 : A) ⊗ₜ[R, f.hom] n)) := by
  subst q
  have hmc : affineModulePseudofunctor.mapComp'
      f.op.op.toLoc g.op.op.toLoc (f ≫ g).op.op.toLoc =
    affineModulePseudofunctor.mapComp
      f.op.op.toLoc g.op.op.toLoc := by
    apply Pseudofunctor.mapComp'_eq_mapComp
  unfold affineMapComp'App
  rw [hmc]
  change (ModuleCat.extendScalarsComp f.hom g.hom).hom.app N
      ((1 : B) ⊗ₜ[R, g.hom.comp f.hom] n) =
    (1 : B) ⊗ₜ[A, g.hom]
      (show ↑((ModuleCat.extendScalars f.hom).obj N) from
        (1 : A) ⊗ₜ[R, f.hom] n)
  exact ModuleCat.extendScalarsComp_hom_app_one_tmul f.hom g.hom N n

private theorem extendScalars_map_one_tmul'
    {A B : Type u} [CommRing A] [CommRing B] (g : A →+* B)
    {M N : ModuleCat.{u} A} (p : M ⟶ N) (m : M) :
    (ModuleCat.extendScalars g).map p
        (show ↑((ModuleCat.extendScalars g).obj M) from
          (1 : B) ⊗ₜ[A, g] m) =
      (show ↑((ModuleCat.extendScalars g).obj N) from
        (1 : B) ⊗ₜ[A, g] p m) := by
  let _ : Algebra A B := g.toAlgebra
  change (LinearMap.baseChange B (ModuleCat.Hom.hom p))
    ((1 : B) ⊗ₜ[A] m) = _
  exact LinearMap.baseChange_tmul _ _ _

private theorem affineModuleComonadicTransport_nested_one_tmul
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g₁ g₂ : A →+* B)
    (h : g₁.comp f = g₂.comp f) (M : ModuleCat.{u} A) (x : M) :
    (affineModuleComonadicTransport f g₁ g₂ h).app M
        ((1 : B) ⊗ₜ[A, g₁] ((1 : A) ⊗ₜ[R, f] x)) =
      (1 : B) ⊗ₜ[A, g₂] x := by
  exact affineModuleComonadicTransport_app_one_tmul f g₁ g₂ h M x

set_option maxHeartbeats 800000 in
-- The comparison calculation normalizes two nested adjunction transposes.
private theorem affineModuleComparison_hom_eq_transport
    {R A : CommRingCat.{u}} (f : R ⟶ A) (N : ModuleCat.{u} R)
    {Y : CommRingCat.{u}ᵒᵖ} (q : Y ⟶ Opposite.op R)
    (f₁ f₂ : Y ⟶ Opposite.op A)
    (hf₁ : f₁ ≫ f.op = q) (hf₂ : f₂ ≫ f.op = q) :
    let h : f₁.unop.hom.comp f.hom = f₂.unop.hom.comp f.hom := by
      ext r
      have h₁ := congrArg
        (fun k : Y ⟶ Opposite.op R => k.unop.hom r) hf₁
      have h₂ := congrArg
        (fun k : Y ⟶ Opposite.op R => k.unop.hom r) hf₂
      exact h₁.trans h₂.symm
    ((affineModuleDescentComparison f).obj N).hom q
        (i₁ := PUnit.unit) (i₂ := PUnit.unit) f₁ f₂ hf₁ hf₂ =
      (ModuleCat.extendScalars f₁.unop.hom).map
          ((ModuleCat.extendScalars f.hom).map
            ((ModuleCat.extendRestrictScalarsAdj f.hom).unit.app N)) ≫
        (affineModuleComonadicTransport f.hom
          f₁.unop.hom f₂.unop.hom h).app
            ((ModuleCat.extendScalars f.hom).obj N) := by
  dsimp only
  subst q
  let h : f₁.unop.hom.comp f.hom = f₂.unop.hom.comp f.hom := by
    ext r
    have hh := congrArg
      (fun k : Y ⟶ Opposite.op R => k.unop.hom r) hf₂
    exact hh.symm
  let g₁ := f₁.unop.hom
  let g₂ := f₂.unop.hom
  let LN := (ModuleCat.extendScalars f.hom).obj N
  let T := (ModuleCat.extendScalars g₂).obj LN
  let q₂ : R ⟶ Y.unop := (f₁ ≫ f.op).unop
  let h₂ : f ≫ f₂.unop = q₂ := by
    simpa [q₂] using congrArg Quiver.Hom.unop hf₂
  let mc₂ : (ModuleCat.extendScalars (g₁.comp f.hom)).obj N ⟶ T :=
    affineMapComp'App f f₂.unop q₂ h₂ N
  let L : (ModuleCat.extendScalars g₁).obj LN ⟶ T :=
    ((affineModuleDescentComparison f).obj N).hom (f₁ ≫ f.op)
      (i₁ := PUnit.unit) (i₂ := PUnit.unit) f₁ f₂ rfl hf₂
  let K : (ModuleCat.extendScalars g₁).obj LN ⟶ T :=
    (ModuleCat.extendScalars g₁).map
        ((ModuleCat.extendScalars f.hom).map
          ((ModuleCat.extendRestrictScalarsAdj f.hom).unit.app N)) ≫
      (affineModuleComonadicTransport f.hom g₁ g₂ h).app LN
  have hmc₁ : affineModulePseudofunctor.mapComp'
      f.op.op.toLoc f₁.op.toLoc (f₁ ≫ f.op).op.toLoc =
      affineModulePseudofunctor.mapComp
        f.op.op.toLoc f₁.op.toLoc := by
    apply Pseudofunctor.mapComp'_eq_mapComp
  have hL :
      L = (ModuleCat.extendScalarsComp f.hom g₁).inv.app N ≫ mc₂ := by
    dsimp only [L, affineModuleDescentComparison,
      Pseudofunctor.toDescentData, Pseudofunctor.DescentData.ofObj]
    rw [hmc₁]
    rfl
  change L = K
  rw [hL]
  let adj₁ := ModuleCat.extendRestrictScalarsAdj g₁
  apply (adj₁.homEquiv LN T).injective
  let Z := (ModuleCat.restrictScalars g₁).obj T
  let adjf := ModuleCat.extendRestrictScalarsAdj f.hom
  apply (adjf.homEquiv N Z).injective
  rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply]
  rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply]
  apply ModuleCat.hom_ext
  ext n
  let nN : N := n
  let x : LN := (1 : A) ⊗ₜ[R, f.hom] nN
  let y : (ModuleCat.extendScalars g₁).obj LN :=
    (1 : Y.unop) ⊗ₜ[A, g₁] x
  let z : (ModuleCat.extendScalars (g₁.comp f.hom)).obj N :=
    (1 : Y.unop) ⊗ₜ[R, g₁.comp f.hom] nN
  let w : T := (1 : Y.unop) ⊗ₜ[A, g₂] x
  change
    ((ModuleCat.extendScalarsComp f.hom g₁).inv.app N ≫ mc₂) y = K y
  have hc :
      (ModuleCat.extendScalarsComp f.hom g₁).inv.app N y = z := by
    exact extendScalarsComp_inv_app_one_tmul f.hom g₁ N nN
  have hm : mc₂ z = w := by
    exact affineMapComp'App_one_tmul f f₂.unop q₂ h₂ N nN
  have hk : K y = w := by
    let a : LN ⟶
        (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad.obj LN :=
      (ModuleCat.extendScalars f.hom).map
        ((ModuleCat.extendRestrictScalarsAdj f.hom).unit.app N)
    let xx : (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad.obj LN :=
      (1 : A) ⊗ₜ[R, f.hom] x
    let yy : (ModuleCat.extendScalars g₁).obj
        ((ModuleCat.extendRestrictScalarsAdj f.hom).toComonad.obj LN) :=
      (1 : Y.unop) ⊗ₜ[A, g₁] xx
    have hgen :
        (affineModuleComonadicTransport f.hom g₁ g₂ h).app LN yy = w := by
      change
        (affineModuleComonadicTransport f.hom g₁ g₂ h).app LN
            ((1 : Y.unop) ⊗ₜ[A, g₁]
              ((1 : A) ⊗ₜ[R, f.hom] x)) =
          (1 : Y.unop) ⊗ₜ[A, g₂] x
      exact affineModuleComonadicTransport_nested_one_tmul
        f.hom g₁ g₂ h LN x
    have hinner : a x = xx := by
      change (ModuleCat.extendScalars f.hom).map
          ((ModuleCat.extendRestrictScalarsAdj f.hom).unit.app N) x = xx
      rw [extendScalars_map_one_tmul']
      rfl
    have houter : (ModuleCat.extendScalars g₁).map a y = yy := by
      rw [extendScalars_map_one_tmul', hinner]
    change (affineModuleComonadicTransport f.hom g₁ g₂ h).app LN
      ((ModuleCat.extendScalars g₁).map a y) = w
    rw [houter]
    exact hgen
  calc
    ((ModuleCat.extendScalarsComp f.hom g₁).inv.app N ≫ mc₂) y =
        mc₂ z := by
      change mc₂ ((ModuleCat.extendScalarsComp f.hom g₁).inv.app N y) =
        mc₂ z
      rw [hc]
    _ = w := hm
    _ = K y := hk.symm

set_option linter.style.haveILetI false in
private theorem affineModuleDescentCoaction_eq_of_canonical_rawT
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (D : AffineModuleDescentData f)
    (a : D.obj PUnit.unit ⟶
      (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad.obj
        (D.obj PUnit.unit))
    (hθ :
      letI : Algebra R A := f.hom.toAlgebra
      let pair := affineCechPair f
      let h : pair.p₁.unop.hom.comp f.hom =
          pair.p₂.unop.hom.comp f.hom := by
        ext r
        have h₁ := congrArg
          (fun k : pair.pullback ⟶ Opposite.op R => k.unop.hom r) pair.hp₁
        have h₂ := congrArg
          (fun k : pair.pullback ⟶ Opposite.op R => k.unop.hom r) pair.hp₂
        exact h₁.trans h₂.symm
      D.hom pair.p (i₁ := PUnit.unit) (i₂ := PUnit.unit)
          pair.p₁ pair.p₂ pair.hp₁ pair.hp₂ =
        (ModuleCat.extendScalars pair.p₁.unop.hom).map a ≫
          (affineModuleComonadicTransport f.hom
            pair.p₁.unop.hom pair.p₂.unop.hom h).app
              (D.obj PUnit.unit)) :
    affineModuleDescentCoaction f D = a := by
  letI : Algebra R A := f.hom.toAlgebra
  let M : ModuleCat A := D.obj PUnit.unit
  let G := (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad
  let aM : M ⟶ G.obj M := a
  let pair := affineCechPair f
  let gR : A →+* TensorProduct R A A :=
    Algebra.TensorProduct.includeRight.toRingHom
  let gL : A →+* TensorProduct R A A :=
    Algebra.TensorProduct.includeLeftRingHom
  let hpair : gR.comp f.hom = gL.comp f.hom :=
    compatibleComp f pair.p pair.p₁ pair.p₂
      pair.hp₁ pair.hp₂
  let θ : (ModuleCat.extendScalars gR).obj M ⟶
      (ModuleCat.extendScalars gL).obj M :=
    D.hom pair.p (i₁ := PUnit.unit) (i₂ := PUnit.unit)
      pair.p₁ pair.p₂ pair.hp₁ pair.hp₂
  let κ : (ModuleCat.extendScalars gR).obj (G.obj M) ⟶
      (ModuleCat.extendScalars gL).obj M :=
    (affineModuleComonadicTransport f.hom gR gL
      hpair).app M
  let adj := ModuleCat.extendRestrictScalarsAdj gR
  let eG :
      (ModuleCat.extendScalars gL ⋙ ModuleCat.restrictScalars gR) ≅
        G.toFunctor :=
    affineTensorCechBaseChangeIso f
  have hθ' : θ = (ModuleCat.extendScalars gR).map aM ≫ κ := by
    exact hθ
  have hκ :
      adj.homEquiv (G.obj M) ((ModuleCat.extendScalars gL).obj M) κ =
        eG.inv.app M := by
    exact affineModuleComonadicTransport_canonicalPair f M
  change
    adj.homEquiv M ((ModuleCat.extendScalars gL).obj M) θ ≫
        eG.hom.app M =
      aM
  rw [hθ', adj.homEquiv_naturality_left]
  rw [hκ]
  have he : eG.inv.app M ≫ eG.hom.app M = 𝟙 (G.obj M) :=
    eG.inv_hom_id_app M
  calc
    (aM ≫ eG.inv.app M) ≫ eG.hom.app M =
        aM ≫ (eG.inv.app M ≫ eG.hom.app M) := Category.assoc _ _ _
    _ = aM ≫ 𝟙 (G.obj M) := congrArg (fun z => aM ≫ z) he
    _ = aM := Category.comp_id _

set_option maxHeartbeats 800000 in
-- Canonical specialization normalizes the comparison pseudofunctor coherence.
set_option linter.style.haveILetI false in
private theorem affineModuleComparison_canonical_rawT
    {R A : CommRingCat.{u}} (f : R ⟶ A) (N : ModuleCat.{u} R) :
    letI : Algebra R A := f.hom.toAlgebra
    let D := (affineModuleDescentComparison f).obj N
    let M : ModuleCat A := (ModuleCat.extendScalars f.hom).obj N
    let G := (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad
    let a : M ⟶ G.obj M := (ModuleCat.extendScalars f.hom).map
      ((ModuleCat.extendRestrictScalarsAdj f.hom).unit.app N)
    let pair := affineCechPair f
    let h : pair.p₁.unop.hom.comp f.hom =
        pair.p₂.unop.hom.comp f.hom := by
      ext r
      have h₁ := congrArg
        (fun k : pair.pullback ⟶ Opposite.op R => k.unop.hom r) pair.hp₁
      have h₂ := congrArg
        (fun k : pair.pullback ⟶ Opposite.op R => k.unop.hom r) pair.hp₂
      exact h₁.trans h₂.symm
    D.hom pair.p (i₁ := PUnit.unit) (i₂ := PUnit.unit)
        pair.p₁ pair.p₂ pair.hp₁ pair.hp₂ =
      (ModuleCat.extendScalars pair.p₁.unop.hom).map a ≫
        (affineModuleComonadicTransport f.hom
          pair.p₁.unop.hom pair.p₂.unop.hom h).app M := by
  letI : Algebra R A := f.hom.toAlgebra
  let D := (affineModuleDescentComparison f).obj N
  let M : ModuleCat A := (ModuleCat.extendScalars f.hom).obj N
  let G := (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad
  let a : M ⟶ G.obj M := (ModuleCat.extendScalars f.hom).map
    ((ModuleCat.extendRestrictScalarsAdj f.hom).unit.app N)
  let pair := affineCechPair f
  exact affineModuleComparison_hom_eq_transport
    f N pair.p pair.p₁ pair.p₂ pair.hp₁ pair.hp₂
set_option linter.style.haveILetI false in
/-- The coaction reconstructed from the canonical affine descent datum is the
canonical comparison-coalgebra coaction. -/
theorem affineModuleDescentCoaction_comparison
    {R A : CommRingCat.{u}} (f : R ⟶ A) (N : ModuleCat.{u} R) :
    affineModuleDescentCoaction f
        ((affineModuleDescentComparison f).obj N) =
      ((comonadicModuleDescentComparison f.hom).obj N).a := by
  let D := (affineModuleDescentComparison f).obj N
  let M : ModuleCat A := (ModuleCat.extendScalars f.hom).obj N
  let G := (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad
  let a : M ⟶ G.obj M := (ModuleCat.extendScalars f.hom).map
    ((ModuleCat.extendRestrictScalarsAdj f.hom).unit.app N)
  apply affineModuleDescentCoaction_eq_of_canonical_rawT f D a
  exact affineModuleComparison_canonical_rawT f N

/-- Component of the comparison-functor compatibility isomorphism. -/
noncomputable def affineModuleDescentComparisonIsoApp
    {R A : CommRingCat.{u}} (f : R ⟶ A) (N : ModuleCat.{u} R) :
    (affineModuleDescentToComonadic f).obj
        ((affineModuleDescentComparison f).obj N) ≅
      (comonadicModuleDescentComparison f.hom).obj N := by
  let L := ModuleCat.extendScalars f.hom
  let G := (ModuleCat.extendRestrictScalarsAdj f.hom).toComonad
  let X := (affineModuleDescentToComonadic f).obj
    ((affineModuleDescentComparison f).obj N)
  let Y := (comonadicModuleDescentComparison f.hom).obj N
  refine Comonad.Coalgebra.isoMk (A := X) (B := Y)
    (Iso.refl (L.obj N)) ?_
  let aX : L.obj N ⟶ G.obj (L.obj N) :=
    affineModuleDescentCoaction f
      ((affineModuleDescentComparison f).obj N)
  let aY : L.obj N ⟶ G.obj (L.obj N) := Y.a
  have ha : aX = aY := affineModuleDescentCoaction_comparison f N
  have hm : G.map (𝟙 (L.obj N)) = 𝟙 (G.obj (L.obj N)) :=
    G.map_id (L.obj N)
  change aX ≫ G.map (𝟙 (L.obj N)) = 𝟙 (L.obj N) ≫ aY
  calc
    aX ≫ G.map (𝟙 (L.obj N)) =
        aX ≫ 𝟙 (G.obj (L.obj N)) := by rw [hm]
    _ = aX := Category.comp_id _
    _ = aY := ha
    _ = 𝟙 (L.obj N) ≫ aY := (Category.id_comp _).symm

/-- The affine and comonadic comparison functors agree under the bridge. -/
noncomputable def affineModuleDescentComparisonIso
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    affineModuleDescentComparison f ⋙ affineModuleDescentToComonadic f ≅
      comonadicModuleDescentComparison f.hom :=
  NatIso.ofComponents (fun N => affineModuleDescentComparisonIsoApp f N) <| by
    intro N₁ N₂ n
    apply Comonad.Coalgebra.Hom.ext
    dsimp only [Functor.comp_map, affineModuleDescentComparison,
      affineModuleDescentToComonadic, affineModuleDescentToComonadicMap,
      affineModuleDescentComparisonIsoApp]
    change (ModuleCat.extendScalars f.hom).map n ≫
        𝟙 ((ModuleCat.extendScalars f.hom).obj N₂) =
      𝟙 ((ModuleCat.extendScalars f.hom).obj N₁) ≫
        (ModuleCat.extendScalars f.hom).map n
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- The full choice-free affine/comonadic bridge. -/
noncomputable def affineModuleComonadicBridge
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    AffineModuleComonadicBridge f where
  equivalence := affineModuleComonadicEquivalence f
  comparisonIso := affineModuleDescentComparisonIso f

/-- The canonical chosen Čech/comonadic bridge. -/
noncomputable def affineCechComonadicBridge
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    AffineCechComonadicBridge f :=
  (affineModuleComonadicBridge f).toCech

/-- Transport an isomorphism from the comonadic side of the canonical bridge
back to an isomorphism of chosen affine Čech descent data. This is the
object-level comparison API needed when a cover-level linear equivalence has
already been proved compatible with the two comonad coactions. -/
noncomputable def affineCechIsoOfComonadicIso
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (D : AffineCechModuleDescentData f)
    (Q : ComonadicModuleDescentData f.hom)
    (q : (affineCechComonadicBridge f).equivalence.functor.obj D ≅ Q) :
    D ≅ (affineCechComonadicBridge f).equivalence.inverse.obj Q :=
  (affineCechComonadicBridge f).equivalence.unitIso.app D ≪≫
    (affineCechComonadicBridge f).equivalence.inverse.mapIso q

/-- A carrier isomorphism satisfying the precise coaction square determines
an isomorphism from a chosen affine Čech datum to the inverse-bridge datum of
the target coalgebra. -/
noncomputable def affineCechIsoOfComonadicCarrierIso
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (D : AffineCechModuleDescentData f)
    (Q : ComonadicModuleDescentData f.hom)
    (e : ((affineCechComonadicBridge f).equivalence.functor.obj D).A ≅ Q.A)
    (h :
      ((affineCechComonadicBridge f).equivalence.functor.obj D).a ≫
          ((ModuleCat.extendRestrictScalarsAdj f.hom).toComonad).map e.hom =
        e.hom ≫ Q.a) :
    D ≅ (affineCechComonadicBridge f).equivalence.inverse.obj Q :=
  affineCechIsoOfComonadicIso f D Q
    (Comonad.Coalgebra.isoMk e h)

/-- Applying the bridge to the transported Čech isomorphism recovers the
supplied comonadic isomorphism through the equivalence counit. -/
theorem affineCechIsoOfComonadicIso_comonadic_hom
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (D : AffineCechModuleDescentData f)
    (Q : ComonadicModuleDescentData f.hom)
    (q : (affineCechComonadicBridge f).equivalence.functor.obj D ≅ Q) :
    (affineCechComonadicBridge f).equivalence.functor.map
        (affineCechIsoOfComonadicIso f D Q q).hom ≫
      (affineCechComonadicBridge f).equivalence.counitIso.hom.app Q =
        q.hom := by
  simp [affineCechIsoOfComonadicIso, Category.assoc]

/-- Faithfully flat ring maps have effective chosen Čech module descent. -/
theorem affineCechModuleDescentComparison_isEquivalence
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat) :
    (affineCechModuleDescentComparison f).IsEquivalence :=
  affineCechModuleDescentComparison_isEquivalence_of_bridge
    f hf (affineCechComonadicBridge f)

/-- Faithfully flat ring maps have effective choice-free affine module
descent. -/
theorem affineModuleDescentComparison_isEquivalence
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat) :
    (affineModuleDescentComparison f).IsEquivalence :=
  affineModuleDescentComparison_isEquivalence_of_bridge
    f hf (affineCechComonadicBridge f)

/-- A chosen Cech module descent datum over a faithfully flat map has an
explicitly selected descended module. -/
noncomputable def affineCechDescendedModule
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D : AffineCechModuleDescentData f) :
    ModuleCat R := by
  let F := affineCechModuleDescentComparison f
  let _ : F.IsEquivalence :=
    affineCechModuleDescentComparison_isEquivalence f hf
  exact F.objPreimage D

/-- The comparison functor carries the selected descended module back to the
given Cech datum. -/
noncomputable def affineCechDescendedModuleIso
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D : AffineCechModuleDescentData f) :
    (affineCechModuleDescentComparison f).obj
        (affineCechDescendedModule f hf D) ≅ D := by
  let F := affineCechModuleDescentComparison f
  let _ : F.IsEquivalence :=
    affineCechModuleDescentComparison_isEquivalence f hf
  exact F.objObjPreimageIso D

/-- On the cover, the selected descended module base-changes to the module
carried by the supplied Cech datum. -/
noncomputable def affineCechDescendedModuleBaseChangeIso
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D : AffineCechModuleDescentData f) :
    (ModuleCat.extendScalars f.hom).obj
        (affineCechDescendedModule f hf D) ≅
      D.obj PUnit.unit :=
  (AffineCechModuleDescentData.evaluation f).mapIso
    (affineCechDescendedModuleIso f hf D)

/-- A morphism of chosen Čech descent data descends to the selected
base-ring modules.

This is the morphism-level effective-descent step needed before algebra,
coaction, and torsor structure maps can be transported. It uses Mathlib's
full inverse-image operation for an equivalence functor. -/
noncomputable def affineCechDescendedModuleHom
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    {D E : AffineCechModuleDescentData f} (g : D ⟶ E) :
    affineCechDescendedModule f hf D ⟶
      affineCechDescendedModule f hf E := by
  let F := affineCechModuleDescentComparison f
  let _ : F.IsEquivalence :=
    affineCechModuleDescentComparison_isEquivalence f hf
  exact F.preimage
    ((affineCechDescendedModuleIso f hf D).hom ≫ g ≫
      (affineCechDescendedModuleIso f hf E).inv)

/-- Comparing a selected descended morphism recovers the supplied morphism,
conjugated by the selected object-level comparison isomorphisms. -/
@[simp] theorem affineCechDescendedModuleHom_comparison
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    {D E : AffineCechModuleDescentData f} (g : D ⟶ E) :
    (affineCechModuleDescentComparison f).map
        (affineCechDescendedModuleHom f hf g) =
      (affineCechDescendedModuleIso f hf D).hom ≫ g ≫
        (affineCechDescendedModuleIso f hf E).inv := by
  let F := affineCechModuleDescentComparison f
  let _ : F.IsEquivalence :=
    affineCechModuleDescentComparison_isEquivalence f hf
  exact F.map_preimage _

/-- The selected descent operation preserves identity morphisms. -/
@[simp] theorem affineCechDescendedModuleHom_id
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    (D : AffineCechModuleDescentData f) :
    affineCechDescendedModuleHom f hf (𝟙 D) =
      𝟙 (affineCechDescendedModule f hf D) := by
  let F := affineCechModuleDescentComparison f
  let _ : F.IsEquivalence :=
    affineCechModuleDescentComparison_isEquivalence f hf
  apply F.map_injective
  rw [affineCechDescendedModuleHom_comparison, F.map_id]
  simp
  rfl

/-- The selected descent operation preserves composition. -/
@[simp] theorem affineCechDescendedModuleHom_comp
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    {D E H : AffineCechModuleDescentData f}
    (g : D ⟶ E) (h : E ⟶ H) :
    affineCechDescendedModuleHom f hf (g ≫ h) =
      affineCechDescendedModuleHom f hf g ≫
        affineCechDescendedModuleHom f hf h := by
  let F := affineCechModuleDescentComparison f
  let _ : F.IsEquivalence :=
    affineCechModuleDescentComparison_isEquivalence f hf
  apply F.map_injective
  rw [affineCechDescendedModuleHom_comparison, F.map_comp,
    affineCechDescendedModuleHom_comparison,
    affineCechDescendedModuleHom_comparison]
  simp [Category.assoc]

/-- A descended morphism is uniquely characterized by its comparison square
on the faithfully flat cover. -/
theorem affineCechDescendedModuleHom_unique
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    {D E : AffineCechModuleDescentData f} (g : D ⟶ E)
    (q : affineCechDescendedModule f hf D ⟶
      affineCechDescendedModule f hf E)
    (hq : (affineCechModuleDescentComparison f).map q ≫
        (affineCechDescendedModuleIso f hf E).hom =
      (affineCechDescendedModuleIso f hf D).hom ≫ g) :
    q = affineCechDescendedModuleHom f hf g := by
  let F := affineCechModuleDescentComparison f
  let _ : F.IsEquivalence :=
    affineCechModuleDescentComparison_isEquivalence f hf
  apply F.map_injective
  rw [affineCechDescendedModuleHom_comparison]
  apply (cancel_mono (affineCechDescendedModuleIso f hf E).hom).1
  simpa [Category.assoc] using hq

/-- After base change, the selected descended morphism is the supplied cover
morphism conjugated by the selected base-change isomorphisms. -/
@[simp] theorem affineCechDescendedModuleHom_baseChange
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat)
    {D E : AffineCechModuleDescentData f} (g : D ⟶ E) :
    (ModuleCat.extendScalars f.hom).map
        (affineCechDescendedModuleHom f hf g) =
      (affineCechDescendedModuleBaseChangeIso f hf D).hom ≫
        g.hom PUnit.unit ≫
          (affineCechDescendedModuleBaseChangeIso f hf E).inv := by
  change (AffineCechModuleDescentData.evaluation f).map
    ((affineCechModuleDescentComparison f).map
      (affineCechDescendedModuleHom f hf g)) = _
  rw [affineCechDescendedModuleHom_comparison]
  rfl

/-- The selected object and morphism descent operations form a functor. -/
noncomputable def affineCechDescendedModuleFunctor
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat) :
    AffineCechModuleDescentData f ⥤ ModuleCat R where
  obj := affineCechDescendedModule f hf
  map := affineCechDescendedModuleHom f hf
  map_id := affineCechDescendedModuleHom_id f hf
  map_comp := affineCechDescendedModuleHom_comp f hf

/-- The selected descent functor followed by comparison is naturally
isomorphic to the identity on chosen Čech module descent data. -/
noncomputable def affineCechDescendedModuleComparisonIso
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat) :
    affineCechDescendedModuleFunctor f hf ⋙
        affineCechModuleDescentComparison f ≅
      𝟭 (AffineCechModuleDescentData f) :=
  NatIso.ofComponents
    (fun D => affineCechDescendedModuleIso f hf D)
    (by
      intro D E g
      change (affineCechModuleDescentComparison f).map
          (affineCechDescendedModuleHom f hf g) ≫
            (affineCechDescendedModuleIso f hf E).hom =
        (affineCechDescendedModuleIso f hf D).hom ≫ g
      rw [affineCechDescendedModuleHom_comparison]
      simp [Category.assoc])

/-- Affine modules satisfy singleton faithfully flat descent. -/
theorem affineModulePseudofunctor_isStackFor_singleton
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (hf : f.hom.FaithfullyFlat) :
    affineModulePseudofunctor.IsStackFor (Presieve.singleton f.op) :=
  affineModulePseudofunctor_isStackFor_singleton_of_bridge
    f hf (affineCechComonadicBridge f)

end RiemannResearch.AlgebraicGeometry
