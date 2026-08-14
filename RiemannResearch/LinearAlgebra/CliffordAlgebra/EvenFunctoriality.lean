/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.LinearAlgebra.CliffordAlgebra.BaseChange
import Mathlib.LinearAlgebra.CliffordAlgebra.Even
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import Mathlib.LinearAlgebra.Projection

/-!
# Functoriality of the even Clifford algebra

This file provides the algebraic layer needed below D4 triality:

* a quadratic isometry maps the even Clifford subalgebra into the even
  Clifford subalgebra;
* an isometry equivalence induces an equivalence of even Clifford algebras;
* scalar extension has a canonical map from the scalar extension of the even
  Clifford algebra to the even Clifford algebra of the extended form; and
* Mathlib's pointwise spin group embeds faithfully into the units of the even
  Clifford algebra.

The scalar-extension declaration is deliberately only an algebra homomorphism.
No flatness hypothesis is imposed here, so this file does not claim that the
map is an equivalence. Likewise, `SpinPoint` means an element of Mathlib's
pointwise group `spinGroup Q`; it is not an affine group scheme, a base-change
theorem for such a scheme, or a construction of half-spin representations.

The proofs use the universal-property and even-induction APIs in Mathlib's
`CliffordAlgebra.Even`, `CliffordAlgebra.BaseChange`, and
`CliffordAlgebra.SpinGroup` modules.
-/

namespace RiemannResearch.LinearAlgebra.CliffordEven

open CliffordAlgebra
open scoped TensorProduct

section Functoriality

variable {R M₁ M₂ M₃ : Type*}
variable [CommRing R]
variable [AddCommGroup M₁] [Module R M₁]
variable [AddCommGroup M₂] [Module R M₂]
variable [AddCommGroup M₃] [Module R M₃]
variable {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
variable {Q₃ : QuadraticForm R M₃}

/-- A quadratic isometry sends even Clifford elements to even Clifford
elements. -/
theorem map_mem_even
    (f : Q₁ →qᵢ Q₂) {x : CliffordAlgebra Q₁}
    (hx : x ∈ even Q₁) :
    map f x ∈ even Q₂ := by
  change x ∈ (even Q₁).toSubmodule at hx
  rw [even_toSubmodule] at hx
  induction x, hx using even_induction with
  | algebraMap r =>
      rw [(map f).commutes r]
      exact (even Q₂).algebraMap_mem r
  | add x y hx hy ihx ihy =>
      simpa using (even Q₂).add_mem ihx ihy
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
      have hp : ι Q₂ (f m₁) * ι Q₂ (f m₂) ∈ even Q₂ := by
        change ι Q₂ (f m₁) * ι Q₂ (f m₂) ∈ (even Q₂).toSubmodule
        rw [even_toSubmodule]
        exact ι_mul_ι_mem_evenOdd_zero Q₂ (f m₁) (f m₂)
      simpa [map_apply_ι] using (even Q₂).mul_mem hp ih

/-- The algebra homomorphism on even Clifford algebras induced by a quadratic
isometry. -/
def evenMap (f : Q₁ →qᵢ Q₂) : even Q₁ →ₐ[R] even Q₂ :=
  ((map f).comp (even Q₁).val).codRestrict (even Q₂) fun x =>
    map_mem_even f x.property

@[simp]
theorem coe_evenMap_apply (f : Q₁ →qᵢ Q₂) (x : even Q₁) :
    (evenMap f x : CliffordAlgebra Q₂) = map f x := rfl

@[simp]
theorem evenMap_id (Q : QuadraticForm R M₁) :
    evenMap (QuadraticMap.Isometry.id Q) = AlgHom.id R (even Q) := by
  apply AlgHom.ext
  intro x
  apply Subtype.ext
  change map (QuadraticMap.Isometry.id Q) (x : CliffordAlgebra Q) = x
  rw [map_id]
  rfl

theorem evenMap_comp (f : Q₂ →qᵢ Q₃) (g : Q₁ →qᵢ Q₂) :
    (evenMap f).comp (evenMap g) = evenMap (f.comp g) := by
  apply AlgHom.ext
  intro x
  apply Subtype.ext
  change map f (map g (x : CliffordAlgebra Q₁)) =
    map (f.comp g) (x : CliffordAlgebra Q₁)
  exact DFunLike.congr_fun (map_comp_map f g) (x : CliffordAlgebra Q₁)

/-- A quadratic isometry equivalence restricts to the even Clifford
subalgebras. -/
def evenEquivOfIsometry (e : Q₁.IsometryEquiv Q₂) :
    even Q₁ ≃ₐ[R] even Q₂ :=
  AlgEquiv.ofAlgHom
    (evenMap e.toIsometry)
    (evenMap e.symm.toIsometry)
    (by
      apply AlgHom.ext
      intro x
      apply Subtype.ext
      change map e.toIsometry (map e.symm.toIsometry
        (x : CliffordAlgebra Q₂)) = x
      rw [← equivOfIsometry_apply, ← equivOfIsometry_apply,
        ← equivOfIsometry_symm]
      exact (equivOfIsometry e).apply_symm_apply x)
    (by
      apply AlgHom.ext
      intro x
      apply Subtype.ext
      change map e.symm.toIsometry (map e.toIsometry
        (x : CliffordAlgebra Q₁)) = x
      rw [← equivOfIsometry_apply, ← equivOfIsometry_apply,
        ← equivOfIsometry_symm]
      exact (equivOfIsometry e).symm_apply_apply x)

@[simp]
theorem coe_evenEquivOfIsometry_apply
    (e : Q₁.IsometryEquiv Q₂) (x : even Q₁) :
    (evenEquivOfIsometry e x : CliffordAlgebra Q₂) =
      equivOfIsometry e x := rfl

theorem evenEquivOfIsometry_symm (e : Q₁.IsometryEquiv Q₂) :
    (evenEquivOfIsometry e).symm = evenEquivOfIsometry e.symm := by
  ext x
  change (equivOfIsometry e).symm (x : CliffordAlgebra Q₂) =
    equivOfIsometry e.symm x
  rw [equivOfIsometry_symm]

theorem evenEquivOfIsometry_trans
    (e₁₂ : Q₁.IsometryEquiv Q₂) (e₂₃ : Q₂.IsometryEquiv Q₃) :
    (evenEquivOfIsometry e₁₂).trans (evenEquivOfIsometry e₂₃) =
      evenEquivOfIsometry (e₁₂.trans e₂₃) := by
  ext x
  change equivOfIsometry e₂₃
      (equivOfIsometry e₁₂ (x : CliffordAlgebra Q₁)) =
    equivOfIsometry (e₁₂.trans e₂₃) x
  exact DFunLike.congr_fun (equivOfIsometry_trans e₁₂ e₂₃)
    (x : CliffordAlgebra Q₁)

end Functoriality

section BaseChange

variable {R A V : Type*}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup V] [Module R V] [Invertible (2 : R)]
variable (Q : QuadraticForm R V)

/-- The auxiliary Clifford base-change map preserves the even subalgebra. -/
theorem ofBaseChangeAux_mem_even
    {x : CliffordAlgebra Q} (hx : x ∈ even Q) :
    ofBaseChangeAux A Q x ∈ even (Q.baseChange A) := by
  change x ∈ (even Q).toSubmodule at hx
  rw [even_toSubmodule] at hx
  induction x, hx using even_induction with
  | algebraMap r =>
      rw [(ofBaseChangeAux A Q).commutes r]
      rw [IsScalarTower.algebraMap_apply R A
        (CliffordAlgebra (Q.baseChange A)) r]
      exact (even (Q.baseChange A)).algebraMap_mem (algebraMap R A r)
  | add x y hx hy ihx ihy =>
      simpa using (even (Q.baseChange A)).add_mem ihx ihy
  | ι_mul_ι_mul v w x hx ih =>
      have hp :
          ι (Q.baseChange A) (1 ⊗ₜ[R] v) *
              ι (Q.baseChange A) (1 ⊗ₜ[R] w) ∈
            even (Q.baseChange A) := by
        change
          ι (Q.baseChange A) (1 ⊗ₜ[R] v) *
              ι (Q.baseChange A) (1 ⊗ₜ[R] w) ∈
            (even (Q.baseChange A)).toSubmodule
        rw [even_toSubmodule]
        exact ι_mul_ι_mem_evenOdd_zero (Q.baseChange A) _ _
      simpa [ofBaseChangeAux_ι] using
        (even (Q.baseChange A)).mul_mem hp ih

/-- The restriction of the auxiliary Clifford base-change map to the even
subalgebra. -/
def evenOfBaseChangeAux : even Q →ₐ[R] even (Q.baseChange A) where
  toFun x := ⟨ofBaseChangeAux A Q x,
    ofBaseChangeAux_mem_even (A := A) Q x.property⟩
  map_one' := by
    apply Subtype.ext
    exact (ofBaseChangeAux A Q).map_one
  map_mul' x y := by
    apply Subtype.ext
    exact (ofBaseChangeAux A Q).map_mul (x : CliffordAlgebra Q) y
  map_zero' := by
    apply Subtype.ext
    exact (ofBaseChangeAux A Q).map_zero
  map_add' x y := by
    apply Subtype.ext
    exact (ofBaseChangeAux A Q).map_add (x : CliffordAlgebra Q) y
  commutes' r := by
    apply Subtype.ext
    simp

@[simp]
theorem coe_evenOfBaseChangeAux_apply (x : even Q) :
    (evenOfBaseChangeAux (A := A) Q x :
      CliffordAlgebra (Q.baseChange A)) =
      ofBaseChangeAux A Q x := rfl

/-- The scalar extension of the inclusion of the even Clifford subalgebra. -/
def tensorEvenInclusion :
    TensorProduct R A (even Q) →ₐ[A]
      TensorProduct R A (CliffordAlgebra Q) :=
  Algebra.TensorProduct.map (AlgHom.id A A) (even Q).val

omit [Invertible (2 : R)] in
@[simp]
theorem tensorEvenInclusion_tmul (a : A) (x : even Q) :
    tensorEvenInclusion (A := A) Q (a ⊗ₜ[R] x) =
      a ⊗ₜ[R] (x : CliffordAlgebra Q) := by
  simp [tensorEvenInclusion]

/-- Projection onto the even summand of the Clifford algebra. -/
noncomputable def evenProjection : CliffordAlgebra Q →ₗ[R] even Q := by
  change CliffordAlgebra Q →ₗ[R] (even Q).toSubmodule
  rw [even_toSubmodule]
  exact (evenOdd Q 0).projectionOnto (evenOdd Q 1)
    (evenOdd_isCompl Q)

omit [Invertible (2 : R)] in
@[simp]
theorem evenProjection_apply (x : even Q) :
    evenProjection Q (x : CliffordAlgebra Q) = x := by
  change
    ((evenOdd Q 0).projectionOnto (evenOdd Q 1)
      (evenOdd_isCompl Q)) (x : CliffordAlgebra Q) = _
  have hx : (x : CliffordAlgebra Q) ∈ evenOdd Q 0 := by
    rw [← even_toSubmodule]
    exact x.property
  exact Submodule.projectionOnto_apply_left (evenOdd_isCompl Q)
    ⟨x, hx⟩

/-- A linear retraction of the scalar-extended even inclusion. -/
noncomputable def tensorEvenRetraction :
    TensorProduct R A (CliffordAlgebra Q) →ₗ[R]
      TensorProduct R A (even Q) :=
  TensorProduct.map LinearMap.id (evenProjection Q)

omit [Invertible (2 : R)] in
theorem tensorEvenRetraction_leftInverse :
    Function.LeftInverse (tensorEvenRetraction (A := A) Q)
      (tensorEvenInclusion (A := A) Q) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
  | tmul a x =>
      simp [tensorEvenRetraction, tensorEvenInclusion]

omit [Invertible (2 : R)] in
theorem tensorEvenInclusion_injective :
    Function.Injective (tensorEvenInclusion (A := A) Q) :=
  (tensorEvenRetraction_leftInverse (A := A) Q).injective

theorem ofBaseChange_tensorEven_mem_even
    (x : TensorProduct R A (even Q)) :
    ofBaseChange A Q (tensorEvenInclusion (A := A) Q x) ∈
      even (Q.baseChange A) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simpa using (even (Q.baseChange A)).add_mem hx hy
  | tmul a x =>
      simp only [tensorEvenInclusion, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply]
      change
        algebraMap A (CliffordAlgebra (Q.baseChange A)) a *
            ofBaseChangeAux A Q (x : CliffordAlgebra Q) ∈
          even (Q.baseChange A)
      exact (even (Q.baseChange A)).mul_mem
        ((even (Q.baseChange A)).algebraMap_mem a)
        (ofBaseChangeAux_mem_even (A := A) Q x.property)

/-- The canonical scalar-extension map for even Clifford algebras.

No bijectivity claim is made without additional hypotheses. -/
def evenOfBaseChange :
    TensorProduct R A (even Q) →ₐ[A] even (Q.baseChange A) :=
  ((ofBaseChange A Q).comp (tensorEvenInclusion (A := A) Q)).codRestrict
    (even (Q.baseChange A)) (ofBaseChange_tensorEven_mem_even (A := A) Q)

theorem evenOfBaseChange_injective :
    Function.Injective (evenOfBaseChange (A := A) Q) := by
  intro x y h
  apply tensorEvenInclusion_injective (A := A) Q
  apply (equivBaseChange A Q).symm.injective
  exact congrArg Subtype.val h

@[simp]
theorem coe_evenOfBaseChange_apply
    (x : TensorProduct R A (even Q)) :
    (evenOfBaseChange (A := A) Q x :
      CliffordAlgebra (Q.baseChange A)) =
      ofBaseChange A Q (tensorEvenInclusion (A := A) Q x) := rfl

@[simp]
theorem evenOfBaseChange_equivBaseChange_symm
    (x : TensorProduct R A (even Q)) :
    (evenOfBaseChange (A := A) Q x :
      CliffordAlgebra (Q.baseChange A)) =
      (equivBaseChange A Q).symm
        (tensorEvenInclusion (A := A) Q x) := rfl

theorem evenOfBaseChange_commutes :
    (even (Q.baseChange A)).val.comp (evenOfBaseChange (A := A) Q) =
      (equivBaseChange A Q).symm.toAlgHom.comp
        (tensorEvenInclusion (A := A) Q) := by
  apply AlgHom.ext
  intro x
  rfl

end BaseChange

section SpinPoints

variable {R M : Type*}
variable [CommRing R] [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)

/-- An element of Mathlib's pointwise spin group. This is not a point of a
group scheme formalized in this project. -/
abbrev SpinPoint := ↥(spinGroup Q)

/-- A spin point, regarded as a unit of the even Clifford algebra. -/
def spinPointToEvenUnit (x : SpinPoint Q) : (even Q)ˣ where
  val := ⟨x.1, spinGroup.mem_even x.2⟩
  inv := ⟨star x.1, spinGroup.mem_even (spinGroup.star_mem x.2)⟩
  val_inv := by
    apply Subtype.ext
    exact spinGroup.coe_mul_star_self x
  inv_val := by
    apply Subtype.ext
    exact spinGroup.coe_star_mul_self x

/-- The pointwise spin group maps to the units of the even Clifford algebra. -/
def spinPointToEvenUnits : SpinPoint Q →* (even Q)ˣ where
  toFun := spinPointToEvenUnit Q
  map_one' := by
    apply Units.ext
    rfl
  map_mul' x y := by
    apply Units.ext
    rfl

@[simp]
theorem coe_spinPointToEvenUnits_apply (x : SpinPoint Q) :
    ((((spinPointToEvenUnits Q x : (even Q)ˣ) : even Q)) :
      CliffordAlgebra Q) = x := rfl

theorem spinPointToEvenUnits_injective :
    Function.Injective (spinPointToEvenUnits Q) := by
  intro x y h
  apply Subtype.ext
  exact congrArg
    (fun z : (even Q)ˣ =>
      (((z : even Q)) : CliffordAlgebra Q)) h

end SpinPoints

end RiemannResearch.LinearAlgebra.CliffordEven
