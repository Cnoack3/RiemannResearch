/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.RingTheory.Bialgebra.Convolution
import RiemannResearch.AlgebraicGeometry.UpperUnitriangularThreeCoordinateHopf

/-!
# Points represented by the upper-unitriangular coordinate Hopf algebra

This file identifies morphisms from `ℤ[x₁₂,x₂₃,x₁₃]` with the point model
`UpperUnitriangularThree.Point`.  It also proves that convolution induced by
the coordinate Hopf algebra is exactly the Heisenberg multiplication

`(a,b,c)(a',b',c') = (a+a', b+b', c+c'+ab')`.

The equivalence is natural under morphisms of commutative rings.  This closes
the representability gap between the point-level group and the affine group
scheme constructed from the Hopf algebra.
-/

open scoped TensorProduct
open WithConv
open Algebra Coalgebra Bialgebra TensorProduct

namespace RiemannResearch
namespace AlgebraicGeometry
namespace UpperUnitriangularThree

namespace Point

variable {R S T : Type} [CommRing R] [CommRing S] [CommRing T]

/-- Base change of an upper-unitriangular point along a ring morphism. -/
def map (f : R →+* S) (x : Point R) : Point S :=
  ⟨f x.root12, f x.root23, f x.root13⟩

@[simp] theorem map_root12 (f : R →+* S) (x : Point R) :
    (map f x).root12 = f x.root12 := rfl

@[simp] theorem map_root23 (f : R →+* S) (x : Point R) :
    (map f x).root23 = f x.root23 := rfl

@[simp] theorem map_root13 (f : R →+* S) (x : Point R) :
    (map f x).root13 = f x.root13 := rfl

@[simp] theorem map_id (x : Point R) :
    map (RingHom.id R) x = x := by
  ext <;> rfl

@[simp] theorem map_comp (g : S →+* T) (f : R →+* S) (x : Point R) :
    map (g.comp f) x = map g (map f x) := by
  ext <;> rfl

/-- Base change is a homomorphism of the point groups. -/
def mapHom (f : R →+* S) : Point R →* Point S where
  toFun := map f
  map_one' := by
    ext <;> simp [map]
  map_mul' x y := by
    ext <;> simp [map]

@[simp] theorem mapHom_apply (f : R →+* S) (x : Point R) :
    mapHom f x = map f x := rfl

end Point

/-- Evaluation of the coordinate variables at an upper-unitriangular point. -/
noncomputable def coordinateEvaluation
    {S : Type} [CommRing S] (p : Point S) : Coordinate →+* S :=
  (MvPolynomial.aeval ![p.root12, p.root23, p.root13]).toRingHom

@[simp] theorem coordinateEvaluation_x12
    {S : Type} [CommRing S] (p : Point S) :
    coordinateEvaluation p x12 = p.root12 := by
  simp [coordinateEvaluation, x12]

@[simp] theorem coordinateEvaluation_x23
    {S : Type} [CommRing S] (p : Point S) :
    coordinateEvaluation p x23 = p.root23 := by
  simp [coordinateEvaluation, x23]

@[simp] theorem coordinateEvaluation_x13
    {S : Type} [CommRing S] (p : Point S) :
    coordinateEvaluation p x13 = p.root13 := by
  simp [coordinateEvaluation, x13]

private theorem coordinateEvaluation_baseChange
    {S : Type} [CommRing S] (f : Coordinate →+* S) :
    coordinateEvaluation ⟨f x12, f x23, f x13⟩ = f := by
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [coordinateEvaluation]
  · intro i
    fin_cases i <;> simp [coordinateEvaluation, x12, x23, x13]

private theorem coordinateEvaluation_point
    {S : Type} [CommRing S] (p : Point S) :
    (⟨coordinateEvaluation p x12,
        coordinateEvaluation p x23,
        coordinateEvaluation p x13⟩ : Point S) = p := by
  ext <;> simp

/-- Ring morphisms from the integral coordinate algebra are naturally
identified with upper-unitriangular points. -/
noncomputable def coordinateRingHomEquiv
    (S : Type) [CommRing S] :
    (Coordinate →+* S) ≃ Point S where
  toFun f := ⟨f x12, f x23, f x13⟩
  invFun := coordinateEvaluation
  left_inv := coordinateEvaluation_baseChange
  right_inv := coordinateEvaluation_point

@[simp] theorem coordinateRingHomEquiv_apply
    {S : Type} [CommRing S] (f : Coordinate →+* S) :
    coordinateRingHomEquiv S f = ⟨f x12, f x23, f x13⟩ := rfl

@[simp] theorem coordinateRingHomEquiv_symm_apply
    {S : Type} [CommRing S] (p : Point S) :
    (coordinateRingHomEquiv S).symm p = coordinateEvaluation p := rfl

/-- The ring-hom representability equivalence commutes with base change. -/
@[simp] theorem coordinateRingHomEquiv_naturality
    {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (φ : Coordinate →+* R) :
    coordinateRingHomEquiv S (f.comp φ) =
      Point.map f (coordinateRingHomEquiv R φ) := by
  rfl

/-- Evaluation as an `ℤ`-algebra morphism, used by Hopf convolution. -/
noncomputable def coordinateAlgEvaluation
    {S : Type} [CommRing S] (p : Point S) : Coordinate →ₐ[ℤ] S :=
  MvPolynomial.aeval ![p.root12, p.root23, p.root13]

@[simp] theorem coordinateAlgEvaluation_x12
    {S : Type} [CommRing S] (p : Point S) :
    coordinateAlgEvaluation p x12 = p.root12 := by
  simp [coordinateAlgEvaluation, x12]

@[simp] theorem coordinateAlgEvaluation_x23
    {S : Type} [CommRing S] (p : Point S) :
    coordinateAlgEvaluation p x23 = p.root23 := by
  simp [coordinateAlgEvaluation, x23]

@[simp] theorem coordinateAlgEvaluation_x13
    {S : Type} [CommRing S] (p : Point S) :
    coordinateAlgEvaluation p x13 = p.root13 := by
  simp [coordinateAlgEvaluation, x13]

private theorem coordinateAlgEvaluation_baseChange
    {S : Type} [CommRing S] (f : Coordinate →ₐ[ℤ] S) :
    coordinateAlgEvaluation ⟨f x12, f x23, f x13⟩ = f := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [coordinateAlgEvaluation, x12, x23, x13]

private theorem coordinateAlgEvaluation_point
    {S : Type} [CommRing S] (p : Point S) :
    (⟨coordinateAlgEvaluation p x12,
        coordinateAlgEvaluation p x23,
        coordinateAlgEvaluation p x13⟩ : Point S) = p := by
  ext <;> simp

/-- `ℤ`-algebra morphisms from the coordinate algebra are represented by the
same point model. -/
noncomputable def coordinateAlgHomEquiv
    (S : Type) [CommRing S] :
    (Coordinate →ₐ[ℤ] S) ≃ Point S where
  toFun f := ⟨f x12, f x23, f x13⟩
  invFun := coordinateAlgEvaluation
  left_inv := coordinateAlgEvaluation_baseChange
  right_inv := coordinateAlgEvaluation_point

@[simp] theorem coordinateAlgHomEquiv_apply
    {S : Type} [CommRing S] (f : Coordinate →ₐ[ℤ] S) :
    coordinateAlgHomEquiv S f = ⟨f x12, f x23, f x13⟩ := rfl

@[simp] theorem coordinateAlgHomEquiv_symm_apply
    {S : Type} [CommRing S] (p : Point S) :
    (coordinateAlgHomEquiv S).symm p = coordinateAlgEvaluation p := rfl

/-- The algebra-hom representability equivalence commutes with base change. -/
@[simp] theorem coordinateAlgHomEquiv_naturality
    {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (φ : Coordinate →ₐ[ℤ] R) :
    coordinateAlgHomEquiv S (f.toIntAlgHom.comp φ) =
      Point.map f (coordinateAlgHomEquiv R φ) := by
  rfl

noncomputable local instance : Bialgebra ℤ Coordinate := bialgebra

/-- Convolution adds the first simple-root coordinate. -/
theorem pointConvolution_mul_x12
    {S : Type} [CommRing S]
    (f g : WithConv (Coordinate →ₐ[ℤ] S)) :
    (f * g).ofConv x12 = f.ofConv x12 + g.ofConv x12 := by
  rw [AlgHom.convMul_apply]
  have hx : CoalgebraStruct.comul (R := ℤ) (A := Coordinate) x12 =
      x12 ⊗ₜ[ℤ] (1 : Coordinate) + (1 : Coordinate) ⊗ₜ[ℤ] x12 := by
    change comul.toLinearMap x12 = _
    exact comul_x12
  rw [hx]
  simp

/-- Convolution adds the second simple-root coordinate. -/
theorem pointConvolution_mul_x23
    {S : Type} [CommRing S]
    (f g : WithConv (Coordinate →ₐ[ℤ] S)) :
    (f * g).ofConv x23 = f.ofConv x23 + g.ofConv x23 := by
  rw [AlgHom.convMul_apply]
  have hx : CoalgebraStruct.comul (R := ℤ) (A := Coordinate) x23 =
      x23 ⊗ₜ[ℤ] (1 : Coordinate) + (1 : Coordinate) ⊗ₜ[ℤ] x23 := by
    change comul.toLinearMap x23 = _
    exact comul_x23
  rw [hx]
  simp

/-- Convolution on the height-two coordinate contains the Chevalley cross
term from the two simple roots. -/
theorem pointConvolution_mul_x13
    {S : Type} [CommRing S]
    (f g : WithConv (Coordinate →ₐ[ℤ] S)) :
    (f * g).ofConv x13 =
      f.ofConv x13 + g.ofConv x13 + f.ofConv x12 * g.ofConv x23 := by
  rw [AlgHom.convMul_apply]
  have hx : CoalgebraStruct.comul (R := ℤ) (A := Coordinate) x13 =
      x13 ⊗ₜ[ℤ] (1 : Coordinate) + (1 : Coordinate) ⊗ₜ[ℤ] x13 +
        x12 ⊗ₜ[ℤ] x23 := by
    change comul.toLinearMap x13 = _
    exact comul_x13
  rw [hx]
  simp

/-- The Hopf-convolution point group is the existing pointwise Heisenberg
group. -/
noncomputable def pointConvolutionEquiv
    (S : Type) [CommRing S] :
    WithConv (Coordinate →ₐ[ℤ] S) ≃* Point S where
  toFun f := ⟨f.ofConv x12, f.ofConv x23, f.ofConv x13⟩
  invFun p := WithConv.toConv (coordinateAlgEvaluation p)
  left_inv f := by
    apply WithConv.ofConv_injective
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;>
      simp [coordinateAlgEvaluation, x12, x23, x13]
  right_inv p := by
    ext <;> simp [coordinateAlgEvaluation, x12, x23, x13]
  map_mul' f g := by
    ext
    · exact pointConvolution_mul_x12 f g
    · exact pointConvolution_mul_x23 f g
    · exact pointConvolution_mul_x13 f g

@[simp] theorem pointConvolutionEquiv_apply
    {S : Type} [CommRing S]
    (f : WithConv (Coordinate →ₐ[ℤ] S)) :
    pointConvolutionEquiv S f =
      coordinateAlgHomEquiv S f.ofConv := rfl

@[simp] theorem pointConvolutionEquiv_symm_apply
    {S : Type} [CommRing S] (p : Point S) :
    (pointConvolutionEquiv S).symm p =
      WithConv.toConv (coordinateAlgEvaluation p) := rfl

/-- Convolution corresponds exactly to the multiplication already installed
on `Point S`. -/
theorem coordinateAlgHomEquiv_convolution
    {S : Type} [CommRing S]
    (f g : WithConv (Coordinate →ₐ[ℤ] S)) :
    coordinateAlgHomEquiv S (f * g).ofConv =
      coordinateAlgHomEquiv S f.ofConv *
        coordinateAlgHomEquiv S g.ofConv :=
  (pointConvolutionEquiv S).map_mul f g

end UpperUnitriangularThree
end AlgebraicGeometry
end RiemannResearch
