/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.RingTheory.Bialgebra.Convolution
import RiemannResearch.AlgebraicGeometry.AdditiveVectorGroupScheme

/-!
# Functor of points of additive vector groups

The coordinate algebra `R[X_i | i : ι]` represents the tuple-valued functor
`S ↦ (ι → S)`.  This file proves that equivalence, its naturality, and that
Hopf convolution is coordinatewise addition.
-/

open scoped TensorProduct
open WithConv
open Algebra Coalgebra Bialgebra TensorProduct

namespace RiemannResearch
namespace AlgebraicGeometry
namespace AdditiveVectorGroup

universe u v

variable (R : Type u) [CommRing R]
variable (ι : Type u)
variable (S : Type v) [CommRing S] [Algebra R S]

/-- Algebra morphisms from the vector-group coordinate algebra are exactly
coordinate tuples. -/
noncomputable def coordinateAlgHomEquiv :
    (Coordinate R ι →ₐ[R] S) ≃ (ι → S) where
  toFun f i := f (MvPolynomial.X i)
  invFun x := MvPolynomial.aeval x
  left_inv f := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  right_inv x := by
    funext i
    simp

@[simp] theorem coordinateAlgHomEquiv_apply
    (f : Coordinate R ι →ₐ[R] S) (i : ι) :
    coordinateAlgHomEquiv R ι S f i =
      f (MvPolynomial.X i) := rfl

@[simp] theorem coordinateAlgHomEquiv_symm_apply
    (x : ι → S) :
    (coordinateAlgHomEquiv R ι S).symm x =
      MvPolynomial.aeval x := rfl

/-- The tuple-valued representability equivalence commutes with base change. -/
@[simp] theorem coordinateAlgHomEquiv_naturality
    {T : Type v} [CommRing T] [Algebra R T]
    (g : S →ₐ[R] T) (f : Coordinate R ι →ₐ[R] S) :
    coordinateAlgHomEquiv R ι T (g.comp f) =
      fun i => g (coordinateAlgHomEquiv R ι S f i) := by
  rfl

noncomputable local instance : Bialgebra R (Coordinate R ι) :=
  bialgebra R ι

/-- Hopf convolution adds the value of every primitive coordinate. -/
theorem pointConvolution_mul_X
    (f g : WithConv (Coordinate R ι →ₐ[R] S)) (i : ι) :
    (f * g).ofConv (MvPolynomial.X i) =
      f.ofConv (MvPolynomial.X i) +
        g.ofConv (MvPolynomial.X i) := by
  rw [AlgHom.convMul_apply]
  have hx :
      CoalgebraStruct.comul (R := R) (A := Coordinate R ι)
        (MvPolynomial.X i) =
      MvPolynomial.X i ⊗ₜ[R] (1 : Coordinate R ι) +
        (1 : Coordinate R ι) ⊗ₜ[R] MvPolynomial.X i := by
    change (comul R ι).toLinearMap (MvPolynomial.X i) = _
    exact comul_X R ι i
  rw [hx]
  simp

/-- The convolution point group of the vector group is coordinatewise
addition, expressed multiplicatively. -/
noncomputable def pointConvolutionEquiv :
    WithConv (Coordinate R ι →ₐ[R] S) ≃*
      Multiplicative (ι → S) where
  toFun f :=
    Multiplicative.ofAdd (fun i => f.ofConv (MvPolynomial.X i))
  invFun x :=
    WithConv.toConv (MvPolynomial.aeval x.toAdd)
  left_inv f := by
    apply WithConv.ofConv_injective
    apply MvPolynomial.algHom_ext
    intro i
    simp
  right_inv x := by
    cases x
    simp
  map_mul' f g := by
    change Multiplicative.ofAdd
        (fun i => (f * g).ofConv (MvPolynomial.X i)) =
      Multiplicative.ofAdd
        (fun i =>
          f.ofConv (MvPolynomial.X i) +
            g.ofConv (MvPolynomial.X i))
    congr 1
    funext i
    exact pointConvolution_mul_X R ι S f g i

@[simp] theorem pointConvolutionEquiv_apply
    (f : WithConv (Coordinate R ι →ₐ[R] S)) :
    pointConvolutionEquiv R ι S f =
      Multiplicative.ofAdd
        (fun i => f.ofConv (MvPolynomial.X i)) := rfl

@[simp] theorem pointConvolutionEquiv_symm_apply
    (x : Multiplicative (ι → S)) :
    (pointConvolutionEquiv R ι S).symm x =
      WithConv.toConv (MvPolynomial.aeval x.toAdd) := rfl

end AdditiveVectorGroup
end AlgebraicGeometry
end RiemannResearch
