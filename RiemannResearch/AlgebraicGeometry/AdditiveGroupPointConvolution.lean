/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.AdditiveGroupPoints
import Mathlib.RingTheory.Bialgebra.Convolution
import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# Convolution law on points of the additive affine group

This file identifies the Hopf-convolution product on algebra maps
`R[X] →ₐ[R] S` with addition in `S`.  It is the point-level group-law bridge
needed when a genuine Chevalley root-subgroup morphism is later constructed.

No E8 group, root subgroup, or filtration is assumed here.
-/

open scoped TensorProduct
open WithConv
open Algebra Coalgebra Bialgebra TensorProduct

namespace RiemannResearch
namespace AlgebraicGeometry
namespace AdditiveGroup

universe u v

variable (R : Type u) [CommRing R]
variable (S : Type v) [CommRing S] [Algebra R S]

noncomputable local instance : Bialgebra R (Coordinate R) :=
  bialgebra R

/-- Convolution of two `S`-valued points of `Gₐ` adds their values at the
polynomial generator. -/
theorem pointConvolution_mul_X
    (f g : WithConv (Coordinate R →ₐ[R] S)) :
    (f * g).ofConv Polynomial.X =
      f.ofConv Polynomial.X + g.ofConv Polynomial.X := by
  rw [AlgHom.convMul_apply]
  have hx : CoalgebraStruct.comul (R := R) (A := Coordinate R)
      (Polynomial.X : Coordinate R) =
      Polynomial.X ⊗ₜ[R] (1 : Coordinate R) +
        (1 : Coordinate R) ⊗ₜ[R] Polynomial.X := by
    change (comul R).toLinearMap (Polynomial.X : Coordinate R) = _
    simp [comul, Algebra.TensorProduct.includeLeft,
      Algebra.TensorProduct.includeRight]
  rw [hx]
  simp

/-- The convolution point group of `Gₐ` is multiplicatively equivalent to the
additive group of the target algebra. -/
noncomputable def pointConvolutionEquiv :
    WithConv (Coordinate R →ₐ[R] S) ≃* Multiplicative S where
  toFun f := Multiplicative.ofAdd (f.ofConv Polynomial.X)
  invFun s := WithConv.toConv (Polynomial.aeval s.toAdd)
  left_inv f := by
    apply WithConv.ofConv_injective
    apply Polynomial.algHom_ext
    simp
  right_inv s := by
    cases s
    simp
  map_mul' f g := by
    change Multiplicative.ofAdd ((f * g).ofConv Polynomial.X) =
      Multiplicative.ofAdd
        (f.ofConv Polynomial.X + g.ofConv Polynomial.X)
    congr 1
    exact pointConvolution_mul_X R S f g

@[simp]
theorem pointConvolutionEquiv_apply
    (f : WithConv (Coordinate R →ₐ[R] S)) :
    pointConvolutionEquiv R S f =
      Multiplicative.ofAdd (f.ofConv Polynomial.X) :=
  rfl

@[simp]
theorem pointConvolutionEquiv_symm_apply (s : Multiplicative S) :
    (pointConvolutionEquiv R S).symm s =
      WithConv.toConv (Polynomial.aeval s.toAdd) :=
  rfl

end AdditiveGroup
end AlgebraicGeometry
end RiemannResearch
