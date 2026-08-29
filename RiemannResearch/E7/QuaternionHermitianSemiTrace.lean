/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E7.QuaternionHermitianAdjointAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Reduced traces and semitraces for the degree-eight E7 adjoint algebra

This file adds the trace-theoretic part of a quadratic pair to the explicit
rank-two biquaternion hermitian construction.

It constructs the reduced trace through the tower

* presented quaternion algebras;
* their biquaternion tensor product;
* the degree-eight matrix algebra `M₂(Q ⊗ Q')`;
* the transported adjoint algebra attached to a hermitian Gram matrix.

The trace is proved invariant under the hermitian adjoint involution. Over a
field of characteristic different from two, one half of this trace therefore
defines the canonical semitrace on the self-adjoint subspace.

This is genuine object-level infrastructure, not an effectivity axiom. It
still does **not** prove that the involution is of orthogonal type, construct a
characteristic-two semitrace, or calculate the two Clifford components.
-/

namespace RiemannResearch.E7.QuaternionHermitian

universe u v

section QuaternionTrace

variable {k : Type u} [CommRing k]

/-- Reduced trace on Mathlib's uniform quaternion presentation. -/
def presentedQuaternionReducedTrace (p : QuaternionParameters k) :
    PresentedQuaternion p →ₗ[k] k where
  toFun x := 2 * x.re + p.c₂ * x.imI
  map_add' x y := by simp; ring
  map_smul' r x := by simp; ring

@[simp] theorem presentedQuaternionReducedTrace_apply
    (p : QuaternionParameters k) (x : PresentedQuaternion p) :
    presentedQuaternionReducedTrace p x =
      2 * x.re + p.c₂ * x.imI := rfl

@[simp] theorem presentedQuaternionReducedTrace_star
    (p : QuaternionParameters k) (x : PresentedQuaternion p) :
    presentedQuaternionReducedTrace p (star x) =
      presentedQuaternionReducedTrace p x := by
  change 2 * (x.re + p.c₂ * x.imI) + p.c₂ * (-x.imI) =
    2 * x.re + p.c₂ * x.imI
  ring

@[simp] theorem presentedQuaternionReducedTrace_one
    (p : QuaternionParameters k) :
    presentedQuaternionReducedTrace p 1 = 2 := by
  simp [presentedQuaternionReducedTrace]

/-- The reduced trace is cyclic on a presented quaternion algebra. -/
@[simp] theorem presentedQuaternionReducedTrace_mul_comm
    (p : QuaternionParameters k) (x y : PresentedQuaternion p) :
    presentedQuaternionReducedTrace p (x * y) =
      presentedQuaternionReducedTrace p (y * x) := by
  simp [presentedQuaternionReducedTrace]
  ring

end QuaternionTrace

section BiquaternionTrace

variable {k : Type u} [CommRing k]

/-- Reduced trace on a biquaternion tensor product. -/
def biquaternionReducedTrace (p q : QuaternionParameters k) :
    Biquaternion p q →ₗ[k] k :=
  TensorProduct.lift
    { toFun := fun x =>
        { toFun := fun y =>
            presentedQuaternionReducedTrace p x *
              presentedQuaternionReducedTrace q y
          map_add' := by intro y z; simp; ring
          map_smul' := by intro r y; simp; ring }
      map_add' := by intro x y; ext z; simp; ring
      map_smul' := by intro r x; ext y; simp; ring }

@[simp] theorem biquaternionReducedTrace_tmul
    (p q : QuaternionParameters k)
    (x : PresentedQuaternion p) (y : PresentedQuaternion q) :
    biquaternionReducedTrace p q (x ⊗ₜ[k] y) =
      presentedQuaternionReducedTrace p x *
        presentedQuaternionReducedTrace q y := by
  simp [biquaternionReducedTrace]

/-- The reduced trace is cyclic on a biquaternion algebra. -/
@[simp] theorem biquaternionReducedTrace_mul_comm
    (p q : QuaternionParameters k) (x y : Biquaternion p q) :
    biquaternionReducedTrace p q (x * y) =
      biquaternionReducedTrace p q (y * x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x z hx hz => simp [add_mul, mul_add, hx, hz]
  | tmul a b =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y z hy hz => simp [mul_add, add_mul, hy, hz]
      | tmul c d =>
          rw [Algebra.TensorProduct.tmul_mul_tmul,
            Algebra.TensorProduct.tmul_mul_tmul]
          simp only [biquaternionReducedTrace_tmul]
          rw [presentedQuaternionReducedTrace_mul_comm p a c,
            presentedQuaternionReducedTrace_mul_comm q b d]

section Star

variable [StarRing k] [TrivialStar k]

@[simp] theorem biquaternionReducedTrace_star
    (p q : QuaternionParameters k) (x : Biquaternion p q) :
    biquaternionReducedTrace p q (star x) =
      biquaternionReducedTrace p q x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      rw [TensorProduct.star_tmul]
      simp only [biquaternionReducedTrace_tmul]
      rw [presentedQuaternionReducedTrace_star,
        presentedQuaternionReducedTrace_star]
  | add x y hx hy => simp [hx, hy]

end Star
end BiquaternionTrace

section DegreeEightTrace

variable {k : Type u} [CommRing k]

/-- Reduced trace of the degree-eight matrix algebra `M₂(Q ⊗ Q')`. -/
def degreeEightReducedTrace (p q : QuaternionParameters k) :
    DegreeEightAlgebra p q →ₗ[k] k :=
  (biquaternionReducedTrace p q).comp
    (Matrix.traceLinearMap (Fin 2) k (Biquaternion p q))

@[simp] theorem degreeEightReducedTrace_apply
    (p q : QuaternionParameters k) (X : DegreeEightAlgebra p q) :
    degreeEightReducedTrace p q X =
      biquaternionReducedTrace p q (X 0 0) +
      biquaternionReducedTrace p q (X 1 1) := by
  simp [degreeEightReducedTrace, Matrix.trace, Fin.sum_univ_two]

/-- The reduced trace is cyclic on the degree-eight matrix algebra. -/
@[simp] theorem degreeEightReducedTrace_mul_comm
    (p q : QuaternionParameters k) (X Y : DegreeEightAlgebra p q) :
    degreeEightReducedTrace p q (X * Y) =
      degreeEightReducedTrace p q (Y * X) := by
  simp [degreeEightReducedTrace_apply, Matrix.mul_apply, Fin.sum_univ_two]
  rw [biquaternionReducedTrace_mul_comm p q (X 0 1) (Y 1 0)]
  rw [biquaternionReducedTrace_mul_comm p q (X 1 0) (Y 0 1)]
  ac_rfl

section Star
variable [StarRing k] [TrivialStar k]

@[simp] theorem degreeEightReducedTrace_star
    (p q : QuaternionParameters k) (X : DegreeEightAlgebra p q) :
    degreeEightReducedTrace p q (star X) =
      degreeEightReducedTrace p q X := by
  simp [degreeEightReducedTrace_apply]

/-- The reduced trace is invariant under every hermitian adjoint involution. -/
@[simp] theorem degreeEightReducedTrace_adjoint
    (p q : QuaternionParameters k) (G : DegreeEightHermitianGram p q)
    (X : DegreeEightAlgebra p q) :
    degreeEightReducedTrace p q (G.adjoint X) =
      degreeEightReducedTrace p q X := by
  calc
    degreeEightReducedTrace p q (G.adjoint X) =
        degreeEightReducedTrace p q ((G.inverse * star X) * G.matrix) := by
          rfl
    _ = degreeEightReducedTrace p q (G.matrix * (G.inverse * star X)) :=
      degreeEightReducedTrace_mul_comm p q _ _
    _ = degreeEightReducedTrace p q ((G.matrix * G.inverse) * star X) := by
      rw [mul_assoc]
    _ = degreeEightReducedTrace p q (star X) := by
      rw [G.matrix_mul_inverse, one_mul]
    _ = degreeEightReducedTrace p q X := degreeEightReducedTrace_star p q X

end Star
end DegreeEightTrace

section AdjointTrace

variable {k : Type u} [CommRing k] [StarRing k] [TrivialStar k]

/-- Reduced trace transported to the packaged adjoint algebra. -/
noncomputable def degreeEightAdjointReducedTrace
    (p q : QuaternionParameters k) (G : DegreeEightHermitianGram p q) :
    DegreeEightAdjointAlgebra p q G →ₗ[k] k :=
  (degreeEightReducedTrace p q).comp
    (AdjointAlgebra.algEquiv (G := G) (R := k)).toLinearMap

@[simp] theorem degreeEightAdjointReducedTrace_apply
    (p q : QuaternionParameters k) (G : DegreeEightHermitianGram p q)
    (x : DegreeEightAdjointAlgebra p q G) :
    degreeEightAdjointReducedTrace p q G x =
      degreeEightReducedTrace p q x.val := rfl

@[simp] theorem degreeEightAdjointReducedTrace_star
    (p q : QuaternionParameters k) (G : DegreeEightHermitianGram p q)
    (x : DegreeEightAdjointAlgebra p q G) :
    degreeEightAdjointReducedTrace p q G (star x) =
      degreeEightAdjointReducedTrace p q G x := by
  change degreeEightReducedTrace p q (G.adjoint x.val) =
    degreeEightReducedTrace p q x.val
  exact degreeEightReducedTrace_adjoint p q G x.val

@[simp] theorem degreeEightAdjointReducedTrace_mul_comm
    (p q : QuaternionParameters k) (G : DegreeEightHermitianGram p q)
    (x y : DegreeEightAdjointAlgebra p q G) :
    degreeEightAdjointReducedTrace p q G (x * y) =
      degreeEightAdjointReducedTrace p q G (y * x) := by
  change degreeEightReducedTrace p q (x.val * y.val) =
    degreeEightReducedTrace p q (y.val * x.val)
  exact degreeEightReducedTrace_mul_comm p q x.val y.val

end AdjointTrace

section SemiTrace

variable {k : Type u} [Field k] [StarRing k] [TrivialStar k]
variable {A : Type v} [Ring A] [Algebra k A] [StarRing A] [StarModule k A]

/-- Self-adjoint elements as a linear subspace. -/
def symmetricSubmodule : Submodule k A where
  carrier := {x | star x = x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change star (x + y) = x + y
    rw [star_add, hx, hy]
  smul_mem' := by
    intro r x hx
    change star (r • x) = r • x
    rw [StarModule.star_smul, TrivialStar.star_trivial, hx]

@[simp] theorem mem_symmetricSubmodule_iff (x : A) :
    x ∈ symmetricSubmodule (k := k) (A := A) ↔ star x = x := Iff.rfl

/-- The canonical self-adjoint symmetrization `x + x⋆`. -/
def symmetrization (x : A) : symmetricSubmodule (k := k) (A := A) :=
  ⟨x + star x, by
    change star (x + star x) = x + star x
    rw [star_add, star_star]
    exact add_comm _ _⟩

@[simp] theorem symmetrization_val (x : A) :
    (symmetrization (k := k) x : A) = x + star x := rfl

/-- A linear semitrace relative to a chosen reduced-trace map. -/
structure LinearSemiTrace (trace : A →ₗ[k] k) where
  toLinearMap : symmetricSubmodule (k := k) (A := A) →ₗ[k] k
  symmetrization_apply : ∀ x : A,
    toLinearMap (symmetrization (k := k) x) = trace x

namespace LinearSemiTrace

/-- Away from characteristic two, one half of reduced trace is canonical. -/
noncomputable def canonical
    (trace : A →ₗ[k] k)
    (trace_star : ∀ x : A, trace (star x) = trace x)
    [NeZero (2 : k)] : LinearSemiTrace trace where
  toLinearMap :=
    ((2 : k)⁻¹ • trace).comp
      (symmetricSubmodule (k := k) (A := A)).subtype
  symmetrization_apply x := by
    change (2 : k)⁻¹ * trace (x + star x) = trace x
    rw [map_add, trace_star]
    calc
      (2 : k)⁻¹ * (trace x + trace x) =
          (2 : k)⁻¹ * ((2 : k) * trace x) := by ring
      _ = ((2 : k)⁻¹ * (2 : k)) * trace x := by rw [mul_assoc]
      _ = trace x := by
        rw [inv_mul_cancel₀ (NeZero.ne (2 : k)), one_mul]

@[simp] theorem canonical_apply
    (trace : A →ₗ[k] k)
    (trace_star : ∀ x : A, trace (star x) = trace x)
    [NeZero (2 : k)]
    (s : symmetricSubmodule (k := k) (A := A)) :
    (canonical trace trace_star).toLinearMap s =
      (2 : k)⁻¹ * trace s.1 := by
  rfl

end LinearSemiTrace
end SemiTrace

section DegreeEightSemiTrace

variable {k : Type u} [Field k] [StarRing k] [TrivialStar k]

/-- Canonical semitrace on a degree-eight hermitian adjoint algebra. -/
noncomputable def degreeEightAdjointSemiTrace
    (p q : QuaternionParameters k) (G : DegreeEightHermitianGram p q)
    [NeZero (2 : k)] :
    LinearSemiTrace (degreeEightAdjointReducedTrace p q G) :=
  LinearSemiTrace.canonical
    (degreeEightAdjointReducedTrace p q G)
    (degreeEightAdjointReducedTrace_star p q G)

@[simp] theorem degreeEightAdjointSemiTrace_symmetrization
    (p q : QuaternionParameters k) (G : DegreeEightHermitianGram p q)
    [NeZero (2 : k)] (x : DegreeEightAdjointAlgebra p q G) :
    (degreeEightAdjointSemiTrace p q G).toLinearMap
        (symmetrization (k := k) x) =
      degreeEightAdjointReducedTrace p q G x :=
  (degreeEightAdjointSemiTrace p q G).symmetrization_apply x

end DegreeEightSemiTrace

end RiemannResearch.E7.QuaternionHermitian
