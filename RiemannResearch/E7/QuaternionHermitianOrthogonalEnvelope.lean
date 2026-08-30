/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E7.QuaternionHermitianBiquaternionSymmetry

/-!
# The verified orthogonal envelope of the E7 hermitian construction

This file packages the object-level facts already proved for a rank-two
hermitian form over a biquaternion algebra:

* the underlying algebra has dimension `64`;
* its adjoint involution has a `36`-dimensional self-adjoint subspace;
* the reduced trace has degree-eight normalization, is cyclic, and is
  invariant under the involution; and
* away from characteristic two, one half of reduced trace is a semitrace.

These are precisely the trace and dimension parts of a degree-eight
orthogonal quadratic pair.  The name `OrthogonalEnvelope` is deliberate: the
present development has not yet formalized central simplicity, the
discriminant, or the generalized Clifford algebra of an algebra with
quadratic pair.  In particular, this file does not identify the two Clifford
components and does not prove the E7 packet-effectivity theorem.
-/

namespace RiemannResearch.E7.QuaternionHermitian

universe u v

/-- Verified finite-dimensional, trace, semitrace, and fixed-space data for a
degree-eight involutive algebra.  This is not declared to be a full central
simple algebra with quadratic pair until the missing CSA and Clifford layers
are supplied. -/
structure DegreeEightOrthogonalEnvelope
    (k : Type u) (A : Type v)
    [Field k] [StarRing k] [TrivialStar k]
    [Ring A] [Algebra k A] [StarRing A] [StarModule k A] where
  reducedTrace : A →ₗ[k] k
  reducedTrace_one : reducedTrace 1 = 8
  reducedTrace_star : ∀ x : A, reducedTrace (star x) = reducedTrace x
  reducedTrace_mul_comm : ∀ x y : A,
    reducedTrace (x * y) = reducedTrace (y * x)
  semiTrace : LinearSemiTrace reducedTrace
  algebra_finrank : Module.finrank k A = 64
  symmetric_finrank :
    Module.finrank k (symmetricSubmodule (k := k) (A := A)) = 36

section TraceNormalization

variable {k : Type u} [Field k]

/-- The reduced trace of the identity of a biquaternion algebra is four. -/
@[simp] theorem biquaternionReducedTrace_one
    (p q : QuaternionParameters k) :
    biquaternionReducedTrace p q 1 = 4 := by
  rw [Algebra.TensorProduct.one_def]
  simp
  norm_num

end TraceNormalization

section AdjointEnvelope

variable {k : Type u} [Field k] [StarRing k] [TrivialStar k]

/-- The reduced trace of the identity in the degree-eight adjoint algebra is
eight. -/
@[simp] theorem degreeEightAdjointReducedTrace_one
    (p q : QuaternionParameters k)
    (G : DegreeEightHermitianGram p q) :
    degreeEightAdjointReducedTrace p q G 1 = 8 := by
  change degreeEightReducedTrace p q (1 : DegreeEightAlgebra p q) = 8
  rw [degreeEightReducedTrace_apply]
  simp only [Matrix.one_apply, Fin.isValue, if_true]
  rw [biquaternionReducedTrace_one]
  norm_num

/-- Every rank-two hermitian adjoint over a presented biquaternion algebra
provides the verified degree-eight orthogonal envelope. -/
noncomputable def degreeEightOrthogonalEnvelope
    (p q : QuaternionParameters k) [NeZero (2 : k)]
    (G : DegreeEightHermitianGram p q) :
    DegreeEightOrthogonalEnvelope k (DegreeEightAdjointAlgebra p q G) where
  reducedTrace := degreeEightAdjointReducedTrace p q G
  reducedTrace_one := degreeEightAdjointReducedTrace_one p q G
  reducedTrace_star := degreeEightAdjointReducedTrace_star p q G
  reducedTrace_mul_comm := degreeEightAdjointReducedTrace_mul_comm p q G
  semiTrace := degreeEightAdjointSemiTrace p q G
  algebra_finrank := degreeEightAdjointAlgebra_finrank p q G
  symmetric_finrank := degreeEightAdjointSymmetric_finrank p q G

@[simp] theorem degreeEightOrthogonalEnvelope_reducedTrace
    (p q : QuaternionParameters k) [NeZero (2 : k)]
    (G : DegreeEightHermitianGram p q) :
    (degreeEightOrthogonalEnvelope p q G).reducedTrace =
      degreeEightAdjointReducedTrace p q G := rfl

@[simp] theorem degreeEightOrthogonalEnvelope_semiTrace
    (p q : QuaternionParameters k) [NeZero (2 : k)]
    (G : DegreeEightHermitianGram p q) :
    (degreeEightOrthogonalEnvelope p q G).semiTrace =
      degreeEightAdjointSemiTrace p q G := rfl

end AdjointEnvelope

end RiemannResearch.E7.QuaternionHermitian
