/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E7.QuaternionHermitianCentralSimpleTransfer

/-!
# Central-simple orthogonal pairs at the E7 index-eight boundary

This file combines the two object-level halves of the rank-two hermitian
construction:

* `QuaternionHermitianOrthogonalEnvelope` supplies the involution, reduced
  trace, semitrace, dimension `64`, and symmetric dimension `36`;
* `QuaternionHermitianCentralSimpleTransfer` supplies central simplicity.

Over a field of characteristic different from two, the resulting structure is
the verified central-simple orthogonal-pair layer of the desired degree-eight
quadratic pair.  The construction is instantiated both for an arbitrary
rank-two hermitian Gram datum and for the concrete diagonal Gram matrix
`diag(1, j ⊗ j')`.

No discriminant or generalized Clifford-component calculation is asserted in
this file.  Those remain the next genuine E7 effectivity obligations.
-/

namespace RiemannResearch.E7.QuaternionHermitian

universe u v

/-- A degree-eight central simple algebra equipped with the verified
orthogonal involution, reduced trace, and semitrace data.  In characteristic
different from two this is the object-level quadratic-pair layer, before the
discriminant and Clifford components are calculated. -/
structure DegreeEightCentralSimpleOrthogonalPair
    (k : Type u) (A : Type v)
    [Field k] [StarRing k] [TrivialStar k]
    [Ring A] [Algebra k A] [StarRing A] [StarModule k A]
    extends DegreeEightOrthogonalEnvelope k A where
  isCentral : Algebra.IsCentral k A
  isSimple : IsSimpleRing A
  finiteDimensional : FiniteDimensional k A

section DegreeEight

variable {k : Type u} [Field k] [StarRing k] [TrivialStar k]

/-- Package an arbitrary rank-two hermitian adjoint algebra once central
simplicity of its biquaternion coefficient algebra is available. -/
noncomputable def degreeEightCentralSimpleOrthogonalPair
    (p q : QuaternionParameters k) [NeZero (2 : k)]
    (G : DegreeEightHermitianGram p q)
    [Algebra.IsCentral k (Biquaternion p q)]
    [IsSimpleRing (Biquaternion p q)] :
    DegreeEightCentralSimpleOrthogonalPair k
      (DegreeEightAdjointAlgebra p q G) where
  toDegreeEightOrthogonalEnvelope := degreeEightOrthogonalEnvelope p q G
  isCentral := degreeEightAdjointAlgebra_isCentral p q G
  isSimple := degreeEightAdjointAlgebra_isSimpleRing p q G
  finiteDimensional := degreeEightAdjointAlgebra_finiteDimensional p q G

/-- The central-simple orthogonal pair obtained directly from two
nondegenerate quaternion presentations and any rank-two hermitian Gram
datum. -/
noncomputable def degreeEightCentralSimpleOrthogonalPair_of_nondegenerate
    (p q : QuaternionParameters k) [NeZero (2 : k)]
    (G : DegreeEightHermitianGram p q)
    (hp₃ : p.c₃ ≠ 0) (hpdisc : 4 * p.c₁ + p.c₂ ^ 2 ≠ 0)
    (hq₃ : q.c₃ ≠ 0) (hqdisc : 4 * q.c₁ + q.c₂ ^ 2 ≠ 0) :
    DegreeEightCentralSimpleOrthogonalPair k
      (DegreeEightAdjointAlgebra p q G) := by
  letI : IsAzumaya k (Biquaternion p q) :=
    QuaternionAzumaya.biquaternion_isAzumaya_of_nondegenerate
      p q hp₃ hpdisc hq₃ hqdisc
  letI : IsSimpleRing (Biquaternion p q) :=
    RiemannResearch.IsAzumaya.isSimpleRing_of_field k (Biquaternion p q)
  exact degreeEightCentralSimpleOrthogonalPair p q G

/-- The concrete Gram matrix `diag(1, j ⊗ j')` determined by two nonzero
quaternion `j²` parameters. -/
noncomputable def canonicalDegreeEightGram
    (p q : QuaternionParameters k)
    (hp₃ : p.c₃ ≠ 0) (hq₃ : q.c₃ ≠ 0) :
    DegreeEightHermitianGram p q :=
  jTensorDegreeEightGram p q
    (JUnitData.ofIsUnit p (isUnit_iff_ne_zero.mpr hp₃))
    (JUnitData.ofIsUnit q (isUnit_iff_ne_zero.mpr hq₃))

@[simp] theorem canonicalDegreeEightGram_matrix
    (p q : QuaternionParameters k)
    (hp₃ : p.c₃ ≠ 0) (hq₃ : q.c₃ ≠ 0) :
    (canonicalDegreeEightGram p q hp₃ hq₃).matrix =
      Matrix.diagonal
        ![1, PresentedQuaternion.j p ⊗ₜ[k] PresentedQuaternion.j q] := by
  simp [canonicalDegreeEightGram]

/-- The fully explicit degree-eight central-simple orthogonal pair built from
two nondegenerate quaternion presentations. -/
noncomputable def canonicalDegreeEightCentralSimpleOrthogonalPair
    (p q : QuaternionParameters k) [NeZero (2 : k)]
    (hp₃ : p.c₃ ≠ 0) (hpdisc : 4 * p.c₁ + p.c₂ ^ 2 ≠ 0)
    (hq₃ : q.c₃ ≠ 0) (hqdisc : 4 * q.c₁ + q.c₂ ^ 2 ≠ 0) :
    DegreeEightCentralSimpleOrthogonalPair k
      (DegreeEightAdjointAlgebra p q
        (canonicalDegreeEightGram p q hp₃ hq₃)) :=
  degreeEightCentralSimpleOrthogonalPair_of_nondegenerate
    p q (canonicalDegreeEightGram p q hp₃ hq₃)
    hp₃ hpdisc hq₃ hqdisc

end DegreeEight

end RiemannResearch.E7.QuaternionHermitian
