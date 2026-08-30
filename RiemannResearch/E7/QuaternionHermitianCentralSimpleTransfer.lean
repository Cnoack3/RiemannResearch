/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E7.QuaternionHermitianOrthogonalEnvelope
import RiemannResearch.Algebra.AzumayaFieldSimple
import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.Algebra.Central.Basic
import Mathlib.Algebra.Central.Matrix
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# Central-simple transfer for the E7 hermitian adjoint algebra

This file transfers centrality and simplicity from a coefficient algebra to
its finite-rank hermitian adjoint algebra. Applied to the rank-two
biquaternion construction, it packages the already verified degree-eight
adjoint algebra as a finite-dimensional central simple algebra, conditional
only on central simplicity of the biquaternion coefficient algebra.

No discriminant or Clifford-component theorem is asserted here. In
particular, this file does not yet prove the index-eight E7 effectivity bridge.
-/

namespace RiemannResearch.E7.QuaternionHermitian

universe u v w

namespace AdjointAlgebra

variable {R : Type w} [CommSemiring R]
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {A : Type v} [Ring A] [Algebra R A] [StarRing A]
variable (G : HermitianGram (ι := ι) (A := A))

/-- Centrality transfers from the coefficient algebra to a hermitian adjoint
algebra because the latter is algebra-isomorphic to a matrix algebra. -/
theorem isCentral [Algebra.IsCentral R A] :
    Algebra.IsCentral R (AdjointAlgebra G) :=
  Algebra.IsCentral.of_algEquiv R (Matrix ι ι A) (AdjointAlgebra G)
    (algEquiv (G := G) (R := R)).symm

/-- Simplicity transfers from the coefficient algebra to a nonempty finite
matrix algebra and then across the underlying ring isomorphism. -/
theorem isSimpleRing [Nonempty ι] [IsSimpleRing A] :
    IsSimpleRing (AdjointAlgebra G) :=
  IsSimpleRing.of_ringEquiv (ringEquiv G).symm inferInstance

end AdjointAlgebra

section DegreeEight

variable {k : Type u} [Field k] [StarRing k] [TrivialStar k]

/-- The degree-eight hermitian adjoint algebra is central whenever the
biquaternion coefficient algebra is central. -/
theorem degreeEightAdjointAlgebra_isCentral
    (p q : QuaternionParameters k) (G : DegreeEightHermitianGram p q)
    [Algebra.IsCentral k (Biquaternion p q)] :
    Algebra.IsCentral k (DegreeEightAdjointAlgebra p q G) :=
  AdjointAlgebra.isCentral G

/-- The degree-eight hermitian adjoint algebra is simple whenever the
biquaternion coefficient algebra is simple. -/
theorem degreeEightAdjointAlgebra_isSimpleRing
    (p q : QuaternionParameters k) (G : DegreeEightHermitianGram p q)
    [IsSimpleRing (Biquaternion p q)] :
    IsSimpleRing (DegreeEightAdjointAlgebra p q G) :=
  AdjointAlgebra.isSimpleRing G

/-- The verified finrank-64 calculation supplies finite-dimensionality of the
rank-two biquaternion adjoint algebra. -/
theorem degreeEightAdjointAlgebra_finiteDimensional
    (p q : QuaternionParameters k) (G : DegreeEightHermitianGram p q) :
    FiniteDimensional k (DegreeEightAdjointAlgebra p q G) :=
  FiniteDimensional.of_finrank_eq_succ (n := 63)
    (degreeEightAdjointAlgebra_finrank p q G)

/-- The rank-two hermitian adjoint algebra, bundled as Mathlib's type of
finite-dimensional central simple algebras. The only unresolved algebraic
input at this stage is central simplicity of the biquaternion coefficient
algebra itself. -/
noncomputable def degreeEightAdjointCSA
    (p q : QuaternionParameters k) (G : DegreeEightHermitianGram p q)
    [Algebra.IsCentral k (Biquaternion p q)]
    [IsSimpleRing (Biquaternion p q)] :
    CSA k where
  toAlgCat := AlgCat.of k (DegreeEightAdjointAlgebra p q G)
  isCentral := degreeEightAdjointAlgebra_isCentral p q G
  isSimple := degreeEightAdjointAlgebra_isSimpleRing p q G
  fin_dim := degreeEightAdjointAlgebra_finiteDimensional p q G

/-- The same degree-eight central simple algebra, obtained from the single
Azumaya hypothesis on the biquaternion coefficient algebra. Over a field,
Azumaya supplies centrality through Mathlib and simplicity through
`RiemannResearch.IsAzumaya.isSimpleRing_of_field`. -/
noncomputable def degreeEightAdjointCSA_of_isAzumaya
    (p q : QuaternionParameters k) (G : DegreeEightHermitianGram p q)
    [IsAzumaya k (Biquaternion p q)] :
    CSA k := by
  have : IsSimpleRing (Biquaternion p q) :=
    RiemannResearch.IsAzumaya.isSimpleRing_of_field k (Biquaternion p q)
  exact degreeEightAdjointCSA p q G

end DegreeEight

end RiemannResearch.E7.QuaternionHermitian
