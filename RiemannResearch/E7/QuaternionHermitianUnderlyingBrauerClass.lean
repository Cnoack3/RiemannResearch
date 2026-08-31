/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E7.QuaternionHermitianCentralSimpleTransfer
import Mathlib.Tactic

/-!
# The underlying Brauer class of the E7 hermitian adjoint algebra

The rank-two hermitian construction has underlying algebra

`End_D(D²) = M₂(D)`,

where `D = Q ⊗ Q'` is biquaternion.  This file records that identity at
Mathlib's actual central-simple-algebra and Brauer-equivalence levels.

For every hermitian Gram datum `G`, it proves

`M₁(AdjointAlgebra G) ≃ₐ[k] M₂(D)`

and therefore identifies the Brauer class of the degree-eight adjoint algebra
with the Brauer class of `D`.  The result is also specialized to the explicit
nondegenerate quaternion presentations used by the E7 construction.

This verifies the **underlying** entry of the desired trialitarian packet by
an actual algebra equivalence.  It does not calculate the discriminant or the
two generalized Clifford components, so it does not by itself establish E7
boundary effectivity.
-/

namespace RiemannResearch.E7.QuaternionHermitian

universe u v

/-- Evaluation at the unique matrix entry is an algebra equivalence from a
one-by-one matrix algebra to its coefficient algebra. -/
noncomputable def matrixOneAlgEquiv
    {k : Type u} [Field k]
    {A : Type v} [Ring A] [Algebra k A] :
    Matrix (Fin 1) (Fin 1) A ≃ₐ[k] A where
  toFun M := M 0 0
  invFun a := fun _ _ => a
  left_inv M := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  right_inv a := rfl
  map_add' M N := rfl
  map_mul' M N := by
    simp [Matrix.mul_apply]
  commutes' r := by
    rfl

variable {k : Type u} [Field k] [StarRing k] [TrivialStar k]

/-- The biquaternion coefficient algebra, bundled as a finite-dimensional
central simple algebra. -/
noncomputable def biquaternionCSA
    (p q : QuaternionParameters k)
    [Algebra.IsCentral k (Biquaternion p q)]
    [IsSimpleRing (Biquaternion p q)] : CSA k where
  toAlgCat := AlgCat.of k (Biquaternion p q)
  isCentral := inferInstance
  isSimple := inferInstance
  fin_dim := inferInstance

/-- An Azumaya biquaternion algebra is a central simple algebra over the base
field. -/
noncomputable def biquaternionCSA_of_isAzumaya
    (p q : QuaternionParameters k)
    [IsAzumaya k (Biquaternion p q)] : CSA k := by
  letI : IsSimpleRing (Biquaternion p q) :=
    RiemannResearch.IsAzumaya.isSimpleRing_of_field k (Biquaternion p q)
  exact biquaternionCSA p q

/-- A completely instantiated biquaternion CSA from the two verified
nondegenerate quaternion presentations. -/
noncomputable def biquaternionCSA_of_nondegenerate
    (p q : QuaternionParameters k)
    (hp₃ : p.c₃ ≠ 0) (hpdisc : 4 * p.c₁ + p.c₂ ^ 2 ≠ 0)
    (hq₃ : q.c₃ ≠ 0) (hqdisc : 4 * q.c₁ + q.c₂ ^ 2 ≠ 0) :
    CSA k := by
  letI : IsAzumaya k (Biquaternion p q) :=
    QuaternionAzumaya.biquaternion_isAzumaya_of_nondegenerate
      p q hp₃ hpdisc hq₃ hqdisc
  exact biquaternionCSA_of_isAzumaya p q

/-- The class of a central simple algebra in Mathlib's Brauer-equivalence
quotient.  Mathlib currently supplies the quotient before its group law, so
this definition uses no unproved additive Brauer-group interface. -/
noncomputable def csaBrauerClass (A : CSA k) : BrauerGroup k :=
  Quotient.mk (Brauer.CSA_Setoid k) A

/-- The degree-eight adjoint algebra is Brauer equivalent to its
biquaternion coefficient algebra.  The witnesses are `1` and `2`, and the
equivalence is the one-by-one matrix collapse followed by the already
verified adjoint-algebra equivalence. -/
theorem degreeEightAdjointCSA_brauerEquivalent_biquaternion
    (p q : QuaternionParameters k) (G : DegreeEightHermitianGram p q)
    [Algebra.IsCentral k (Biquaternion p q)]
    [IsSimpleRing (Biquaternion p q)] :
    IsBrauerEquivalent (degreeEightAdjointCSA p q G)
      (biquaternionCSA p q) := by
  refine ⟨1, 2, one_ne_zero, by norm_num, ?_⟩
  change Nonempty
    (Matrix (Fin 1) (Fin 1) (DegreeEightAdjointAlgebra p q G) ≃ₐ[k]
      Matrix (Fin 2) (Fin 2) (Biquaternion p q))
  exact
    ⟨matrixOneAlgEquiv.trans
      (AdjointAlgebra.algEquiv (G := G) (R := k))⟩

/-- Equality of the corresponding classes in Mathlib's Brauer quotient. -/
theorem degreeEightAdjointCSA_brauerClass_eq_biquaternion
    (p q : QuaternionParameters k) (G : DegreeEightHermitianGram p q)
    [Algebra.IsCentral k (Biquaternion p q)]
    [IsSimpleRing (Biquaternion p q)] :
    csaBrauerClass (degreeEightAdjointCSA p q G) =
      csaBrauerClass (biquaternionCSA p q) :=
  Quotient.sound
    (degreeEightAdjointCSA_brauerEquivalent_biquaternion p q G)

/-- The underlying-algebra Brauer equivalence with all quaternion
nondegeneracy hypotheses discharged explicitly. -/
theorem degreeEightAdjointCSA_of_nondegenerate_brauerEquivalent
    (p q : QuaternionParameters k) (G : DegreeEightHermitianGram p q)
    (hp₃ : p.c₃ ≠ 0) (hpdisc : 4 * p.c₁ + p.c₂ ^ 2 ≠ 0)
    (hq₃ : q.c₃ ≠ 0) (hqdisc : 4 * q.c₁ + q.c₂ ^ 2 ≠ 0) :
    IsBrauerEquivalent
      (degreeEightAdjointCSA_of_nondegenerate p q G
        hp₃ hpdisc hq₃ hqdisc)
      (biquaternionCSA_of_nondegenerate p q
        hp₃ hpdisc hq₃ hqdisc) := by
  refine ⟨1, 2, one_ne_zero, by norm_num, ?_⟩
  change Nonempty
    (Matrix (Fin 1) (Fin 1) (DegreeEightAdjointAlgebra p q G) ≃ₐ[k]
      Matrix (Fin 2) (Fin 2) (Biquaternion p q))
  exact
    ⟨matrixOneAlgEquiv.trans
      (AdjointAlgebra.algEquiv (G := G) (R := k))⟩

/-- The nondegenerate adjoint algebra and the explicit biquaternion CSA have
the same class in the Brauer quotient. -/
theorem degreeEightAdjointCSA_of_nondegenerate_brauerClass_eq
    (p q : QuaternionParameters k) (G : DegreeEightHermitianGram p q)
    (hp₃ : p.c₃ ≠ 0) (hpdisc : 4 * p.c₁ + p.c₂ ^ 2 ≠ 0)
    (hq₃ : q.c₃ ≠ 0) (hqdisc : 4 * q.c₁ + q.c₂ ^ 2 ≠ 0) :
    csaBrauerClass
      (degreeEightAdjointCSA_of_nondegenerate p q G
        hp₃ hpdisc hq₃ hqdisc) =
    csaBrauerClass
      (biquaternionCSA_of_nondegenerate p q
        hp₃ hpdisc hq₃ hqdisc) :=
  Quotient.sound
    (degreeEightAdjointCSA_of_nondegenerate_brauerEquivalent
      p q G hp₃ hpdisc hq₃ hqdisc)

end RiemannResearch.E7.QuaternionHermitian
