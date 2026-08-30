/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E7.QuaternionHermitianCentralSimpleOrthogonalPair

/-!
# Quadratic-pair conditions for the E7 hermitian construction

This file upgrades the explicit degree-eight central-simple orthogonal pair to
the characteristic-different-from-two quadratic-pair defining conditions.

The already verified semitrace satisfies

`f(x + x⋆) = Trd(x)`,

and the symmetric subspace has dimension `36 = 8 * 9 / 2`.  The remaining
condition needed at this layer is that the reduced trace vanishes on skew-adjoint
elements.  This follows formally from invariance of reduced trace under the
involution and invertibility of `2`.

The concrete constructor is still not the full E7 packet-effectivity theorem:
the discriminant and the two generalized Clifford components have not yet
been calculated, and the present construction is restricted to
characteristic different from two.
-/

namespace RiemannResearch.E7.QuaternionHermitian

universe u v

section SkewSubmodule

variable {k : Type u} [Field k] [StarRing k] [TrivialStar k]
variable {A : Type v} [Ring A] [Algebra k A] [StarRing A] [StarModule k A]

/-- Skew-adjoint elements as a linear subspace. -/
def skewSubmodule : Submodule k A where
  carrier := {x | star x = -x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change star (x + y) = -(x + y)
    rw [star_add, hx, hy, neg_add_rev]
    exact add_comm _ _
  smul_mem' := by
    intro r x hx
    change star (r • x) = -(r • x)
    rw [StarModule.star_smul, TrivialStar.star_trivial, hx]
    exact smul_neg r x

@[simp] theorem mem_skewSubmodule_iff (x : A) :
    x ∈ skewSubmodule (k := k) (A := A) ↔ star x = -x := Iff.rfl

/-- A trace invariant under the involution vanishes on skew-adjoint elements
when `2` is invertible. -/
theorem trace_eq_zero_of_star_eq_neg
    (trace : A →ₗ[k] k)
    (trace_star : ∀ x : A, trace (star x) = trace x)
    [NeZero (2 : k)]
    (x : A) (hx : star x = -x) : trace x = 0 := by
  have hneg : trace x = -trace x := by
    calc
      trace x = trace (star x) := (trace_star x).symm
      _ = trace (-x) := by rw [hx]
      _ = -trace x := map_neg trace x
  have hsum : trace x + trace x = 0 := by
    calc
      trace x + trace x = trace x + (-trace x) :=
        congrArg (fun z : k => trace x + z) hneg
      _ = 0 := add_neg_cancel (trace x)
  have hmul : (2 : k) * trace x = 0 := by
    simpa [two_mul] using hsum
  exact (mul_eq_zero.mp hmul).resolve_left (NeZero.ne (2 : k))

end SkewSubmodule

/-- The exact degree-eight quadratic-pair conditions available from the concrete
hermitian construction in characteristic different from two.

The inherited data include central simplicity, the adjoint involution,
reduced trace, semitrace, algebra dimension `64`, symmetric dimension `36`,
trace normalization, trace invariance, and trace cyclicity. -/
structure DegreeEightQuadraticPair
    (k : Type u) (A : Type v)
    [Field k] [StarRing k] [TrivialStar k]
    [Ring A] [Algebra k A] [StarRing A] [StarModule k A]
    extends DegreeEightCentralSimpleOrthogonalPair k A where
  reducedTrace_skew :
    ∀ x : A, star x = -x → reducedTrace x = 0

namespace DegreeEightQuadraticPair

variable {k : Type u} [Field k] [StarRing k] [TrivialStar k]
variable {A : Type v} [Ring A] [Algebra k A] [StarRing A] [StarModule k A]

/-- The quadratic-pair semitrace condition, exposed directly from the inherited
`LinearSemiTrace`. -/
@[simp] theorem semiTrace_symmetrization
    (P : DegreeEightQuadraticPair k A) (x : A) :
    P.semiTrace.toLinearMap (symmetrization (k := k) x) =
      P.reducedTrace x :=
  P.semiTrace.symmetrization_apply x

/-- Reduced trace vanishes on the skew-adjoint submodule. -/
@[simp] theorem reducedTrace_skewSubmodule
    (P : DegreeEightQuadraticPair k A)
    (x : skewSubmodule (k := k) (A := A)) :
    P.reducedTrace x = 0 :=
  P.reducedTrace_skew x x.property

end DegreeEightQuadraticPair

namespace DegreeEightCentralSimpleOrthogonalPair

variable {k : Type u} [Field k] [StarRing k] [TrivialStar k]
variable {A : Type v} [Ring A] [Algebra k A] [StarRing A] [StarModule k A]

/-- Every verified central-simple orthogonal pair in characteristic different
from two satisfies the remaining skew-trace condition. -/
noncomputable def toQuadraticPair [NeZero (2 : k)]
    (P : DegreeEightCentralSimpleOrthogonalPair k A) :
    DegreeEightQuadraticPair k A where
  toDegreeEightCentralSimpleOrthogonalPair := P
  reducedTrace_skew x hx :=
    trace_eq_zero_of_star_eq_neg P.reducedTrace P.reducedTrace_star x hx

end DegreeEightCentralSimpleOrthogonalPair

section Concrete

variable {k : Type u} [Field k] [StarRing k] [TrivialStar k]

/-- The concrete degree-eight quadratic pair attached to the diagonal
hermitian Gram matrix `diag(1, j ⊗ j')`. -/
noncomputable def canonicalDegreeEightQuadraticPair
    (p q : QuaternionParameters k) [NeZero (2 : k)]
    (hp₃ : p.c₃ ≠ 0) (hpdisc : 4 * p.c₁ + p.c₂ ^ 2 ≠ 0)
    (hq₃ : q.c₃ ≠ 0) (hqdisc : 4 * q.c₁ + q.c₂ ^ 2 ≠ 0) :
    DegreeEightQuadraticPair k
      (DegreeEightAdjointAlgebra p q
        (canonicalDegreeEightGram p q hp₃ hq₃)) :=
  (canonicalDegreeEightCentralSimpleOrthogonalPair
    p q hp₃ hpdisc hq₃ hqdisc).toQuadraticPair

end Concrete

end RiemannResearch.E7.QuaternionHermitian
