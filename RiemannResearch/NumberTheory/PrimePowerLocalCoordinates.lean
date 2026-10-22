import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring

/-!
Source: user-provided handoff Sections 3--4 for the coefficients and twist.
The first three positive-degree coefficients of the formal local exponential
and logarithm. These are finite polynomial identities only; no infinite
Dirichlet-series or formal-power-series identity is asserted here.
-/

namespace PrimePowerLocalDegreeThree

variable {K : Type*} [Field K] [CharZero K]

def localExp3 (h : K × K × K) : K × K × K :=
  (h.1, h.2.1 + h.1 ^ 2 / 2,
    h.2.2 + h.1 * h.2.1 + h.1 ^ 3 / 6)

def localLog3 (f : K × K × K) : K × K × K :=
  (f.1, f.2.1 - f.1 ^ 2 / 2,
    f.2.2 - f.1 * f.2.1 + f.1 ^ 3 / 3)

theorem localLog3_localExp3 (h : K × K × K) :
    localLog3 (localExp3 h) = h := by
  apply Prod.ext
  · rfl
  · apply Prod.ext <;> dsimp [localLog3, localExp3] <;> ring

theorem localExp3_localLog3 (f : K × K × K) :
    localExp3 (localLog3 f) = f := by
  apply Prod.ext
  · rfl
  · apply Prod.ext <;> dsimp [localLog3, localExp3] <;> ring

def localExpLogEquiv3 : (K × K × K) ≃ (K × K × K) where
  toFun := localExp3
  invFun := localLog3
  left_inv := localLog3_localExp3
  right_inv := localExp3_localLog3

theorem geometric_localLog3 (alpha : K) :
    localLog3 (alpha, alpha ^ 2, alpha ^ 3) =
      (alpha, alpha ^ 2 / 2, alpha ^ 3 / 3) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext <;> dsimp [localLog3] <;> ring

theorem geometric_localExp3 (alpha : K) :
    localExp3 (alpha, alpha ^ 2 / 2, alpha ^ 3 / 3) =
      (alpha, alpha ^ 2, alpha ^ 3) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext <;> dsimp [localExp3] <;> ring

/-- A completely multiplicative twist acts with prime-power degree weights. -/
def localTwist3 (alpha : K) (h : K × K × K) : K × K × K :=
  (alpha * h.1, alpha ^ 2 * h.2.1, alpha ^ 3 * h.2.2)

theorem localExp3_twist (alpha : K) (h : K × K × K) :
    localExp3 (localTwist3 alpha h) = localTwist3 alpha (localExp3 h) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext <;> dsimp [localExp3, localTwist3] <;> ring

theorem localLog3_twist (alpha : K) (f : K × K × K) :
    localLog3 (localTwist3 alpha f) = localTwist3 alpha (localLog3 f) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext <;> dsimp [localLog3, localTwist3] <;> ring

end PrimePowerLocalDegreeThree
