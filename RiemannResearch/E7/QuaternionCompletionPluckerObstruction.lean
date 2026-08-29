/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.Tactic.Ring

/-!
# A Plücker obstruction to the four-quaternion completion route

The exponent-two bookkeeping in `QuaternionTrialityPacket` isolates a
four-quaternion orthogonal-sum construction as a sufficient route to the
remaining E7 bridge.  That route asks for one symbol `r` such that the four
classes

* `r`,
* `r + e₁₂`,
* `r + e₃₄`, and
* `r + e₁₂ + e₃₄`

are all symbols.

At the level of decomposable bivectors in dimension four, this is impossible.
Writing a bivector in coordinates

`(a₁₂,a₁₃,a₁₄,a₂₃,a₂₄,a₃₄)`,

the Plücker equation is

`a₁₂*a₃₄ - a₁₃*a₂₄ + a₁₄*a₂₃ = 0`.

The mixed finite difference of this polynomial in the `e₁₂` and `e₃₄`
directions is exactly `1`. Hence the four shifted bivectors cannot all
satisfy the Plücker equation over a nontrivial commutative ring.

This does not produce a counterexample to Gille's E7 realization problem:
it proves only that the particular simultaneous-symbol-factor strengthening
is not a formal consequence of symbol arithmetic and must not be used as the
main E7 bridge.
-/

namespace RiemannResearch.E7.QuaternionCompletionPluckerObstruction

universe u

variable {R : Type u} [CommRing R] [Nontrivial R]

/-- The single Plücker polynomial for a bivector in rank four. -/
def plucker
    (a₁₂ a₁₃ a₁₄ a₂₃ a₂₄ a₃₄ : R) : R :=
  a₁₂ * a₃₄ - a₁₃ * a₂₄ + a₁₄ * a₂₃

/-- The mixed finite difference of the rank-four Plücker polynomial in the
`e₁₂` and `e₃₄` directions is one. -/
theorem plucker_mixed_difference
    (a₁₂ a₁₃ a₁₄ a₂₃ a₂₄ a₃₄ : R) :
    plucker (a₁₂ + 1) a₁₃ a₁₄ a₂₃ a₂₄ (a₃₄ + 1)
        - plucker (a₁₂ + 1) a₁₃ a₁₄ a₂₃ a₂₄ a₃₄
        - plucker a₁₂ a₁₃ a₁₄ a₂₃ a₂₄ (a₃₄ + 1)
        + plucker a₁₂ a₁₃ a₁₄ a₂₃ a₂₄ a₃₄ = 1 := by
  simp only [plucker]
  ring

/-- No bivector and its three shifts by `e₁₂`, `e₃₄`, and
`e₁₂ + e₃₄` can all satisfy the Plücker equation. -/
theorem no_four_plucker_zero_shifts
    (a₁₂ a₁₃ a₁₄ a₂₃ a₂₄ a₃₄ : R)
    (h₀ : plucker a₁₂ a₁₃ a₁₄ a₂₃ a₂₄ a₃₄ = 0)
    (h₁₂ : plucker (a₁₂ + 1) a₁₃ a₁₄ a₂₃ a₂₄ a₃₄ = 0)
    (h₃₄ : plucker a₁₂ a₁₃ a₁₄ a₂₃ a₂₄ (a₃₄ + 1) = 0)
    (h₁₂₃₄ :
      plucker (a₁₂ + 1) a₁₃ a₁₄ a₂₃ a₂₄ (a₃₄ + 1) = 0) :
    False := by
  have hOne : (1 : R) = 0 := by
    rw [← plucker_mixed_difference
      a₁₂ a₁₃ a₁₄ a₂₃ a₂₄ a₃₄,
      h₁₂₃₄, h₁₂, h₃₄, h₀]
    ring
  exact one_ne_zero hOne

/-- Existential form of the obstruction, suitable for importing into a
symbol-completion interface. -/
theorem not_exists_four_plucker_zero_shifts
    (a₁₃ a₁₄ a₂₃ a₂₄ : R) :
    ¬ ∃ a₁₂ a₃₄ : R,
      plucker a₁₂ a₁₃ a₁₄ a₂₃ a₂₄ a₃₄ = 0 ∧
      plucker (a₁₂ + 1) a₁₃ a₁₄ a₂₃ a₂₄ a₃₄ = 0 ∧
      plucker a₁₂ a₁₃ a₁₄ a₂₃ a₂₄ (a₃₄ + 1) = 0 ∧
      plucker (a₁₂ + 1) a₁₃ a₁₄ a₂₃ a₂₄ (a₃₄ + 1) = 0 := by
  rintro ⟨a₁₂, a₃₄, h₀, h₁₂, h₃₄, h₁₂₃₄⟩
  exact no_four_plucker_zero_shifts
    a₁₂ a₁₃ a₁₄ a₂₃ a₂₄ a₃₄ h₀ h₁₂ h₃₄ h₁₂₃₄

end RiemannResearch.E7.QuaternionCompletionPluckerObstruction
