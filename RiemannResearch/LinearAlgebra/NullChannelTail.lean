/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.LinearAlgebra.SignedChannelUpdate
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

/-!
# Null completions and exact signed head--tail identities

Source: user-provided argument,
`RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md`,
Sections 5, 7 and 9. This supplies the algebraic statements and proof strategy.

These are general Hermitian-form theorems. The hypothesis `B g = 0` is the
actual left-null condition on the sesquilinear map, not positivity and not
merely `B g g = 0`. Identifying a full arithmetic return as such a null vector
for the complete Weil form remains a separate analytic provider.

-/

open scoped ComplexConjugate

namespace LinearMap.IsSymm

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hB : B.IsSymm)

include hB

/-- A Hermitian left-null vector is also right-null. -/
theorem null_right_apply {g : V} (hg : B g = 0) (x : V) : B x g = 0 := by
  rw [← hB.eq g x]
  simp [hg]

/-- Subtracting an actual null vector preserves the full complex diagonal. -/
theorem null_sub_diagonal {g : V} (hg : B g = 0) (x : V) :
    B (x - g) (x - g) = B x x := by
  simp [map_sub, hg, hB.null_right_apply hg x]

theorem null_sub_signedValue {g : V} (hg : B g = 0) (x : V) :
    B.signedValue (x - g) = B.signedValue x := by
  exact congrArg Complex.re (hB.null_sub_diagonal hg x)

/-- The mixed term of a null completion is exactly minus its head diagonal. -/
theorem null_completion_mixed (head tail : V) (hnull : B (head + tail) = 0) :
    B head tail = -(B head head) := by
  have hz := hB.null_right_apply hnull head
  simp only [map_add] at hz
  linear_combination hz

/-- The head and tail have the same full complex diagonal value. -/
theorem null_completion_diagonal (head tail : V) (hnull : B (head + tail) = 0) :
    B tail tail = B head head := by
  have hm := hB.null_completion_mixed head tail hnull
  have hz : B (head + tail) tail = 0 := by simp [hnull]
  simp only [map_add, LinearMap.add_apply] at hz
  linear_combination hz - hm

theorem null_completion_signedValue (head tail : V)
    (hnull : B (head + tail) = 0) :
    B.signedValue tail = B.signedValue head := by
  exact congrArg Complex.re (hB.null_completion_diagonal head tail hnull)

/-- Pairing two compact heads equals pairing their corresponding tails. -/
theorem null_completion_cross (head₁ tail₁ head₂ tail₂ : V)
    (h₁ : B (head₁ + tail₁) = 0) (h₂ : B (head₂ + tail₂) = 0) :
    B head₁ head₂ = B tail₁ tail₂ := by
  have hleft : B (head₁ + tail₁) head₂ = 0 := by simp [h₁]
  have hright := hB.null_right_apply h₂ tail₁
  simp only [map_add, LinearMap.add_apply] at hleft hright
  linear_combination hleft - hright

/-- Compactification exposes both the tail self-term and its mixed term. -/
theorem null_compactification_change (r head tail : V)
    (hnull : B (head + tail) = 0) :
    B.signedValue (r - head) - B.signedValue r =
      2 * (B r tail).re + B.signedValue tail := by
  have hzero := hB.null_sub_signedValue hnull (r + tail)
  have hvec : r + tail - (head + tail) = r - head := by abel
  rw [hvec] at hzero
  rw [hzero, hB.signedValue_add]
  ring

/-- In particular, a positive-semidefinite form on all tails suffices for
the associated heads; the null-completion provider stays explicit. -/
theorem null_completion_nonnegative_iff (head tail : V)
    (hnull : B (head + tail) = 0) :
    0 ≤ B.signedValue head ↔ 0 ≤ B.signedValue tail := by
  rw [hB.null_completion_signedValue head tail hnull]

end LinearMap.IsSymm
