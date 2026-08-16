/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Tactic.NormNum

/-!
# The arithmetic endpoint of the trialitarian central residue

These lemmas isolate the exact additive step that would finish the
trialitarian D4 central residue after a cubic boundary norm theorem has been
proved. They do not construct that norm theorem.

Source: user-provided Full Serre II Research Ledger, Section 5
(10 August 2026); the source supports the reduction statement.
-/

namespace RiemannResearch.GroupCohomology

/-- On a two-torsion additive class, multiplication by three is the
identity. -/
theorem three_nsmul_eq_self_of_two_torsion
    {A : Type*} [AddCommGroup A] {z : A}
    (h2 : (2 : ℕ) • z = 0) :
    (3 : ℕ) • z = z := by
  calc
    (3 : ℕ) • z = (2 + 1 : ℕ) • z := by norm_num
    _ = (2 : ℕ) • z + (1 : ℕ) • z := by rw [add_nsmul]
    _ = z := by simp only [h2, zero_add, one_nsmul]

/-- If a cubic norm calculation places `3 • z` in a boundary image and
`z` is two-torsion, then the same witness already maps to `z`.

The load-bearing missing input in the trialitarian application is
`hcubic`, not the additive argument proved here. -/
theorem central_residue_of_cubic_norm
    {A B : Type*} [AddCommGroup A]
    (boundary : B → A) {z : A}
    (h2 : (2 : ℕ) • z = 0)
    (hcubic : ∃ b, boundary b = (3 : ℕ) • z) :
    ∃ b, boundary b = z := by
  obtain ⟨b, hb⟩ := hcubic
  exact ⟨b, hb.trans (three_nsmul_eq_self_of_two_torsion h2)⟩

/-- The matrix formula for the order-three triality action on a pair of
central two-primary coordinates.  The fixed-point theorem below itself only
needs additive cancellation. -/
def trialityPair {A : Type*} [Add A] (z : A × A) : A × A :=
  (z.2, z.1 + z.2)

/-- Triality has no nonzero fixed central pair.  In the D4 application this
is the fixed-point calculation on the two-dimensional mod-two discriminant
or central-character module. -/
theorem trialityPair_fixed_iff
    {A : Type*} [AddCommGroup A] (z : A × A) :
    trialityPair z = z ↔ z = 0 := by
  constructor
  · intro h
    have h₁ : z.2 = z.1 := congrArg Prod.fst h
    have h₂ : z.1 + z.2 = z.2 := congrArg Prod.snd h
    have hz₁ : z.1 = 0 := by
      have hc := congrArg (fun a => a - z.2) h₂
      simpa using hc
    apply Prod.ext
    · simpa using hz₁
    · simpa using h₁.trans hz₁
  · rintro rfl
    simp [trialityPair]

end RiemannResearch.GroupCohomology
