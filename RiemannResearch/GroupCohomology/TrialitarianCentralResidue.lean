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

end RiemannResearch.GroupCohomology
