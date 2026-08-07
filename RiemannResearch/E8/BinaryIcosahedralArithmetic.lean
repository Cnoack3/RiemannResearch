/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib

/-!
# Binary-icosahedral arithmetic and nonsolvability guard

The finite order calculations are the numerical backbone of the two-gauge
reduction. The generic perfect-group lemma records why a prime-cyclic normal
tower cannot be invoked for a nontrivial perfect Galois group such as
`SL₂(𝔽₅)`; a separate finite-group certificate is still needed to instantiate
that example in Lean.
-/

namespace RiemannResearch.E8

/-- A nontrivial perfect group is not solvable. This prevents a cyclic-prime
induction from being silently applied to a perfect Galois group. -/
theorem not_solvable_of_nontrivial_perfect
    (G : Type*) [Group G] [Nontrivial G]
    (hperfect : commutator G = ⊤) :
    ¬ Group.IsSolvable G := by
  intro hsolv
  obtain ⟨n, hn⟩ := hsolv.solvable
  have hall : ∀ m : ℕ, derivedSeries G m = ⊤ := by
    intro m
    induction m with
    | zero => exact derivedSeries_zero G
    | succ m ih =>
        rw [show m + 1 = Nat.succ m from rfl, derivedSeries_succ, ih]
        exact hperfect
  rw [hall n] at hn
  exact top_ne_bot hn

/-- For subgroup orders `|H| = 24`, `|K| = 20`, and
`|H ∩ K| = 4` inside a group of order 120, the fixed-field degrees are
5, 6, and 30, and the first two degrees are coprime. -/
theorem binaryIcosahedral_orders_and_indices :
    120 = 2 ^ 3 * 3 * 5 ∧
      24 * 20 = 4 * 120 ∧
      120 / 24 = 5 ∧
      120 / 20 = 6 ∧
      120 / 4 = 30 ∧
      Nat.gcd 5 6 = 1 := by
  norm_num

end RiemannResearch.E8
