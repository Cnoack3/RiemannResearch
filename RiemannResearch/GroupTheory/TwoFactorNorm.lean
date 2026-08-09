/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Prod

/-!
# Obstruction to a two-factor group norm

Generic group-theoretic content of Proposition 10.7 in the user-provided
27 July 2026 rational-involutions manuscript.
-/

namespace RiemannResearch.GroupTheory

/-- Proposition 10.7. -/
theorem commutative_of_two_factor_norm
    {G : Type*} [Group G] (N : G × G →* G)
    (hleft : ∀ g : G, N (g, 1) = g)
    (hright : ∀ g : G, N (1, g) = g) :
    ∀ g h : G, g * h = h * g := by
  intro g h
  calc
    g * h = N (g, 1) * N (1, h) := by rw [hleft, hright]
    _ = N ((g, 1) * (1, h)) := (N.map_mul (g, 1) (1, h)).symm
    _ = N ((1, h) * (g, 1)) := by simp
    _ = N (1, h) * N (g, 1) := N.map_mul (1, h) (g, 1)
    _ = h * g := by rw [hleft, hright]

theorem no_two_factor_norm_of_noncommuting
    {G : Type*} [Group G] (g h : G) (hne : g * h ≠ h * g) :
    ¬ ∃ N : G × G →* G,
      (∀ x : G, N (x, 1) = x) ∧ (∀ x : G, N (1, x) = x) := by
  rintro ⟨N, hleft, hright⟩
  exact hne (commutative_of_two_factor_norm N hleft hright g h)

end RiemannResearch.GroupTheory
