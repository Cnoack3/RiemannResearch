/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Fixed points for generated subgroup actions

This module isolates the formal gluing step behind simultaneous-gauge
criteria. It does not assert that separately existing local fixed points
coincide; a common point is an essential hypothesis.
-/

namespace RiemannResearch.GroupTheory

/-- A point fixed by each of two subgroups is fixed by the whole group when
the two subgroups generate the whole group.

This is the precise formal implication used in the manuscript's mixed-prime
simultaneous-fixed-point criterion. It deliberately does not infer the
existence of a common fixed point from nonempty fixed-point sets.
-/
theorem fixed_of_fixed_on_join_eq_top
    {G X : Type*} [Group G] [MulAction G X]
    (H K : Subgroup G) (hgen : H ⊔ K = ⊤) {x : X}
    (hH : ∀ h : H, (h : G) • x = x)
    (hK : ∀ k : K, (k : G) • x = x) :
    ∀ g : G, g • x = x := by
  intro g
  have hHle : H ≤ MulAction.stabilizer G x := by
    intro h hh
    exact hH ⟨h, hh⟩
  have hKle : K ≤ MulAction.stabilizer G x := by
    intro k hk
    exact hK ⟨k, hk⟩
  have htop : (⊤ : Subgroup G) ≤ MulAction.stabilizer G x := by
    rw [← hgen]
    exact sup_le hHle hKle
  exact htop (by simp)

end RiemannResearch.GroupTheory
