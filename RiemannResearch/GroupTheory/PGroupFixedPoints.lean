/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.GroupTheory.PGroup

/-!
# Fixed points of finite p-group actions

This module collects reusable fixed-point consequences of orbit counting for
finite p-group actions.
-/

namespace RiemannResearch.GroupTheory

/-- A nonzero point fixed by every element of a multiplicative action. -/
def HasNonzeroFixedPoint (G V : Type*) [Group G] [Zero V] [SMul G V] : Prop :=
  ∃ v : V, v ≠ 0 ∧ ∀ g : G, g • v = v

/-- Orbit counting for a finite p-group action.

If the cardinality of the additive group is not congruent to one modulo p,
its fixed-point set cannot consist only of zero.
-/
theorem exists_nonzero_fixedPoint_of_isPGroup_of_not_card_modEq_one
    {p : ℕ} {G V : Type*} [Group G] [AddGroup V]
    [DistribMulAction G V] [Finite V] [Fact (Nat.Prime p)]
    (hG : IsPGroup p G) (hcard : ¬ Nat.card V ≡ 1 [MOD p]) :
    HasNonzeroFixedPoint G V := by
  by_contra hfixed
  have hsubsingleton : Subsingleton (MulAction.fixedPoints G V) := by
    constructor
    intro v w
    apply Subtype.ext
    have hv : v.1 = 0 := by
      by_contra hv0
      exact hfixed ⟨v.1, hv0, v.2⟩
    have hw : w.1 = 0 := by
      by_contra hw0
      exact hfixed ⟨w.1, hw0, w.2⟩
    exact hv.trans hw.symm
  have hnonempty : Nonempty (MulAction.fixedPoints G V) :=
    ⟨⟨0, by simp⟩⟩
  have hfixedCard : Nat.card (MulAction.fixedPoints G V) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨hsubsingleton, hnonempty⟩
  apply hcard
  have hmod := hG.card_modEq_card_fixedPoints V
  rwa [hfixedCard] at hmod

end RiemannResearch.GroupTheory
