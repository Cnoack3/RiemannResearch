/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.NormNum

/-!
# Elementary order facts for Omega_8^+(2)

This module records the displayed order used in the E8 full-Weyl descent
argument and the resulting noncommutativity consequence for a simple group of
that order.
-/

namespace RiemannResearch.E8

/-- The displayed order of Omega_8^+(2) in decimal form. -/
theorem omegaEightPlusTwo_order :
    2 ^ 12 * 3 ^ 5 * 5 ^ 2 * 7 = 174182400 := by
  norm_num

/-- A simple group of the displayed composite order is nonabelian. -/
theorem nonabelian_of_isSimpleGroup_of_card_eq_omegaOrder
    {Ω : Type*} [Group Ω] [Finite Ω]
    (hsimple : IsSimpleGroup Ω)
    (hcard : Nat.card Ω = 2 ^ 12 * 3 ^ 5 * 5 ^ 2 * 7) :
    ∃ a b : Ω, a * b ≠ b * a := by
  by_contra hnonabelian
  simp only [not_exists, not_not] at hnonabelian
  let _ : IsMulCommutative Ω :=
    ⟨⟨fun a b => hnonabelian a b⟩⟩
  have hprime : Nat.Prime (Nat.card Ω) :=
    Group.is_simple_iff_prime_card.mp hsimple
  rw [hcard] at hprime
  have htwo : 2 ∣ 174182400 := by norm_num
  have h := hprime.eq_one_or_self_of_dvd 2 htwo
  norm_num at h

end RiemannResearch.E8
