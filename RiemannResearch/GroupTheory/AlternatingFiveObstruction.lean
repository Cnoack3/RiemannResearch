/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
import Mathlib.Tactic.NormNum

/-!
# The alternating-five obstruction to cyclic-prime towers

The order and nonsolvability of `A₅` show that an extension degree supported
at 2, 3, and 5 does not by itself permit reduction to a tower of cyclic
prime-degree extensions.

This is the proof-gap certificate used in the audit of the 5 August 2026 E8
Serre II memorandum. It is not a counterexample to the cohomological theorem.
-/

namespace RiemannResearch.GroupTheory

/-- The alternating group on five letters has order sixty. -/
theorem alternatingGroup_fin_five_card :
    Fintype.card (alternatingGroup (Fin 5)) = 60 := by
  rw [card_alternatingGroup, Fintype.card_fin]
  norm_num [Nat.factorial]

/-- The order of A5 has only the prime support allowed in Gille's printed
`2^a * 3^b * 5^c` extension-degree hypothesis. -/
theorem alternatingGroup_fin_five_card_prime_support :
    Fintype.card (alternatingGroup (Fin 5)) = 2 ^ 2 * 3 * 5 := by
  rw [alternatingGroup_fin_five_card]
  norm_num

/-- A5 is not solvable, so a cyclic-prime tower induction does not cover every
group allowed by the printed degree hypothesis. -/
theorem alternatingGroup_fin_five_not_solvable :
    ¬ Group.IsSolvable (alternatingGroup (Fin 5)) := by
  intro h
  let _ : Group.IsSolvable (alternatingGroup (Fin 5)) := h
  have hlt :=
    Group.IsSolvable.commutator_lt_top_of_nontrivial
      (alternatingGroup (Fin 5))
  rw [commutator_alternatingGroup_eq_top (by simp)] at hlt
  exact lt_irrefl _ hlt

end RiemannResearch.GroupTheory
