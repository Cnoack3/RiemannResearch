/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring

/-!
# Boolean Signs

Adapted from the user-provided archive `combined_audited_lean_sources.zip`,
which describes these declarations as extracted from
`combined_audited_manuscript(4).pdf`. The manuscript itself was not bundled
with this continuation, so this module records archive provenance rather than
claiming page-level source verification.
-/

namespace RiemannResearch.RH.CombinedAudited

variable {ι : Type*}

/-- The squarefree Boolean/Koszul sign attached to a finite set of prime labels. -/
def squarefreeSign (s : Finset ι) : ℤ := (-1 : ℤ) ^ s.card

@[simp] theorem squarefreeSign_empty :
    squarefreeSign (∅ : Finset ι) = 1 := by
  simp [squarefreeSign]

@[simp] theorem squarefreeSign_singleton (a : ι) :
    squarefreeSign ({a} : Finset ι) = -1 := by
  simp [squarefreeSign]

/-- Adjoining one new prime reverses the Boolean/Koszul sign. -/
theorem squarefreeSign_insert [DecidableEq ι] {a : ι} {s : Finset ι} (ha : a ∉ s) :
    squarefreeSign (insert a s) = -squarefreeSign s := by
  rw [squarefreeSign, squarefreeSign, Finset.card_insert_of_notMem ha, pow_succ]
  ring

/-- Two independent parity shifts cancel. -/
theorem squarefreeSign_insert_insert [DecidableEq ι] {a b : ι} {s : Finset ι}
    (ha : a ∉ s) (hb : b ∉ insert a s) :
    squarefreeSign (insert b (insert a s)) = squarefreeSign s := by
  rw [squarefreeSign_insert hb, squarefreeSign_insert ha]
  ring

end RiemannResearch.RH.CombinedAudited
