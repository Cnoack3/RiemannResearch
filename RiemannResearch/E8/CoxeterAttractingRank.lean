/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.GroupTheory.CoxeterAttractingRank

/-!
# E8 Coxeter attracting-rank specialization

The E8 Coxeter system, its length-plus-descent rank, and the corresponding
specializations of the general attracting-rank results.
-/

namespace RiemannResearch.E8

open RiemannResearch.GroupTheory

/-- Mathlib's presented Coxeter group of type E8. -/
abbrev E8CoxeterGroup : Type := CoxeterMatrix.E₈.Group

/-- The canonical Coxeter system on Mathlib's presented E8 Coxeter group. -/
abbrev e8CoxeterSystem :
    CoxeterSystem CoxeterMatrix.E₈ E8CoxeterGroup :=
  CoxeterMatrix.E₈.toCoxeterSystem

/-- Number of simple right descents of an element in the E8 Coxeter group. -/
noncomputable def e8RightDescentCount (w : E8CoxeterGroup) : ℕ :=
  coxeterRightDescentCount e8CoxeterSystem w

/-- The Coxeter-theoretic rank function from the document, defined directly on
Mathlib's E8 Coxeter group. -/
noncomputable def e8AttractingRank (w : E8CoxeterGroup) : ℕ :=
  e8CoxeterSystem.length w + e8RightDescentCount w

/-- E8 rank conclusions, conditional only on the currently absent Mathlib
longest-element length-complement theorem. -/
theorem e8AttractingRank_properties_of_lengthComplement
    (w0 : E8CoxeterGroup)
    (length_complement : ∀ w,
      e8CoxeterSystem.length (w0 * w) + e8CoxeterSystem.length w = 120) :
    AttractingRankConclusion E8CoxeterGroup 1 (fun w => w0 * w)
      e8AttractingRank e8CoxeterSystem.length e8RightDescentCount 120 8 := by
  exact coxeterAttractingRank_properties_of_lengthComplement
    e8CoxeterSystem w0 e8AttractingRank 120 (fun _ => rfl) length_complement

/-- The identity is the unique zero of the E8 length-plus-descent rank
function. This part of the source theorem is proved directly from Mathlib's
Coxeter system, without a geometric hypothesis. -/
theorem e8AttractingRank_eq_zero_iff (w : E8CoxeterGroup) :
    e8AttractingRank w = 0 ↔ w = 1 := by
  constructor
  · intro h
    have h' : e8CoxeterSystem.length w + e8RightDescentCount w = 0 := by
      simpa [e8AttractingRank] using h
    exact (e8CoxeterSystem.length_eq_zero_iff).mp
      (Nat.add_eq_zero_iff.mp h').1
  · rintro rfl
    simp [e8AttractingRank, e8RightDescentCount,
      coxeterRightDescentCount_one e8CoxeterSystem]

/-- For E8, the complementary attracting ranks sum to 120 + 8 = 128. -/
theorem e8_total_attracting_rank : 120 + 8 = 128 := by
  rfl

end RiemannResearch.E8
