/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! Exact finite summation by parts, including the boundary term.
Source: the user's cumulative cross-moment research agenda; standard finite Abel summation. -/

open scoped BigOperators
namespace RiemannResearch.Analysis
/-- Finite Abel summation including its endpoint and every signed increment. -/
theorem finite_abel {R : Type*} [CommRing R] (a m : ℕ → R) (H : ℕ) :
    (∑ n ∈ Finset.range (H + 1), a n * m n) =
      a H * (∑ n ∈ Finset.range (H + 1), m n) -
        ∑ t ∈ Finset.range H,
          (a (t + 1) - a t) * (∑ n ∈ Finset.range (t + 1), m n) := by
  induction H with
  | zero => simp
  | succ H ih =>
    calc
      _ = (∑ n ∈ Finset.range (H + 1), a n * m n) +
          a (H + 1) * m (H + 1) := Finset.sum_range_succ _ _
      _ = (a H * (∑ n ∈ Finset.range (H + 1), m n) -
          ∑ t ∈ Finset.range H,
            (a (t + 1) - a t) * (∑ n ∈ Finset.range (t + 1), m n)) +
          a (H + 1) * m (H + 1) := by rw [ih]
      _ = _ := by
        rw [Finset.sum_range_succ m (H + 1),
          Finset.sum_range_succ (fun t =>
            (a (t + 1) - a t) * (∑ n ∈ Finset.range (t + 1), m n)) H]
        ring

end RiemannResearch.Analysis
