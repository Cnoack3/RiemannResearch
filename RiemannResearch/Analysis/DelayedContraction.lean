/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-! A uniform bound for a real-variable recurrence whose delay is at least one. -/

namespace RiemannResearch.Analysis

/-- A bounded initial interval and a uniform delayed contraction give a global bound.
This is induction on expanding finite intervals; no hypothesis about the
unknown future values of `F` is used. -/
theorem delayed_contraction_bound
    (F r : ℝ → ℝ) (T B C : ℝ)
    (hbase : ∀ t : ℝ, 0 ≤ t → t ≤ T → F t ≤ B)
    (hr : ∀ t : ℝ, T < t → 0 ≤ r t ∧ r t ≤ t - 1)
    (hrec : ∀ t : ℝ, T < t → F t ≤ (1 / 2 : ℝ) * F (r t) + C) :
    ∀ t : ℝ, 0 ≤ t → F t ≤ max B (2 * C) := by
  have hbound (n : ℕ) : ∀ t : ℝ, 0 ≤ t → t ≤ T + (n : ℝ) →
      F t ≤ max B (2 * C) := by
    induction n with
    | zero =>
        intro t ht htn
        have htT : t ≤ T := by simpa only [Nat.cast_zero, add_zero] using htn
        exact (hbase t ht htT).trans (le_max_left _ _)
    | succ n ih =>
        intro t ht htn
        by_cases htT : t ≤ T
        · exact (hbase t ht htT).trans (le_max_left _ _)
        · have hTt : T < t := lt_of_not_ge htT
          obtain ⟨hr0, hrle⟩ := hr t hTt
          have hrt : r t ≤ T + (n : ℝ) := by
            simp only [Nat.cast_succ] at htn
            linarith
          have hprev := ih (r t) hr0 hrt
          have hstep := hrec t hTt
          have hc := le_max_right B (2 * C)
          linarith
  intro t ht
  obtain ⟨n, hn⟩ := exists_nat_ge (t - T)
  exact hbound n t ht (by linarith)

end RiemannResearch.Analysis
