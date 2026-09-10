import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Module

/-!
# Finite geometric difference identity

Source: independently developed finite Abel summation identity, used by
the actual arithmetic residue telescoping in the RH regularization.
-/

open scoped BigOperators

namespace RiemannResearch.Analysis

/-- Finite Abel summation for a geometric difference, with its full terminal. -/
theorem finite_geometric_difference
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (q : ℝ) (v : ℕ → H) (J : ℕ) :
    (∑ j ∈ Finset.range (J + 1), q ^ j • (v (j + 1) - v j)) =
      q ^ J • v (J + 1) - v 0 +
        (1 - q) • ∑ j ∈ Finset.range J, q ^ j • v (j + 1) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, pow_succ]
    module

end RiemannResearch.Analysis
