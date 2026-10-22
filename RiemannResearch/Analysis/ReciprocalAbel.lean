import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Finite reciprocal Abel summation

Source: direct finite summation by parts; this module retains the endpoint
correction needed in the harmonic von-Mangoldt remainder argument.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis

/-- An exact finite Abel formula, retaining the endpoint correction.
Applied to a(n) = Lambda(n)-1, its primitive is psi(N)-N. -/
theorem reciprocal_partial_sum_abel
    (a A : ℕ → ℝ) (hzero : A 0 = 0)
    (hstep : ∀ n, A (n + 1) = A n + a (n + 1)) (N : ℕ) :
    (∑ n ∈ Finset.range N, a (n + 1) / ((n : ℝ) + 1)) =
      A N / ((N : ℝ) + 1) +
        ∑ n ∈ Finset.range N,
          A (n + 1) / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  induction N with
  | zero => simp [hzero]
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, hstep N]
      push_cast
      have h1 : (N : ℝ) + 1 ≠ 0 := by positivity
      have h2 : (N : ℝ) + 2 ≠ 0 := by positivity
      field_simp [h1, h2]
      <;> ring

end RiemannResearch.Analysis
