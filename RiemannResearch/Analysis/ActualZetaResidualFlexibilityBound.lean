/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZetaSquareResidualBound
import RiemannResearch.Analysis.ActualZetaResidualFlexibility

/-! # The uniform actual zeta residual with arbitrary independent cutoffs -/

noncomputable section
open MeasureTheory Complex Set
open scoped BigOperators

namespace RiemannResearch.Analysis

/-- One unconditional constant controls every actual residual formed from two
independent positive cutoffs at most the height, unit-bounded coefficients,
and any continuous phase bounded by one on the dyadic interval. -/
theorem exists_actual_uniform_two_cutoff_residual_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 2 ≤ U → ∀ N M : ℕ,
      0 < N → 0 < M → (N : ℝ) ≤ U → (M : ℝ) ≤ U →
      ∀ u v : ℕ → ℂ, (∀ n ∈ Finset.Icc 1 N, ‖u n‖ ≤ 1) →
        (∀ n ∈ Finset.Icc 1 M, ‖v n‖ ≤ 1) →
      ∀ φ : ℝ → ℂ, Continuous φ → (∀ t ∈ Set.Icc U (2 * U), ‖φ t‖ ≤ 1) →
      (∫ t in U..(2 * U),
        ‖zetaSquareResidual (divisorPolynomial N u)
          (fun t => φ t * star (divisorPolynomial M v t)) t‖ ^ 2) ≤
            C * U * (Real.log U) ^ 4 :=
  exists_uniform_two_cutoff_residual_bound_of_fourth_moment
    exists_actual_zeta_fourth_moment_bound

/-- The actual functional-equation residual is uniform in every positive cutoff
at most the height; the lower comparability constraint has been removed. -/
theorem exists_actual_zetaSquareResidual_uniform_cutoff_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ U ≥ 2, ∀ N : ℕ, 0 < N → (N : ℝ) ≤ U →
      (∫ t in U..2 * U, ‖zetaSquareResidual (divisorPolynomial N (fun _ => 1))
        (fun t => zetaSquareCriticalPhase t *
          star (divisorPolynomial N (fun _ => 1) t)) t‖ ^ 2) ≤
            C * U * (Real.log U) ^ 4 := by
  obtain ⟨C, hC, hb⟩ := exists_actual_uniform_two_cutoff_residual_bound
  refine ⟨C, hC, ?_⟩
  intro U hU N hN hNU
  exact hb U hU N N hN hN hNU hNU (fun _ => 1) (fun _ => 1)
    (by simp) (by simp) zetaSquareCriticalPhase continuous_zetaSquareCriticalPhase
    (by simp)

end RiemannResearch.Analysis
