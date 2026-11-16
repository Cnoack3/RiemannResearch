/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZetaSquareResidualBound
import RiemannResearch.Analysis.ActualInghamMixedMoment

/-! # The unconditional uniform actual Ingham mixed moment -/

noncomputable section
open MeasureTheory Complex Set

namespace RiemannResearch.Analysis.InghamMollifier

/-- The actual zeta function and the actual finite Möbius mollifier satisfy
one mixed four-thirds moment bound, uniform in both height and cutoff. -/
theorem exists_actual_critical_error_moment_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ X : ℕ,
      1 ≤ X → (X : ℝ) ≤ T →
      (∫ t in (0 : ℝ)..T, ‖riemannZeta ((1 / 2 : ℂ) + I * t) *
        mollifier X ((1 / 2 : ℂ) + I * t) - 1‖ ^ (4 / 3 : ℝ)) ≤
          C * T * (1 + Real.log T) ^ 2 :=
  exists_critical_error_moment_bound_of_fourth_moment
    exists_actual_zeta_fourth_moment_bound

/-- The conventional logarithmic form, including the cutoff `X = 1`. -/
theorem exists_actual_critical_error_moment_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ X : ℕ,
      1 ≤ X → (X : ℝ) ≤ T →
      (∫ t in (0 : ℝ)..T, ‖riemannZeta ((1 / 2 : ℂ) + I * t) *
        mollifier X ((1 / 2 : ℂ) + I * t) - 1‖ ^ (4 / 3 : ℝ)) ≤
          C * T * (Real.log T) ^ 2 :=
  exists_critical_error_moment_log_bound_of_fourth_moment
    exists_actual_zeta_fourth_moment_bound

end RiemannResearch.Analysis.InghamMollifier
