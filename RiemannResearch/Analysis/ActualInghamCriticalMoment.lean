/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ComplexMixedMomentBounds
import RiemannResearch.Analysis.ActualMobiusZeroDetector

/-!
# The actual critical-line mixed moment in Ingham's method

This proves the Holder step (41) of Chourasiya--Simonic,
https://arxiv.org/html/2507.15184v2, for the actual zeta function and finite
Mobius mollifier. Asymptotic moment estimates and interpolation remain separate.
-/

noncomputable section
open MeasureTheory Set

namespace RiemannResearch.Analysis.InghamMollifier

theorem continuous_critical_zeta :
    Continuous (fun t : ℝ => riemannZeta ((1/2 : ℂ) + Complex.I * t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply (analyticAt_riemannZeta ?_).continuousAt.comp (by fun_prop)
  intro h
  have hr := congrArg Complex.re h
  norm_num at hr

theorem continuous_vertical_mollifier (X : ℕ) (σ : ℝ) :
    Continuous (fun t : ℝ => mollifier X ((σ : ℂ) + Complex.I * t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (mollifier_analyticAt X _).continuousAt.comp (by fun_prop)

/-- The critical-line Holder step in Ingham's method, with both moments on [H,T]. -/
theorem critical_error_moment_le (X : ℕ) {H T : ℝ} (hHT : H ≤ T) :
    (∫ t in H..T, ‖riemannZeta ((1/2 : ℂ) + Complex.I*t) *
      mollifier X ((1/2 : ℂ) + Complex.I*t) - 1‖ ^ (4/3 : ℝ)) ≤
      (2 : ℝ) ^ (1/3 : ℝ) *
        ((∫ t in H..T, ‖riemannZeta ((1/2 : ℂ) + Complex.I*t)‖ ^ 4) ^ (1/3 : ℝ) *
         (∫ t in H..T, ‖mollifier X ((1/2 : ℂ) + Complex.I*t)‖ ^ 2) ^ (2/3 : ℝ)
         + (T-H)) := by
  exact Complex.integral_mul_sub_one_four_thirds_le continuous_critical_zeta
    (by convert continuous_vertical_mollifier X (1/2) using 1 <;> norm_num) hHT

end RiemannResearch.Analysis.InghamMollifier
