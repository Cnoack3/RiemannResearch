/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import RiemannResearch.Analysis.SmoothedDivisorMoment
import RiemannResearch.Analysis.ActualZetaFourthMomentReduction

/-! # Smoothing-defect moments on the full dyadic window

A cutoff N=floor(U) need not be as long as the interval [U,2U].
Splitting at the midpoint extends the previous length-N theorem to
every translated interval of length at most 2N.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory
namespace RiemannResearch.Analysis

theorem continuous_divisorSmoothingDefect {N : ℕ} (hN : 0 < N) :
    Continuous (divisorSmoothingDefect N) :=
  (continuous_smoothedDivisorSeries hN).sub (continuous_divisorPolynomial N (fun _ => 1))

theorem divisorSmoothingDefect_second_moment_le_twice {N : ℕ} (hN : 0 < N)
    {H T : ℝ} (hHT : H ≤ T) (hlen : T-H ≤ 2 * N) :
    (∫ t in H..T, ‖divisorSmoothingDefect N t‖^2) ≤
      (4*smoothedDivisorMomentConstant + 8*divisorMeanValueConstant) *
        N * (1+Real.log N)^4 := by
  have hc := (continuous_divisorSmoothingDefect hN).norm.pow 2
  have hleft := divisorSmoothingDefect_second_moment_le hN
    (H := H) (T := (H+T)/2) (by linarith) (by linarith)
  have hright := divisorSmoothingDefect_second_moment_le hN
    (H := (H+T)/2) (T := T) (by linarith) (by linarith)
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable H ((H+T)/2)) (hc.intervalIntegrable ((H+T)/2) T)
  simp only [Pi.pow_apply] at hadd
  rw [← hadd]
  linarith

/-- The actual smoothing defect on a dyadic height window, with a cutoff
between half the height and the height. -/
theorem divisorSmoothingDefect_dyadic_second_moment_le {N : ℕ} (hN : 0 < N)
    {U : ℝ} (hU : 2 ≤ U) (hNU : (N : ℝ) ≤ U) (hUN : U ≤ 2 * N) :
    (∫ t in U..2*U, ‖divisorSmoothingDefect N t‖^2) ≤
      (162 * (4*smoothedDivisorMomentConstant + 8*divisorMeanValueConstant)) *
        U * (Real.log U)^4 := by
  let A := 4*smoothedDivisorMomentConstant + 8*divisorMeanValueConstant
  have hA : 0 ≤ A := by
    dsimp [A, smoothedDivisorMomentConstant, divisorMeanValueConstant]
    positivity
  have hh := divisorSmoothingDefect_second_moment_le_twice hN
    (H := U) (T := 2*U) (by linarith) (by linarith)
  have hcost := cutoff_log_four_cost_le hN hU hNU hA
  have hpre : A * N * (1+Real.log N)^4 ≤ A * (U+N) * (1+Real.log N)^4 := by
    gcongr
    linarith
  exact hh.trans (hpre.trans hcost)

end RiemannResearch.Analysis
