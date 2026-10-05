/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# Analytic orders of a quadratic zero detector

The elementary factorization underlying Chourasiya--Simonic's detector in
Section 4, arXiv:2507.15184v2, is proved for arbitrary analytic functions:
https://arxiv.org/html/2507.15184v2.
At a zero of F the unit factor has order zero, so the full order is the
sum of the orders of F and M, including possible infinite orders.
This formalizes the algebraic detector step, not a density theorem.
-/

noncomputable section

namespace Complex
def quadraticZeroDetector (F M : ℂ → ℂ) (s : ℂ) : ℂ := 1-(1-F s*M s)^2
theorem quadraticZeroDetector_factor (F M : ℂ → ℂ) (s : ℂ) :
    quadraticZeroDetector F M s = (2-F s*M s)*(F s*M s) := by unfold quadraticZeroDetector; ring
theorem quadraticZeroDetector_analyticAt {F M : ℂ → ℂ} {s : ℂ}
    (hF : AnalyticAt ℂ F s) (hM : AnalyticAt ℂ M s) :
    AnalyticAt ℂ (quadraticZeroDetector F M) s := by unfold quadraticZeroDetector; fun_prop
theorem quadraticZeroDetector_order {F M : ℂ → ℂ} {s : ℂ}
    (hF : AnalyticAt ℂ F s) (hM : AnalyticAt ℂ M s) (hz : F s=0) :
    analyticOrderAt (quadraticZeroDetector F M) s =
      analyticOrderAt F s+analyticOrderAt M s := by
  have hunit : AnalyticAt ℂ (fun z => 2-F z*M z) s := by fun_prop
  have hunit0 : analyticOrderAt (fun z => 2-F z*M z) s=0 :=
    hunit.analyticOrderAt_eq_zero.mpr (by simp [hz])
  have he : quadraticZeroDetector F M = (fun z => 2-F z*M z)*(F*M) := by
    funext z
    exact quadraticZeroDetector_factor F M z
  rw [he, analyticOrderAt_mul hunit (hF.mul hM), hunit0, zero_add,
    analyticOrderAt_mul hF hM]
end Complex
