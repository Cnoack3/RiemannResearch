/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Full signed logarithmic rectangle functional

The four signs match the Littlewood functional in Chourasiya--Simonic,
arXiv:2507.15184v2, equation (32):
https://arxiv.org/html/2507.15184v2.
The horizontal functions are explicit argument lifts. Their analytic
compatibility and the Littlewood identity are not asserted by this definition.
A common additive change cancels exactly; independent changes need not.
-/

noncomputable section

namespace Complex
/-- Full signed rectangle functional. The horizontal functions are supplied
argument lifts; no principal-argument or analytic-compatibility claim is made. -/
def logRectangleBoundary (F : ℂ → ℂ) (aH aT : ℝ → ℝ) (α β H T : ℝ) : ℝ :=
  (∫ t in H..T, Real.log ‖F ((α : ℂ)+(t : ℂ)*Complex.I)‖) -
  (∫ t in H..T, Real.log ‖F ((β : ℂ)+(t : ℂ)*Complex.I)‖) +
  (∫ u in α..β, aT u) - (∫ u in α..β, aH u)
theorem logRectangleBoundary_le {F : ℂ → ℂ} {aH aT : ℝ → ℝ}
    {α β H T A R U V : ℝ}
    (hleft : (∫ t in H..T, Real.log ‖F ((α : ℂ)+(t : ℂ)*Complex.I)‖) ≤ A)
    (hright : R ≤ (∫ t in H..T, Real.log ‖F ((β : ℂ)+(t : ℂ)*Complex.I)‖))
    (htop : (∫ u in α..β, aT u) ≤ U)
    (hbottom : V ≤ (∫ u in α..β, aH u)) :
    logRectangleBoundary F aH aT α β H T ≤ A-R+U-V := by
  unfold logRectangleBoundary
  linarith

/-- A common change of the two horizontal argument lifts cancels exactly.
Independent changes do not cancel; analytic branch compatibility stays explicit. -/
theorem logRectangleBoundary_add_argument_const (F : ℂ → ℂ) (aH aT : ℝ → ℝ)
    (α β H T c : ℝ)
    (hH : IntervalIntegrable aH MeasureTheory.volume α β)
    (hT : IntervalIntegrable aT MeasureTheory.volume α β) :
    logRectangleBoundary F (fun u => aH u+c) (fun u => aT u+c) α β H T =
      logRectangleBoundary F aH aT α β H T := by
  unfold logRectangleBoundary
  rw [intervalIntegral.integral_add hT intervalIntegrable_const,
    intervalIntegral.integral_add hH intervalIntegrable_const]
  ring

end Complex
