/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoCRTReciprocalEnergy
import RiemannResearch.RH.ArithmeticCumulativeBasic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Exact rational CRT certificate with period six

Source: the finite constrained quadratic calculation in the user-provided
CRT discussion, 13 October 2026. Only this finite certificate is asserted.
It gives no bound uniform in the exact-head length.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative
noncomputable section

def crtSixWitness (n : ℕ) : ℝ :=
  residueFraction 2 n + (913 / 769 : ℝ) * residueFraction 3 n +
    (481 / 769 : ℝ) * residueFraction 6 n

theorem crtSixWitness_exact_head (n : ℕ) (hn : 0 < n) (hn2 : n ≤ 2) :
    crtSixWitness n = 1 := by
  interval_cases n <;> norm_num [crtSixWitness, residueFraction]

theorem crtSixWitness_energy :
    crtReciprocalEnergy 6 (fun n => 1 - crtSixWitness n) = 1669 / 27684 := by
  norm_num [crtReciprocalEnergy, Fin.sum_univ_succ, crtSixWitness, residueFraction]

theorem crtSixWitness_energy_lt :
    crtReciprocalEnergy 6 (fun n => 1 - crtSixWitness n) < 1 / 16 := by
  rw [crtSixWitness_energy]
  norm_num

end
end RiemannResearch.RH.Pareto
