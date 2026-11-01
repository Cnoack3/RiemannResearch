/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ConditionalMeanEnergy
import Mathlib.Tactic.Ring

/-!
# Normalized Cesàro energy and lower logarithmic growth

Source: user-provided
`Conditional_IID_Pareto_Cesaro_Research_Agenda_2026-11-01.md`,
Sections 8 and 11.5. This formalizes the stated sufficient condition;
it does not construct a family meeting its arithmetic growth premise.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open Probability.ConditionalIID Analysis.Cesaro

theorem conditionalMeanSquare_mul (g : ℕ → ℝ) (c : ℝ) :
    conditionalMeanSquare (fun n => c * g n) = c ^ 2 * conditionalMeanSquare g := by
  have hmean (n : ℕ) : cesaro (fun n => c * g n) n = c * cesaro g n := by
    simp only [cesaro, ← Finset.mul_sum, mul_div_assoc]
  unfold conditionalMeanSquare
  simp_rw [hmean, mul_pow]
  calc
    _ = ∑' k : ℕ, c ^ 2 * (conditionalWeight k * cesaro g (k + 1) ^ 2) := by
      apply tsum_congr
      intro k
      ring
    _ = _ := tsum_mul_left

theorem conditionalMeanSquare_normalize (g : ℕ → ℝ) (c : ℝ) :
    conditionalMeanSquare (fun n => c⁻¹ * g n) =
      conditionalMeanSquare g / |c| ^ 2 := by
  rw [conditionalMeanSquare_mul]
  simp only [inv_pow, sq_abs]
  ring

end RiemannResearch.RH.Pareto
