/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoMellinFunctional
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Mellin bounds after an exactly zero head

Source: user-provided TwoStageSieveObstructionResearch20261020.md.
The actual integral is localized to the head cutoff before applying the
already established continuous tail Cauchy--Schwarz inequality.
-/

noncomputable section
open MeasureTheory Set

namespace RiemannResearch.RH.Pareto

/-- A finite zero head localizes the actual Mellin integral. -/
theorem paretoMellin_eq_tail_of_head_zero
    (f : ThresholdHilbert) (s : ℂ) (H : ℕ) (hH : 1 ≤ H)
    (hhead : ∀ n ≤ H, hilbertSequence f n = 0) :
    paretoMellin f s =
      ∫ x in Ioi (H : ℝ), mellinWeightedStep f x * paretoMellinKernel s x := by
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hz (x : ℝ) (hx : x ≤ (H : ℝ)) :
      mellinWeightedStep f x * paretoMellinKernel s x = 0 := by
    have hn : ⌊x⌋₊ ≤ H := by simpa using Nat.floor_mono hx
    simp [mellinWeightedStep, hhead _ hn]
  calc
    paretoMellin f s =
        ∫ x, mellinWeightedStep f x * paretoMellinKernel s x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      exact hz x ((le_of_not_gt hx).trans hHR)
    _ = ∫ x in Ioi (H : ℝ), mellinWeightedStep f x * paretoMellinKernel s x := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      exact hz x (le_of_not_gt hx)

/-- Complete Pareto norm controls a Mellin functional supported after its zero head. -/
theorem paretoMellin_norm_sq_le_of_head_zero
    (f : ThresholdHilbert) (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (H : ℕ) (hH : 1 ≤ H)
    (hhead : ∀ n ≤ H, hilbertSequence f n = 0) :
    ‖paretoMellin f s‖ ^ 2 ≤
      ‖f‖ ^ 2 * ((H : ℝ) ^ (1 - 2 * s.re) / (2 * s.re - 1)) := by
  have hd : 0 < 2 * s.re - 1 := by linarith
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  rw [paretoMellin_eq_tail_of_head_zero f s H hH hhead]
  apply (paretoMellin_tail_norm_sq_le f s hs hHR).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  rw [← mellinWeightedStep_energy f]
  exact integral_mono_measure
    (Measure.restrict_mono (Ioi_subset_Ioi hHR) le_rfl)
    (Filter.Eventually.of_forall (fun x => sq_nonneg ‖mellinWeightedStep f x‖))
    (mellinWeightedStep_memLp f).norm.integrable_sq

end RiemannResearch.RH.Pareto
