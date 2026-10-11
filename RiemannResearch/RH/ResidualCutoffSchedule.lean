/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.LogarithmicCorrectionTarget
import RiemannResearch.Analysis.ResidualGainProduct

/-!
# Actual residual gain along unrestricted cutoff schedules

Source: user-provided
RH_Zero_Ordinates_Haar_and_Actual_Residual_Gain_Consolidated_2026-10-11.md,
Sections 5.3 and 15 (variable costs and uncontrolled larger cutoffs).
This extension retains the exact distance drop and product for any increasing
schedule. The required nonsummable actual gain provider remains open.
-/

open Filter
open scoped Topology BigOperators
noncomputable section
namespace RiemannResearch.RH.Pareto.CoupledResidual
open RiemannResearch.Analysis.ResidualGain

def cutoffRelativeGain (M : ℕ → ℕ) (n : ℕ) : ℝ :=
  (distance (M n) - distance (M (n + 1))) / distance (M n)

theorem cutoffRelativeGain_nonneg (M : ℕ → ℕ) (hM : Monotone M) (n : ℕ) :
    0 ≤ cutoffRelativeGain M n :=
  div_nonneg (sub_nonneg.mpr (distance_antitone (hM (Nat.le_succ n))))
    (distance_pos _).le

theorem cutoffRelativeGain_lt_one (M : ℕ → ℕ) (n : ℕ) :
    cutoffRelativeGain M n < 1 := by
  unfold cutoffRelativeGain
  apply (div_lt_one (distance_pos _)).mpr
  linarith [distance_pos (M (n + 1))]

theorem cutoff_distance_recurrence (M : ℕ → ℕ) (n : ℕ) :
    distance (M (n + 1)) = distance (M n) * (1 - cutoffRelativeGain M n) := by
  unfold cutoffRelativeGain
  field_simp [ne_of_gt (distance_pos (M n))]
  ring

/-- Complete product identity, with all actual stage gains preserved. -/
theorem cutoff_distance_product (M : ℕ → ℕ) (N : ℕ) :
    distance (M N) = distance (M 0) *
      ∏ n ∈ Finset.range N, (1 - cutoffRelativeGain M n) := by
  simpa only [survivalProduct] using
    recurrence_eq_mul_product (d := fun n => distance (M n))
      (r := cutoffRelativeGain M) (cutoff_distance_recurrence M) N

theorem cutoff_distance_tendsto_zero_iff (M : ℕ → ℕ) (hM : Monotone M) :
    Tendsto (fun n => distance (M n)) atTop (𝓝 0) ↔
      ¬ Summable (cutoffRelativeGain M) :=
  residual_tendsto_zero_iff_not_summable
    (distance_pos _) (cutoffRelativeGain_nonneg M hM)
    (cutoffRelativeGain_lt_one M) (cutoff_distance_recurrence M)

/-- No dyadic bound, cutoff growth rate, or RH-dependent input is required.
The actual nonsummability hypothesis is the outstanding arithmetic obligation. -/
theorem riemannHypothesis_of_cutoff_gain_divergence
    (M : ℕ → ℕ) (hM : Monotone M)
    (h : ¬ Summable (cutoffRelativeGain M)) : RiemannHypothesis :=
  riemannHypothesis_of_distance_convergence M
    ((cutoff_distance_tendsto_zero_iff M hM).mpr h)

theorem riemannHypothesis_of_cutoff_gain_minorant
    (M : ℕ → ℕ) (hM : Monotone M) (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hdiv : ¬ Summable a)
    (hgain : ∀ n, a n ≤ cutoffRelativeGain M n) : RiemannHypothesis := by
  apply riemannHypothesis_of_cutoff_gain_divergence M hM
  intro hs
  exact hdiv (Summable.of_nonneg_of_le ha hgain hs)

end RiemannResearch.RH.Pareto.CoupledResidual
