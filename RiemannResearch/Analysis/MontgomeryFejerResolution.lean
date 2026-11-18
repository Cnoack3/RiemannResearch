/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/

import RiemannResearch.Analysis.MontgomeryFejerCertificate
import RiemannResearch.Analysis.OrdinateCollisionRemainder
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Absolute resolution of the Montgomery Fejér certificate

The finite Fejér criterion from the user-provided Montgomery continuation admits
an explicit radius. Keeping the full oscillatory remainder gives a weighted
inverse-square budget for the nonzero gaps.
-/

noncomputable section
open Filter Zeta23
open scoped BigOperators

namespace RiemannResearch.Analysis.MontgomeryFormFactor
open ActualZeroOrdinate ActualZeroCollisionCertificate OrdinateCollisionCertificate
open MontgomeryPoisson

/-- Coefficient of the bounded sine square from a gap in the rescaled remainder. -/
def fejerGapCoefficient (T d : ℝ) : ℝ :=
  4 * cauchyWeight d / (Real.log T * d) ^ 2

/-- Weighted inverse-square budget over all ordered pairs at different heights. -/
def fejerGapBudget (T : ℝ) : ℝ := by
  classical
  exact ∑ i : Copies T, ∑ j : Copies T, if copyOrdinate T i = copyOrdinate T j then 0 else
    fejerGapCoefficient T (copyOrdinate T i - copyOrdinate T j)

private theorem fejerGapCoefficient_nonneg (T d : ℝ) : 0 ≤ fejerGapCoefficient T d := by
  unfold fejerGapCoefficient cauchyWeight
  positivity

theorem fejerGapBudget_nonneg (T : ℝ) : 0 ≤ fejerGapBudget T := by
  classical
  unfold fejerGapBudget
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact le_rfl
  · exact fejerGapCoefficient_nonneg _ _

theorem sq_mul_fejerNonzeroGapRemainder_eq {T R : ℝ} (hT : 1 < T) (hR : 0 < R) :
    R ^ 2 * fejerNonzeroGapRemainder T R =
      ∑ i : Copies T, ∑ j : Copies T, if copyOrdinate T i = copyOrdinate T j then 0 else
        fejerGapCoefficient T (copyOrdinate T i - copyOrdinate T j) *
          Real.sin (R * (Real.log T * (copyOrdinate T i - copyOrdinate T j)) / 2) ^ 2 := by
  classical
  unfold fejerNonzeroGapRemainder
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : copyOrdinate T i = copyOrdinate T j
  · simp [hij]
  · simp only [if_neg hij]
    let d := copyOrdinate T i - copyOrdinate T j
    change R ^ 2 * (cauchyWeight d * sincSquared R (Real.log T * d)) =
      fejerGapCoefficient T d * Real.sin (R * (Real.log T * d) / 2) ^ 2
    have hL := (Real.log_pos hT).ne'
    have hd : d ≠ 0 := sub_ne_zero.mpr hij
    have harg : R * (Real.log T * d) / 2 ≠ 0 :=
      div_ne_zero (mul_ne_zero hR.ne' (mul_ne_zero hL hd)) (by norm_num)
    rw [sincSquared, Real.sinc_of_ne_zero harg, div_pow]
    unfold fejerGapCoefficient
    field_simp [hR.ne', hL, hd]
    ring

theorem fejerNonzeroGapRemainder_le_gapBudget {T R : ℝ} (hT : 1 < T) (hR : 0 < R) :
    fejerNonzeroGapRemainder T R ≤ fejerGapBudget T / R ^ 2 := by
  classical
  apply (le_div_iff₀ (by positivity : 0 < R ^ 2)).mpr
  rw [mul_comm (fejerNonzeroGapRemainder T R), sq_mul_fejerNonzeroGapRemainder_eq hT hR]
  unfold fejerGapBudget
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  split_ifs
  · exact le_rfl
  · exact mul_le_of_le_one_right (fejerGapCoefficient_nonneg _ _) (Real.sin_sq_le_one _)

/-- This radius resolves the ordered collision count to within one pair. -/
def fejerResolvingRadius (T : ℝ) : ℝ := Real.sqrt (fejerGapBudget T + 1)

theorem fejerResolvingRadius_pos (T : ℝ) : 0 < fejerResolvingRadius T := by
  exact Real.sqrt_pos.2 (by linarith only [fejerGapBudget_nonneg T])

theorem fejerNonzeroGapRemainder_lt_one_of_resolving_radius {T R : ℝ}
    (hT : 1 < T) (hresolve : fejerResolvingRadius T ≤ R) :
    fejerNonzeroGapRemainder T R < 1 := by
  have hpos := fejerResolvingRadius_pos T
  have hR := hpos.trans_le hresolve
  have hs : fejerResolvingRadius T ^ 2 = fejerGapBudget T + 1 :=
    Real.sq_sqrt (by linarith only [fejerGapBudget_nonneg T])
  have hmul := mul_le_mul hresolve hresolve hpos.le hR.le
  refine (fejerNonzeroGapRemainder_le_gapBudget hT hR).trans_lt ?_
  apply (div_lt_iff₀ (by positivity : 0 < R ^ 2)).2
  nlinarith only [hs, hmul]

/-- Above the resolving radius the analytic-subtracted Fejér value determines
the unnormalized distinct-zero collision count as the unique integer in its unit band. -/
theorem normalized_fejer_sub_analytic_in_collision_unit_interval {T R : ℝ}
    (hT : 1 < T) (hresolve : fejerResolvingRadius T ≤ R) :
    let value := (T * Real.log T / (2 * Real.pi)) * fejerFormFactor T R -
      (analyticPairCount T : ℝ)
    (distinctZeroCollision T : ℝ) ≤ value ∧ value < (distinctZeroCollision T : ℝ) + 1 := by
  dsimp only
  rw [normalized_fejer_sub_analytic_eq hT ((fejerResolvingRadius_pos T).trans_le hresolve)]
  refine ⟨le_add_of_nonneg_right (fejerNonzeroGapRemainder_nonneg T R), ?_⟩
  linarith only [fejerNonzeroGapRemainder_lt_one_of_resolving_radius hT hresolve]

theorem fejer_critical_line_iff_of_resolving_radius {T R : ℝ}
    (hT : 1 < T) (hresolve : fejerResolvingRadius T ≤ R) :
    (T * Real.log T / (2 * Real.pi)) * fejerFormFactor T R - (analyticPairCount T : ℝ) < 2 ↔
      ∀ ρ ∈ cutoff T, ρ.re = 1 / 2 := by
  constructor
  · intro h
    exact (fejer_critical_line_iff hT).mp
      ⟨R, (fejerResolvingRadius_pos T).trans_le hresolve, by linarith only [h]⟩
  · intro hall
    have hc := (collision_eq_analyticPairCount_iff T).mpr hall
    have hz : distinctZeroCollision T = 0 := by
      have heq := collision_eq_analytic_add_distinctZeroCollision T
      omega
    have hu := (normalized_fejer_sub_analytic_in_collision_unit_interval hT hresolve).2
    rw [hz, Nat.cast_zero, zero_add] at hu
    exact hu.trans (by norm_num)

/-- The prescribed radius gives a single test per height equivalent to RH. -/
theorem eventually_resolving_fejer_gap_lt_two_iff_RH :
    (∀ᶠ T : ℝ in atTop,
      (T * Real.log T / (2 * Real.pi)) * fejerFormFactor T (fejerResolvingRadius T) -
        (analyticPairCount T : ℝ) < 2) ↔ RiemannHypothesis := by
  rw [← cofinal_fejer_critical_line_iff_RH]
  constructor
  · intro h H
    obtain ⟨T, ⟨hs, hHT⟩, hT⟩ :=
      ((h.and (eventually_ge_atTop H)).and (eventually_gt_atTop (1 : ℝ))).exists
    exact ⟨T, fejerResolvingRadius T, hHT, hT, fejerResolvingRadius_pos T,
      by linarith only [hs]⟩
  · intro h
    have hall := cofinal_fejer_critical_line_iff.mp h
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    exact (fejer_critical_line_iff_of_resolving_radius hT le_rfl).mpr (hall T)

end RiemannResearch.Analysis.MontgomeryFormFactor
