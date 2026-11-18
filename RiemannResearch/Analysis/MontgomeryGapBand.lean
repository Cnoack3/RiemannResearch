/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/

import RiemannResearch.Analysis.MontgomeryCauchyGapMesh
import RiemannResearch.Analysis.MontgomeryGapPrescribedMesh
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Signed-gap tests on an interval away from the origin

Subtracting two instances of the physical triangle identity from the
Goldston–Lee–Schettler–Suriajaya argument (arXiv:2503.15449v3, Section 3)
cancels the integrated positive-gap mass below the lower endpoint.
A centered quadrature on the remaining interval estimates the absolute
distinct-zero collision count.
-/

noncomputable section
open Filter MeasureTheory Set Zeta23

namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate ActualZeroCollisionCertificate ActualZeroWindowVariance

/-- The physical triangle increment retains the equal-ordinate atom, and
only the integrated positive-gap observations on the chosen band. -/
theorem physicalTriangle_sub_eq_collision_add_positiveGapBand {T U R : ℝ}
    (hT : 1 < T) (hU : 0 ≤ U) (hUR : U ≤ R) :
    actualPhysicalTriangleEnergy T (R / (Real.log T / (2 * Real.pi))) -
      actualPhysicalTriangleEnergy T (U / (Real.log T / (2 * Real.pi))) =
      (R - U) * ((actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi))) +
        2 * (∫ u in U..R, positiveGapMass T u) := by
  have hP := positiveGapMass_mono hT
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (f := positiveGapMass T) (a := 0) (b := U) (c := R)
    hP.intervalIntegrable hP.intervalIntegrable
  rw [physicalTriangle_eq_collision_add_positive_gaps hT (hU.trans hUR),
    physicalTriangle_eq_collision_add_positive_gaps hT hU]
  rw [← hi]
  ring

/-- The centered sampled signed-gap statistic on the interval from U to R. -/
def centeredSampledGapBand (T U R : ℝ) (n : ℕ) : ℝ :=
  let D := T * Real.log T / (2 * Real.pi)
  let L := Real.log T / (2 * Real.pi)
  let Q := gapMeshSum (fun u => positiveGapMass T (u + U)) (R - U) n
  D / (R - U) * (actualPhysicalTriangleEnergy T (R / L) -
    actualPhysicalTriangleEnergy T (U / L) - 2 * Q) -
      (analyticPairCount T : ℝ) - (D / n) * (positiveGapMass T R - positiveGapMass T U)

theorem centeredSampledGapBand_sub_collision_eq {T U R : ℝ}
    (hT : 1 < T) (hU : 0 ≤ U) (hUR : U < R) (n : ℕ) :
    let D := T * Real.log T / (2 * Real.pi)
    centeredSampledGapBand T U R n - (distinctZeroCollision T : ℝ) =
      (2 * D / (R - U)) * ((∫ u in U..R, positiveGapMass T u) -
        gapMeshSum (fun u => positiveGapMass T (u + U)) (R - U) n) -
        (D / n) * (positiveGapMass T R - positiveGapMass T U) := by
  have hD : 0 < T * Real.log T / (2 * Real.pi) :=
    div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  dsimp only [centeredSampledGapBand]
  rw [physicalTriangle_sub_eq_collision_add_positiveGapBand hT hU hUR.le,
    collision_eq_analytic_add_distinctZeroCollision, Nat.cast_add]
  field_simp [(sub_pos.mpr hUR).ne', hD.ne', (Real.log_pos hT).ne',
    (zero_lt_one.trans hT).ne', Real.pi_ne_zero]
  ring

/-- The error budget depends on the number of gaps in the band alone. -/
theorem abs_centeredSampledGapBand_sub_collision_le {T U R : ℝ}
    (hT : 1 < T) (hU : 0 ≤ U) (hUR : U < R) {n : ℕ} (hn : 0 < n) :
    |centeredSampledGapBand T U R n - (distinctZeroCollision T : ℝ)| ≤
      (T * Real.log T / (2 * Real.pi) / n) * (positiveGapMass T R - positiveGapMass T U) := by
  let p := fun u : ℝ => positiveGapMass T (u + U)
  let D := T * Real.log T / (2 * Real.pi)
  let S := R - U
  have hD : 0 ≤ D :=
    div_nonneg (mul_nonneg (zero_lt_one.trans hT).le (Real.log_pos hT).le) (by positivity)
  have hS : 0 < S := sub_pos.mpr hUR
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hp : Monotone p := by
    intro x y hxy
    apply positiveGapMass_mono hT
    change x + U ≤ y + U
    linarith only [hxy]
  have hshift : (∫ u in (0 : ℝ)..S, p u) = ∫ u in U..R, positiveGapMass T u := by
    simpa only [p, S, zero_add, sub_add_cancel] using
      (intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := S) (positiveGapMass T) U)
  obtain ⟨hlo, hhi⟩ := integral_sub_gapMeshSum_bounds hp hS.le hn
  rw [hshift] at hlo hhi
  have hends : p S - p 0 = positiveGapMass T R - positiveGapMass T U := by
    simp only [p, S, sub_add_cancel, zero_add]
  rw [hends] at hhi
  have hs : 0 ≤ 2 * D / S := div_nonneg (mul_nonneg (by norm_num) hD) hS.le
  have hlo' := mul_nonneg hs hlo
  have hhi' := mul_le_mul_of_nonneg_left hhi hs
  have hscale : 2 * D / S * (S / n * (positiveGapMass T R - positiveGapMass T U)) =
      2 * (D / n * (positiveGapMass T R - positiveGapMass T U)) := by
    field_simp [hS.ne', hn']
  rw [hscale] at hhi'
  rw [centeredSampledGapBand_sub_collision_eq hT hU hUR n, abs_le]
  change -(D / n * (positiveGapMass T R - positiveGapMass T U)) ≤
      2 * D / S * ((∫ u in U..R, positiveGapMass T u) - gapMeshSum p S n) -
        D / n * (positiveGapMass T R - positiveGapMass T U) ∧
    _ ≤ D / n * (positiveGapMass T R - positiveGapMass T U)
  exact ⟨by linarith only [hlo'], by linarith only [hhi']⟩

/-- A band statistic with error budget below one pair certifies the entire
cutoff, even when the mesh has no observations below its lower endpoint. -/
theorem centered_sampled_gap_band_critical_line_iff {T U R : ℝ}
    (hT : 1 < T) (hU : 0 ≤ U) (hUR : U < R) {n : ℕ} (hn : 0 < n)
    (hbudget : (T * Real.log T / (2 * Real.pi) / n) *
      (positiveGapMass T R - positiveGapMass T U) < 1) :
    centeredSampledGapBand T U R n < 1 ↔ ∀ ρ ∈ cutoff T, ρ.re = 1 / 2 := by
  obtain ⟨hlo, hhi⟩ := abs_lt.mp
    ((abs_centeredSampledGapBand_sub_collision_le hT hU hUR hn).trans_lt hbudget)
  constructor
  · intro h ρ hρ
    by_contra hoff
    have hc : (2 : ℝ) ≤ distinctZeroCollision T := by
      exact_mod_cast two_le_distinctZeroCollision_of_off_line hρ hoff
    linarith only [hlo, h, hc]
  · intro hall
    have hc := (collision_eq_analyticPairCount_iff T).mpr hall
    have hzero : distinctZeroCollision T = 0 := by
      have he := collision_eq_analytic_add_distinctZeroCollision T
      omega
    simpa only [hzero, Nat.cast_zero, sub_zero] using hhi

/-- One unconditional logarithmic mesh prescription works for any fixed
band. The cofinal strict inequality is an absolute signed-gap RH test. -/
theorem exists_cofinal_cauchyGapBand_critical_line_iff_RH :
    ∃ C : ℝ, 0 < C ∧ ∀ U R : ℝ, 0 ≤ U → U < R →
      ((∀ H : ℝ, ∃ T : ℝ, H ≤ T ∧
        centeredSampledGapBand T U R (cauchyGapMesh C T) < 1) ↔ RiemannHypothesis) := by
  obtain ⟨C, hC, hbound⟩ := exists_eventually_positiveGapMass_mul_mainTerm_le
  refine ⟨C, hC, fun U R hU hUR => ?_⟩
  have he : ∀ᶠ T : ℝ in atTop,
      (centeredSampledGapBand T U R (cauchyGapMesh C T) < 1 ↔
        ∀ ρ ∈ cutoff T, ρ.re = 1 / 2) := by
    filter_upwards [hbound R, eventually_gt_atTop (1 : ℝ)] with T hbound hT
    let D := T * Real.log T / (2 * Real.pi)
    let n := cauchyGapMesh C T
    have hn : 0 < n := Nat.succ_pos _
    have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hD : 0 ≤ D :=
      div_nonneg (mul_nonneg (zero_lt_one.trans hT).le (Real.log_pos hT).le) (by positivity)
    have hmesh : C * (Ncount 0 T : ℝ) * Real.log (T + 3) < (n : ℝ) :=
      (Nat.le_ceil _).trans_lt (by
        dsimp [n, cauchyGapMesh]
        exact_mod_cast Nat.lt_succ_self _)
    apply centered_sampled_gap_band_critical_line_iff hT hU hUR hn
    change D / n * (positiveGapMass T R - positiveGapMass T U) < 1
    calc
      _ ≤ D / n * positiveGapMass T R :=
        mul_le_mul_of_nonneg_left (sub_le_self _ (positiveGapMass_nonneg hT U))
          (div_nonneg hD hn'.le)
      _ = (D * positiveGapMass T R) / n := by ring
      _ < 1 := (div_lt_iff₀ hn').mpr (by simpa only [one_mul] using hbound.trans_lt hmesh)
  obtain ⟨H₀, hH₀⟩ := eventually_atTop.mp he
  rw [← MontgomeryFormFactor.cofinal_fejer_critical_line_iff_RH,
    MontgomeryFormFactor.cofinal_fejer_critical_line_iff]
  constructor
  · intro h H ρ hρ
    obtain ⟨T, hT, hs⟩ := h (max H H₀)
    have ht := (le_max_right H H₀).trans hT
    obtain ⟨hz, hi, hheight⟩ := mem_cutoff.mp hρ
    exact (hH₀ T ht).mp hs ρ
      (mem_cutoff.mpr ⟨hz, hi, hheight.trans ((le_max_left H H₀).trans hT)⟩)
  · intro h H
    let T := max H H₀
    exact ⟨T, le_max_left _ _, (hH₀ T (le_max_right _ _)).mpr (h T)⟩

end RiemannResearch.Analysis.MontgomeryPositiveGap
