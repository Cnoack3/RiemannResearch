/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/

import RiemannResearch.Analysis.MontgomeryGapMesh
import RiemannResearch.Analysis.MontgomeryFejerCertificate
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A prescribed mesh for the absolute signed-gap certificate

The finite triangle calculation uses the normalization of Goldston, Lee,
Schettler and Suriajaya, arXiv:2503.15449v3, Section 3, Propositions 1 and 2.
Their short-window moment is the explicit analytic input for the linear mesh
bound. Centering the left and right endpoint rules gives an exact signed
quadrature correction and a two-sided error interval.
-/

noncomputable section
open Filter MeasureTheory Set Zeta23

namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate ActualZeroCollisionCertificate ActualZeroWindowVariance

/-- The midpoint of the absolute statistics from the left and right quadrature
rules. The subtracted term is half of their difference. -/
def centeredSampledGapStatistic (T R : ℝ) (n : ℕ) : ℝ :=
  let D := T * Real.log T / (2 * Real.pi)
  D * (sineHoleTriangle R + shortWindowMomentDeficit T R + sampledIntegratedGapDeficit T R n) -
    (analyticPairCount T : ℝ) - (D / n) * (positiveGapMass T R - positiveGapMass T 0)

theorem centeredSampledGapStatistic_sub_collision_eq {T R : ℝ}
    (hT : 1 < T) (hR : 0 < R) (n : ℕ) :
    let D := T * Real.log T / (2 * Real.pi)
    centeredSampledGapStatistic T R n - (distinctZeroCollision T : ℝ) =
      D * ((2 / R) * ((∫ u in (0 : ℝ)..R, positiveGapMass T u) -
          gapMeshSum (positiveGapMass T) R n)) -
        (D / n) * (positiveGapMass T R - positiveGapMass T 0) := by
  dsimp only
  unfold centeredSampledGapStatistic
  dsimp only
  rw [absolute_sampled_gap_sub_analytic_eq hT hR n]
  ring

/-- The centered rule halves the worst-case absolute error of the left rule. -/
theorem abs_centeredSampledGapStatistic_sub_collision_le {T R : ℝ}
    (hT : 1 < T) (hR : 0 < R) {n : ℕ} (hn : 0 < n) :
    |centeredSampledGapStatistic T R n - (distinctZeroCollision T : ℝ)| ≤
      (T * Real.log T / (2 * Real.pi) / n) * (positiveGapMass T R - positiveGapMass T 0) := by
  let D := T * Real.log T / (2 * Real.pi)
  have hlog := Real.log_pos hT
  have hT0 := zero_lt_one.trans hT
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨hlo, hhi⟩ := integral_sub_gapMeshSum_bounds (positiveGapMass_mono hT) hR.le hn
  have hlo' := mul_nonneg hD (mul_nonneg (by positivity : 0 ≤ 2 / R) hlo)
  have hhi' := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hhi (by positivity : 0 ≤ 2 / R)) hD
  have hscale : D * ((2 / R) * ((R / n) * (positiveGapMass T R - positiveGapMass T 0))) =
      2 * ((D / n) * (positiveGapMass T R - positiveGapMass T 0)) := by
    field_simp [hR.ne', hn']
  rw [hscale] at hhi'
  have he := centeredSampledGapStatistic_sub_collision_eq hT hR n
  dsimp only at he
  rw [he, abs_le]
  change -((D / n) * (positiveGapMass T R - positiveGapMass T 0)) ≤ _ ∧
    _ ≤ (D / n) * (positiveGapMass T R - positiveGapMass T 0)
  exact ⟨by linarith only [hlo'], by linarith only [hhi']⟩

theorem centered_sampled_gap_critical_line_iff {T R : ℝ} (hT : 1 < T) (hR : 0 < R)
    {n : ℕ} (hn : 0 < n)
    (hbudget : (T * Real.log T / (2 * Real.pi) / n) *
      (positiveGapMass T R - positiveGapMass T 0) < 1) :
    centeredSampledGapStatistic T R n < 1 ↔ ∀ ρ ∈ cutoff T, ρ.re = 1 / 2 := by
  have habs := (abs_centeredSampledGapStatistic_sub_collision_le hT hR hn).trans_lt hbudget
  obtain ⟨hlo, hhi⟩ := abs_lt.mp habs
  constructor
  · intro hs ρ hρ
    by_contra hoff
    have hc : (2 : ℝ) ≤ distinctZeroCollision T := by
      exact_mod_cast two_le_distinctZeroCollision_of_off_line hρ hoff
    linarith only [hlo, hs, hc]
  · intro hall
    have hc := (collision_eq_analyticPairCount_iff T).mpr hall
    have hzero : distinctZeroCollision T = 0 := by
      have he := collision_eq_analytic_add_distinctZeroCollision T
      omega
    simpa only [hzero, Nat.cast_zero, sub_zero] using hhi

/-- The same physical triangle at a wider window bounds the count of all
strictly positive gaps in the narrower window. -/
theorem positiveGapMass_le_of_window {T R B : ℝ}
    (hT : 1 < T) (hR : 0 ≤ R) (hRB : R ≤ B) :
    2 * (B - R) * positiveGapMass T R ≤
      actualPhysicalTriangleEnergy T (B / (Real.log T / (2 * Real.pi))) := by
  have hP := positiveGapMass_mono hT
  have hc := intervalIntegral.integral_mono_on (μ := volume) hRB
    intervalIntegrable_const hP.intervalIntegrable
    (fun u (hu : u ∈ Icc R B) => hP hu.1)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hc
  have hs := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (f := positiveGapMass T) (a := 0) (b := R) (c := B)
    hP.intervalIntegrable hP.intervalIntegrable
  have hI := intervalIntegral.integral_nonneg_of_forall (μ := volume) hR
    (positiveGapMass_nonneg hT)
  rw [physicalTriangle_eq_collision_add_positive_gaps hT (hR.trans hRB)]
  have hlog := Real.log_pos hT
  have hT0 := zero_lt_one.trans hT
  have hdiag : 0 ≤ B * ((actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi))) :=
    mul_nonneg (hR.trans hRB) (by positivity)
  linarith only [hc, hs, hI, hdiag]

/-- A short-window moment at width B supplies an eventual mesh bound at
width B/2. Every integer larger than (B + 1)D works at the same cutoff. -/
theorem eventual_centered_sampled_gap_of_shortWindowMoment
    (hm : ShortWindowSecondMomentUpper) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ᶠ T : ℝ in atTop,
      1 < T ∧ ∀ n : ℕ, (B + 1) * (T * Real.log T / (2 * Real.pi)) < (n : ℝ) →
        (centeredSampledGapStatistic T (B / 2) n < 1 ↔ ∀ ρ ∈ cutoff T, ρ.re = 1 / 2) := by
  obtain ⟨B, hB, hm⟩ := hm 1 zero_lt_one
  have hB0 := zero_lt_one.trans_le hB
  have hR : 0 < B / 2 := by positivity
  refine ⟨B, hB, ?_⟩
  filter_upwards [hm, eventually_gt_atTop (1 : ℝ)] with T hW hT
  refine ⟨hT, fun n hn => ?_⟩
  let D := T * Real.log T / (2 * Real.pi)
  have hT0 := zero_lt_one.trans hT
  have hlog := Real.log_pos hT
  have hD : 0 < D := by dsimp [D]; positivity
  change (B + 1) * D < (n : ℝ) at hn
  have hn' : 0 < (n : ℝ) := (mul_pos (by positivity) hD).trans hn
  have hgap := (positiveGapMass_le_of_window hT hR.le (by linarith)).trans hW
  have hP : positiveGapMass T (B / 2) ≤ B + 1 := by
    apply (le_of_mul_le_mul_left ?_ hB0)
    calc
      B * positiveGapMass T (B / 2) = 2 * (B - B / 2) * positiveGapMass T (B / 2) := by ring
      _ ≤ B ^ 2 + 1 * B := hgap
      _ = B * (B + 1) := by ring
  apply centered_sampled_gap_critical_line_iff hT hR (Nat.cast_pos.mp hn')
  change (D / n) * (positiveGapMass T (B / 2) - positiveGapMass T 0) < 1
  calc
    _ ≤ (D / n) * (B + 1) :=
      mul_le_mul_of_nonneg_left
        ((sub_le_self _ (positiveGapMass_nonneg hT 0)).trans hP) (by positivity)
    _ = ((B + 1) * D) / n := by ring
    _ < 1 := (div_lt_iff₀ hn').mpr (by simpa only [one_mul] using hn)

/-- Prescribed integer sample count. Its coefficient is the fixed moment width. -/
def prescribedGapMesh (B T : ℝ) : ℕ :=
  ⌈(B + 1) * (T * Real.log T / (2 * Real.pi))⌉₊ + 1

theorem cofinal_prescribed_sampled_gap_critical_line_iff_RH (hm : ShortWindowSecondMomentUpper) :
    ∃ B : ℝ, 1 ≤ B ∧
      ((∀ H : ℝ, ∃ T : ℝ, H ≤ T ∧
        centeredSampledGapStatistic T (B / 2) (prescribedGapMesh B T) < 1) ↔
        RiemannHypothesis) := by
  obtain ⟨B, hB, he⟩ := eventual_centered_sampled_gap_of_shortWindowMoment hm
  obtain ⟨H₀, hH₀⟩ := eventually_atTop.mp he
  have hmesh (T : ℝ) :
      (B + 1) * (T * Real.log T / (2 * Real.pi)) < (prescribedGapMesh B T : ℝ) := by
    exact (Nat.le_ceil _).trans_lt (by unfold prescribedGapMesh; exact_mod_cast Nat.lt_succ_self _)
  refine ⟨B, hB, ?_⟩
  rw [← MontgomeryFormFactor.cofinal_fejer_critical_line_iff_RH,
    MontgomeryFormFactor.cofinal_fejer_critical_line_iff]
  constructor
  · intro h H ρ hρ
    obtain ⟨T, hT, hs⟩ := h (max H H₀)
    have ht := (le_max_right H H₀).trans hT
    obtain ⟨hz, hi, hheight⟩ := mem_cutoff.mp hρ
    exact ((hH₀ T ht).2 _ (hmesh T)).mp hs ρ
      (mem_cutoff.mpr ⟨hz, hi, hheight.trans ((le_max_left H H₀).trans hT)⟩)
  · intro h H
    let T := max H H₀
    exact ⟨T, le_max_left _ _, ((hH₀ T (le_max_right _ _)).2 _ (hmesh T)).mpr (h T)⟩

end RiemannResearch.Analysis.MontgomeryPositiveGap
