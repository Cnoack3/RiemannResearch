/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/

import RiemannResearch.Analysis.ActualZeroCountNormalization
import RiemannResearch.Analysis.MontgomeryGapPrescribedMesh
import RiemannResearch.Analysis.MontgomeryLocalMass
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # An unconditional prescribed mesh from Cauchy row bounds

The centered test of the Goldston–Lee–Schettler–Suriajaya triangle needs a
bound on the number of positive gaps at its width. The checked Cauchy row
estimate provides that bound at every fixed width and gives a prescribed
mesh without a short-window second-moment premise.
-/

noncomputable section
open Filter MeasureTheory Zeta23
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate MontgomeryPoisson MontgomeryLocalMass

/-- At every fixed width the raw number of positive pairs is eventually
bounded by a constant times the number of copies times the Cauchy row bound.
The constant is independent of the unfolded width. -/
theorem exists_eventually_positiveGapMass_mul_mainTerm_le :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, ∀ᶠ T : ℝ in atTop,
      (T * Real.log T / (2 * Real.pi)) * positiveGapMass T R ≤
        C * (Ncount 0 T : ℝ) * Real.log (T + 3) := by
  obtain ⟨B, hB, hrow⟩ := exists_actual_cauchy_row_bound
  refine ⟨2 * B, by positivity, fun R => ?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (Real.pi * R)] with T hT hlog
  let D := T * Real.log T / (2 * Real.pi)
  let L := Real.log T / (2 * Real.pi)
  have hT0 := zero_lt_one.trans hT
  have hlog0 := Real.log_pos hT
  have hD : 0 < D := by dsimp [D]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hR : R ≤ L * 2 := by
    dsimp [L]
    have h := (le_div_iff₀ Real.pi_pos).mpr (by simpa [mul_comm] using hlog)
    calc
      R ≤ Real.log T / Real.pi := h
      _ = _ := by ring
  have hentry (i j : Copies T) :
      (if 0 < L * (copyOrdinate T j - copyOrdinate T i) ∧
        L * (copyOrdinate T j - copyOrdinate T i) ≤ R then (1 : ℝ) else 0) ≤
        2 * cauchyWeight (copyOrdinate T i - copyOrdinate T j) := by
    split_ifs with h
    · let d := copyOrdinate T j - copyOrdinate T i
      have hd0 : 0 < d := (mul_pos_iff_of_pos_left hL).mp h.1
      have hd2 : d ≤ 2 := le_of_mul_le_mul_left (h.2.trans hR) hL
      have hdSq : d ^ 2 ≤ 4 := by nlinarith only [mul_nonneg hd0.le (sub_nonneg.mpr hd2), hd2]
      rw [show copyOrdinate T i - copyOrdinate T j = -d by dsimp [d]; ring,
        cauchyWeight_neg, cauchyWeight, ← mul_div_assoc]
      apply (le_div_iff₀ (by positivity)).mpr
      linarith only [hdSq]
    · exact mul_nonneg (by norm_num) (cauchyWeight_nonneg _)
  change D * ((∑ i : Copies T, ∑ j : Copies T,
    if 0 < L * (copyOrdinate T j - copyOrdinate T i) ∧
      L * (copyOrdinate T j - copyOrdinate T i) ≤ R then (1 : ℝ) else 0) / D) ≤ _
  rw [mul_comm D, div_mul_cancel₀ _ hD.ne']
  calc
    _ ≤ ∑ i : Copies T, ∑ j : Copies T,
        2 * cauchyWeight (copyOrdinate T i - copyOrdinate T j) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hentry i j
    _ ≤ ∑ _i : Copies T, 2 * (B * Real.log (T + 3)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hrow T hT0.le (copyOrdinate T i)) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, card_copies, nsmul_eq_mul]; ring

/-- The fixed-width sample count prescribed by the unconditional logarithmic
row bound. -/
def cauchyGapMesh (C T : ℝ) : ℕ :=
  ⌈C * (Ncount 0 T : ℝ) * Real.log (T + 3)⌉₊ + 1

/-- At every fixed width the centered test with the prescribed sample count
is eventually equivalent to criticality of the entire finite cutoff. -/
theorem exists_eventually_cauchyGapMesh_critical_line_iff :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R → ∀ᶠ T : ℝ in atTop,
      (centeredSampledGapStatistic T R (cauchyGapMesh C T) < 1 ↔
        ∀ ρ ∈ cutoff T, ρ.re = 1 / 2) := by
  obtain ⟨C, hC, hbound⟩ := exists_eventually_positiveGapMass_mul_mainTerm_le
  refine ⟨C, hC, fun R hR => ?_⟩
  filter_upwards [hbound R, eventually_gt_atTop (1 : ℝ)] with T hbound hT
  let D := T * Real.log T / (2 * Real.pi)
  let n := cauchyGapMesh C T
  have hn : 0 < n := Nat.succ_pos _
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hD : 0 ≤ D := by
    dsimp [D]
    exact div_nonneg (mul_nonneg (zero_lt_one.trans hT).le (Real.log_pos hT).le) (by positivity)
  have hmesh : C * (Ncount 0 T : ℝ) * Real.log (T + 3) < (n : ℝ) :=
    (Nat.le_ceil _).trans_lt (by
      dsimp [n, cauchyGapMesh]
      exact_mod_cast Nat.lt_succ_self _)
  apply centered_sampled_gap_critical_line_iff hT hR hn
  change D / n * (positiveGapMass T R - positiveGapMass T 0) < 1
  calc
    _ ≤ D / n * positiveGapMass T R :=
      mul_le_mul_of_nonneg_left (sub_le_self _ (positiveGapMass_nonneg hT 0))
        (div_nonneg hD hn'.le)
    _ = (D * positiveGapMass T R) / n := by ring
    _ < 1 := (div_lt_iff₀ hn').mpr (by simpa only [one_mul] using hbound.trans_lt hmesh)

/-- The absolute signed-gap test at any fixed positive width is equivalent to
RH when it holds on cofinally many cutoffs. No analytic moment premise enters. -/
theorem exists_cofinal_cauchyGapMesh_critical_line_iff_RH :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R →
      ((∀ H : ℝ, ∃ T : ℝ, H ≤ T ∧
        centeredSampledGapStatistic T R (cauchyGapMesh C T) < 1) ↔ RiemannHypothesis) := by
  obtain ⟨C, hC, he⟩ := exists_eventually_cauchyGapMesh_critical_line_iff
  refine ⟨C, hC, fun R hR => ?_⟩
  obtain ⟨H₀, hH₀⟩ := eventually_atTop.mp (he R hR)
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

/-- A finite mesh misses only the left-endpoint quadrature remainder. Its
normalized contribution is bounded by twice the endpoint gap mass per cell. -/
theorem sampled_gap_deficit_sub_bounds {T R : ℝ} {n : ℕ}
    (hT : 1 < T) (hR : 0 < R) (hn : 0 < n) :
    0 ≤ sampledIntegratedGapDeficit T R n - integratedGapDeficit T R ∧
      sampledIntegratedGapDeficit T R n - integratedGapDeficit T R ≤
        (2 / (n : ℝ)) * (positiveGapMass T R - positiveGapMass T 0) := by
  have ha := integral_sub_gapMeshSum_bounds (positiveGapMass_mono hT) hR.le hn
  unfold sampledIntegratedGapDeficit integratedGapDeficit
  rw [show (2 / R) * ((∫ u in (0 : ℝ)..R, sineGapMass u) -
      gapMeshSum (positiveGapMass T) R n) - (2 / R) *
      ((∫ u in (0 : ℝ)..R, sineGapMass u) - ∫ u in (0 : ℝ)..R, positiveGapMass T u) =
    (2 / R) * ((∫ u in (0 : ℝ)..R, positiveGapMass T u) - gapMeshSum (positiveGapMass T) R n)
    by ring]
  refine ⟨mul_nonneg (by positivity) ha.1, ?_⟩
  apply (mul_le_mul_of_nonneg_left ha.2 (show 0 ≤ 2 / R by positivity)).trans_eq
  field_simp [hR.ne', (Nat.cast_pos.mpr hn : 0 < (n : ℝ)).ne']

/-- The actual finite gap-count mesh asymptotically reproduces the integrated
deficit whenever its cell count grows faster than the Cauchy logarithmic row
bound. No estimate for the limiting two-point statistic is used. -/
theorem sampled_gap_deficit_sub_tendsto_zero {R : ℝ} (hR : 0 < R) (n : ℝ → ℕ)
    (hn : ∀ᶠ T in atTop, 0 < n T)
    (hrate : Tendsto (fun T : ℝ => Real.log (T + 3) / (n T : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => sampledIntegratedGapDeficit T R (n T) - integratedGapDeficit T R)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_eventually_positiveGapMass_mul_mainTerm_le
  have ht := tendsto_count_div_mainTerm.mul hrate
  have upper := ht.const_mul (2 * C)
  simp only [mul_zero] at upper
  apply squeeze_zero' _ _ upper
  · filter_upwards [eventually_gt_atTop (1 : ℝ), hn] with T hT hnT
    exact (sampled_gap_deficit_sub_bounds hT hR hnT).1
  · filter_upwards [eventually_gt_atTop (1 : ℝ), hn, hbound R] with T hT hnT hb
    let D := T * Real.log T / (2 * Real.pi)
    have hD : 0 < D := div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
    have hc : positiveGapMass T R ≤ C * (Ncount 0 T : ℝ) * Real.log (T+3) / D :=
      (le_div_iff₀ hD).mpr (by rw [mul_comm _ D]; exact hb)
    have hpos : 0 ≤ 2 / (n T : ℝ) := by positivity
    calc
      _ ≤ _ := (sampled_gap_deficit_sub_bounds hT hR hnT).2
      _ ≤ (2 / (n T : ℝ)) * (C * (Ncount 0 T : ℝ) * Real.log (T+3) / D) :=
        mul_le_mul_of_nonneg_left ((sub_le_self _ (positiveGapMass_nonneg hT 0)).trans hc) hpos
      _ = _ := by dsimp only [D]; ring

/-- A mesh with an explicit logarithm-squared sample count. -/
def logSquareGapMesh (T : ℝ) : ℕ := ⌈(Real.log (T + 3)) ^ 2⌉₊ + 1

theorem log_div_logSquareGapMesh_tendsto_zero :
    Tendsto (fun T : ℝ => Real.log (T + 3) / (logSquareGapMesh T : ℝ)) atTop (𝓝 0) := by
  have ht : Tendsto (fun T : ℝ => T + 3) atTop atTop :=
    tendsto_atTop_add_const_right atTop 3 tendsto_id
  have hlog := Real.tendsto_log_atTop.comp ht
  have hinv := tendsto_inv_atTop_zero.comp hlog
  change Tendsto (fun T : ℝ => (Real.log (T+3))⁻¹) atTop (𝓝 0) at hinv
  apply squeeze_zero' _ _ hinv
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    exact div_nonneg (Real.log_nonneg (by linarith)) (Nat.cast_nonneg _)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    have hl : 0 < Real.log (T+3) := Real.log_pos (by linarith)
    have hn : 0 < (logSquareGapMesh T : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos _)
    have hs : (Real.log (T+3)) ^ 2 ≤ (logSquareGapMesh T : ℝ) :=
      (Nat.le_ceil _).trans (by unfold logSquareGapMesh; push_cast; linarith)
    rw [inv_eq_one_div, div_le_div_iff₀ hn hl]
    simpa only [← sq, one_mul] using hs

end RiemannResearch.Analysis.MontgomeryPositiveGap
