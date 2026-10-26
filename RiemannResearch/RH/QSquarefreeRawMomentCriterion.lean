/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeRawSourceBounds
import RiemannResearch.RH.QSquarefreeMovingHeadEnergy
import RiemannResearch.RH.QReciprocalWeightedEnergy
import RiemannResearch.RH.QHeadTailLayerEnergy
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import RiemannResearch.RH.QTriangularCharge
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.QHeadCrossMoments
import RiemannResearch.RH.QAnnihilatorTailEscape
import RiemannResearch.RH.QPolylogTailEnergy
import RiemannResearch.RH.QPolylogMovingHeadEnergy
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QShiftedReciprocalBounds
import RiemannResearch.RH.QSquarefreeResidualTail
import RiemannResearch.RH.QSquarefreeLogResidualTail
import RiemannResearch.RH.QHilbertConvergence
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.Analysis.LogTailWeights
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Raw positive moments and the actual squarefree correction

Source: the user's RawSourceBoundsResearch20261026 handoff. These are
independent derivations from the exact signed layer identity. The comparison
estimates are unconditional. The boundedness and strict relative-gap premises
in the RH reductions remain Open; neither is asserted here.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QSquarefreeRawMomentCriterion
open ZetaTwoHilbert ZetaTwoOptimizerStage QShiftedReciprocal
open QAnnihilatorTailEscape QHeadCrossMoments QPolylogTailEnergy
open QSquarefreeSmoothedProjection QSquarefreeRawSourceBounds
open QSquarefreeMovingHeadEnergy
open RiemannResearch.Analysis.LogTailWeights

theorem raw_source_layer_le (N H : ℕ) :
    cappedTailEnergy 2 H (B (residual N)) ≤ ‖residual N‖ ^ 2 / 256 :=
  (cappedTailEnergy_le_total 2 H (B (residual N))
    (reciprocal_weightedEnergy_summable (residual N))).trans
      (reciprocal_weightedEnergy_le (residual N))

theorem raw_positiveCrossVariation_sub_layer_abs_le (N H : ℕ) :
    |positiveCrossVariation 2 H (movingCorrection N)
      (B (residual N) - movingCorrection N) -
        cappedTailEnergy 2 H (movingCorrection N)| ≤ ‖residual N‖ ^ 2 / 256 := by
  have h := positiveCrossVariation_sub_layer_B_le H
    (movingCorrection N) (residual N) (raw_remainder_orthogonal N)
  have hq := movingCorrection_norm_le_quarter N
  have hs := mul_le_mul hq hq (norm_nonneg (movingCorrection N))
    (by positivity : 0 ≤ (1 / 4 : ℝ) * ‖residual N‖)
  nlinarith

theorem raw_positiveCrossVariation_sub_layer_sq_le (N H : ℕ) :
    (positiveCrossVariation 2 H (movingCorrection N)
      (B (residual N) - movingCorrection N) -
        cappedTailEnergy 2 H (movingCorrection N)) ^ 2 ≤
      cappedTailEnergy 2 H (movingCorrection N) * ‖residual N‖ ^ 2 / 256 := by
  have hx : 0 ≤ cappedTailEnergy 2 H (movingCorrection N) := by
    apply Finset.sum_nonneg
    intro t ht
    exact mul_nonneg
      (sub_nonneg.mpr (polylogTailProfile_monotone 2 (Nat.le_succ t)))
      (sq_nonneg _)
  have h := positiveCrossVariation_sub_layer_sq_le 2 H
    (movingCorrection N) (B (residual N)) (raw_remainder_orthogonal N)
  have hs := mul_le_mul_of_nonneg_left (raw_source_layer_le N H) hx
  calc
    _ ≤ _ := h
    _ ≤ _ := hs
    _ = _ := by ring

theorem residual_zero_of_frequently_raw_positive_bound
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop) (C : ℝ)
    (hb : ∃ᶠ N : ℕ in atTop,
      positiveCrossVariation 2 (H N) (movingCorrection N)
        (B (residual N) - movingCorrection N) ≤ C) :
    limitingResidual = 0 := by
  apply residual_zero_of_frequently_moving_head_energy_bound 2 H hH (2*C+1/256)
  apply hb.mono
  intro N hN
  have he := moving_energy_le_raw_positive_variation N (H N)
  have hn := QTriangularCharge.residual_norm_le_one N
  nlinarith [norm_nonneg (residual N)]

/-- Conditional research reduction: the common positive-variation budget is Open. -/
theorem riemannHypothesis_of_frequently_raw_positive_bound
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop) (C : ℝ)
    (hb : ∃ᶠ N : ℕ in atTop,
      positiveCrossVariation 2 (H N) (movingCorrection N)
        (B (residual N) - movingCorrection N) ≤ C) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_frequently_moving_head_energy_bound 2 H hH (2*C+1/256)
  apply hb.mono
  intro N hN
  have he := moving_energy_le_raw_positive_variation N (H N)
  have hn := QTriangularCharge.residual_norm_le_one N
  nlinarith [norm_nonneg (residual N)]

/-- Every expanding head has divergent positive variation if the actual
limiting squarefree residual is nonzero. -/
theorem raw_positive_tendsto_atTop_of_residual_ne_zero
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (hr : limitingResidual ≠ 0) :
    Tendsto (fun N => positiveCrossVariation 2 (H N) (movingCorrection N)
      (B (residual N) - movingCorrection N)) atTop atTop := by
  apply tendsto_atTop.2
  intro C
  have hnot : ¬ ∃ᶠ N : ℕ in atTop,
      positiveCrossVariation 2 (H N) (movingCorrection N)
        (B (residual N) - movingCorrection N) ≤ C := by
    intro hb
    exact hr (residual_zero_of_frequently_raw_positive_bound H hH C hb)
  simp only [Filter.Frequently, not_not, not_le] at hnot
  exact hnot.mono (fun N hN => hN.le)

/-- A strict relative gap absorbs the positive variation even when it has no
assumed absolute bound. This is a numerical consequence, not an arithmetic gap proof. -/
theorem raw_layer_bound_of_relative_gap (N H : ℕ) (θ C : ℝ) (hθ : θ < 1)
    (hb : positiveCrossVariation 2 H (movingCorrection N)
      (B (residual N) - movingCorrection N) ≤
        θ * cappedTailEnergy 2 H (movingCorrection N) + C) :
    cappedTailEnergy 2 H (movingCorrection N) ≤ (C + ‖residual N‖ ^ 2 / 256) / (1 - θ) := by
  have ha := (abs_le.mp (raw_positiveCrossVariation_sub_layer_abs_le N H)).1
  apply (le_div_iff₀ (sub_pos.mpr hθ)).2
  nlinarith

/-- Conditional research reduction. The strict relative-gap premise is Open. -/
theorem riemannHypothesis_of_frequently_raw_relative_gap
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (θ C : ℝ) (hθ : θ < 1)
    (hb : ∃ᶠ N : ℕ in atTop,
      positiveCrossVariation 2 (H N) (movingCorrection N)
        (B (residual N) - movingCorrection N) ≤
          θ * cappedTailEnergy 2 (H N) (movingCorrection N) + C) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_frequently_moving_head_energy_bound 2 H hH
    ((C + 1 / 256) / (1 - θ))
  apply hb.mono
  intro N hN
  have he := cappedTailEnergy_exact 2 (H N) (movingCorrection N)
  have hx := raw_layer_bound_of_relative_gap N (H N) θ C hθ hN
  have hr := QTriangularCharge.residual_norm_le_one N
  have hr2 : ‖residual N‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (residual N)]
  have hden : 0 ≤ 1 - θ := (sub_pos.mpr hθ).le
  have hbound : (C + ‖residual N‖ ^ 2 / 256) / (1 - θ) ≤
      (C + 1 / 256) / (1 - θ) :=
    div_le_div_of_nonneg_right (by linarith) hden
  have hn : 0 ≤ polylogTailProfile 2 (H N) * ‖tail (H N) (movingCorrection N)‖ ^ 2 :=
    mul_nonneg (polylogTailProfile_nonneg _ _) (sq_nonneg _)
  linarith

open Filter
open scoped Topology BigOperators
open ZetaTwoHilbert ZetaTwoOptimizerStage QShiftedReciprocal
open QAnnihilatorTailEscape QHeadCrossMoments QPolylogTailEnergy
open QSquarefreeSmoothedProjection QSquarefreeResidualTail
open QSquarefreeLogResidualTail
open RiemannResearch.Analysis.LogTailWeights

theorem raw_positive_variation_fixed_head_tendsto_zero
    (hr : limitingResidual = 0) (H : ℕ) :
    Tendsto (fun N => positiveCrossVariation 2 H (movingCorrection N)
      (B (residual N) - movingCorrection N)) atTop (𝓝 0) := by
  have hb : Tendsto (fun N => ‖movingCorrection N‖ ^ 2) atTop (𝓝 0) := by
    have ht := movingCorrection_tendsto.norm.pow 2
    simpa [correction, hr] using ht
  have he : Tendsto (fun N => ‖residual N‖ ^ 2) atTop (𝓝 0) := by
    simpa [hr] using residual_tendsto.norm.pow 2
  have hmajor : Tendsto (fun N =>
      (3 / 2 * polylogTailProfile 2 H) * ‖movingCorrection N‖ ^ 2 +
        ‖residual N‖ ^ 2 / 512) atTop (𝓝 0) := by
    simpa using (hb.const_mul (3 / 2 * polylogTailProfile 2 H)).add
      (he.div_const 512)
  apply squeeze_zero _ _ hmajor
  · intro N
    apply Finset.sum_nonneg
    intro t ht
    exact mul_nonneg
      (sub_nonneg.mpr (polylogTailProfile_monotone 2 (Nat.le_succ t)))
      (le_max_right _ _)
  · intro N
    have hp := positiveCrossVariation_le_layer_add_source 2 H
      (movingCorrection N) (B (residual N)) (raw_remainder_orthogonal N)
    have hb' := cappedTailEnergy_le_profile_norm_sq 2 H (movingCorrection N)
    have hs := cappedTailEnergy_le_total 2 H (B (residual N))
      (reciprocal_weightedEnergy_summable (residual N))
    have he' := reciprocal_weightedEnergy_le (residual N)
    nlinarith

/-- Exact zero-residual characterization with a common constant but separate
cofinal stage sets for each fixed physical head. -/
theorem residual_zero_iff_fixed_head_frequently_positive_variation_bounded :
    limitingResidual = 0 ↔
      ∃ C : ℝ, ∀ H : ℕ, ∃ᶠ N : ℕ in atTop,
        positiveCrossVariation 2 H (movingCorrection N)
          (B (residual N) - movingCorrection N) ≤ C := by
  constructor
  · intro hr
    refine ⟨1, ?_⟩
    intro H
    have ht := raw_positive_variation_fixed_head_tendsto_zero hr H
    exact (ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).frequently.mono
      (fun N hN => hN.le)
  · rintro ⟨C, hC⟩
    have hh (H : ℕ) : weightedHeadEnergy 2 H correction ≤ 2 * C + 1 / 256 := by
      have hlim : Tendsto (fun N => weightedHeadEnergy 2 H (movingCorrection N))
          atTop (𝓝 (weightedHeadEnergy 2 H correction)) := by
        unfold weightedHeadEnergy
        apply tendsto_finsetSum
        intro n hn
        exact ((qSequence_tendsto_of_tendsto movingCorrection_tendsto n).pow 2).const_mul
          (polylogTailProfile 2 n * positiveQWeight n)
      have hf : ∃ᶠ N : ℕ in atTop,
          weightedHeadEnergy 2 H (movingCorrection N) ≤ 2 * C + 1 / 256 := by
        apply (hC H).mono
        intro N hN
        have henergy := moving_energy_le_raw_positive_variation N H
        have hn := QTriangularCharge.residual_norm_le_one N
        nlinarith [norm_nonneg (residual N)]
      by_contra h
      have hg := hlim.eventually (Ioi_mem_nhds (lt_of_not_ge h))
      obtain ⟨N, hN, hgt⟩ := (hf.and_eventually hg).exists
      exact (not_lt_of_ge hN) hgt
    obtain ⟨hs, htotal⟩ := weightedEnergy_summable_of_frequently_moving_head_bound
      2 (fun _ : ℕ => correction) correction tendsto_const_nhds id tendsto_id
      (2 * C + 1 / 256) (Eventually.of_forall hh).frequently
    have htail (N : ℕ) : logWeight 2 N * ‖tail N correction‖ ^ 2 ≤
        (8 : ℝ) ^ 2 * (2 * C + 1 / 256) := by
      have hprofile := (profile_mul_tail_energy_le 2 N correction hs).trans htotal
      have h1 := mul_le_mul_of_nonneg_right
        (logWeight_le_polylogTailProfile 2 N) (sq_nonneg ‖tail N correction‖)
      norm_num at h1
      nlinarith
    exact (residual_zero_iff_correction_frequently_bounded_log_scaled_tail 2).mpr
      ⟨(8 : ℝ) ^ 2 * (2 * C + 1 / 256), (Eventually.of_forall htail).frequently⟩


end RiemannResearch.RH.QSquarefreeRawMomentCriterion
