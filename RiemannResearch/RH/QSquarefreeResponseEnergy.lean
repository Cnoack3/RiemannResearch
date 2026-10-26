/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeTailResponse
import RiemannResearch.RH.QPolylogMovingHeadEnergy
import RiemannResearch.RH.QTriangularCharge
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Weighted energy of the actual squarefree response components

Source: the user's stronger constant-energy bound request, 26 October 2026.
The exact weighted response split retains its signed cross term. The zero-head
component has a common energy budget on quadratic windows and its energy
vanishes uniformly. The complementary head response remains uncontrolled;
these results do not prove the constant-energy criterion for RH.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QSquarefreeResponseEnergy
open ZetaTwoHilbert ZetaTwoOptimizerStage
open QPolylogTailEnergy QSquarefreeTailResponse QSquarefreeSmoothedProjection
open QAnnihilatorTailEscape QFiniteSupportDualCriterion
open RiemannResearch.Analysis.LogTailWeights

/-- The exact response split retains the signed weighted cross term. -/
theorem movingCorrection_weighted_energy_exact (k N L H : ℕ) :
    weightedHeadEnergy k H (movingCorrection N) =
      weightedHeadEnergy k H (headResponse N L) +
      weightedHeadEnergy k H (tailResponse N L) +
      2 * weightedHeadCross k H (headResponse N L) (tailResponse N L) := by
  rw [response_split N L, weightedHeadEnergy_add_exact]

/-- The solved zero-head response has uniformly controlled weighted energy
through a head whose profile is quadratic in the zero-head cutoff. -/
theorem tailResponse_weighted_energy_le (k N L H : ℕ) :
    weightedHeadEnergy k H (tailResponse N L) ≤
      polylogTailProfile k H / (4 * ((L : ℝ) + 2) ^ 2) *
        ‖tail L (ZetaTwoOptimizerStage.residual N)‖ ^ 2 := by
  have hn := tailResponse_norm_le N L
  have hs := mul_self_le_mul_self (norm_nonneg (tailResponse N L)) hn
  have hs' : ‖tailResponse N L‖ ^ 2 ≤
      (1 / (2 * ((L : ℝ) + 2))) ^ 2 *
        ‖tail L (ZetaTwoOptimizerStage.residual N)‖ ^ 2 := by
    simpa only [← pow_two, mul_pow] using hs
  calc
    _ ≤ polylogTailProfile k H * ‖tailResponse N L‖ ^ 2 :=
      weightedHeadEnergy_le_profile_norm_sq k H (tailResponse N L)
    _ ≤ polylogTailProfile k H * ((1 / (2 * ((L : ℝ) + 2))) ^ 2 *
        ‖tail L (ZetaTwoOptimizerStage.residual N)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hs' (polylogTailProfile_nonneg k H)
    _ = _ := by
      have hd : (L : ℝ) + 2 ≠ 0 := by positivity
      field_simp [hd]
      ring

theorem tailResponse_weighted_energy_quadratic (k N L H : ℕ)
    (A : ℝ) (_hA : 0 ≤ A)
    (hH : (H : ℝ) ≤ A * ((L : ℝ) + 2) ^ 2) :
    weightedHeadEnergy k H (tailResponse N L) ≤
      (A / 4) * ‖tail L (ZetaTwoOptimizerStage.residual N)‖ ^ 2 := by
  have hp : polylogTailProfile k H ≤ (H : ℝ) :=
    (polylogTailProfile_le_logWeight k H).trans (logWeight_le_nat k H)
  have hd : 0 < 4 * ((L : ℝ) + 2) ^ 2 := by positivity
  have hratio : polylogTailProfile k H / (4 * ((L : ℝ) + 2) ^ 2) ≤ A / 4 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [hp, hH]
  exact (tailResponse_weighted_energy_le k N L H).trans
    (mul_le_mul_of_nonneg_right hratio (sq_nonneg _))

/-- A common numerical bound for the solved component only. -/
theorem tailResponse_weighted_energy_le_quarter (k N L H : ℕ)
    (hH : (H : ℝ) ≤ ((L : ℝ) + 2) ^ 2) :
    weightedHeadEnergy k H (tailResponse N L) ≤ (1 / 4 : ℝ) := by
  have hb := tailResponse_weighted_energy_quadratic k N L H 1 (by norm_num)
    (by simpa only [one_mul] using hH)
  have ht : ‖tail L (ZetaTwoOptimizerStage.residual N)‖ ≤ 1 :=
    (tail_norm_le L (ZetaTwoOptimizerStage.residual N)).trans
      (QTriangularCharge.residual_norm_le_one N)
  nlinarith [hb, norm_nonneg (tail L (ZetaTwoOptimizerStage.residual N))]

/-- On every quadratic window, the solved component's entire weighted
head energy vanishes uniformly in the optimizer stage and the integer weight. -/
theorem tailResponse_weighted_energy_uniform_quadratic (A ε : ℝ)
    (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ N H k : ℕ,
      (H : ℝ) ≤ A * ((L : ℝ) + 2) ^ 2 →
        weightedHeadEnergy k H (tailResponse N L) < ε := by
  have hδ : 0 < ε / (A + 1) := div_pos hε (by linarith)
  obtain ⟨L₀, hL₀⟩ := uniform_tail_tightness_of_tendsto
    ZetaTwoOptimizerStage.residual limitingResidual residual_tendsto
    (ε / (A + 1)) hδ
  refine ⟨L₀, ?_⟩
  intro L hL N H k hH
  have ht := hL₀ L hL N
  have ht0 := norm_nonneg (tail L (ZetaTwoOptimizerStage.residual N))
  have ht1 : ‖tail L (ZetaTwoOptimizerStage.residual N)‖ ≤ 1 :=
    (tail_norm_le L (ZetaTwoOptimizerStage.residual N)).trans
      (QTriangularCharge.residual_norm_le_one N)
  have ht2 : ‖tail L (ZetaTwoOptimizerStage.residual N)‖ ^ 2 ≤
      ‖tail L (ZetaTwoOptimizerStage.residual N)‖ := by nlinarith
  have hb := tailResponse_weighted_energy_quadratic k N L H A hA hH
  have hm := mul_le_mul_of_nonneg_left ht2 (show 0 ≤ A / 4 from by positivity)
  have hprod := mul_lt_mul_of_pos_left ht (show 0 < A + 1 from by linarith)
  have hcancel : (A + 1) * (ε / (A + 1)) = ε := by
    have hne : A + 1 ≠ 0 := ne_of_gt (by linarith : 0 < A + 1)
    field_simp [hne]
  rw [hcancel] at hprod
  nlinarith [hb, hm, hprod, mul_nonneg hA ht0]

/-- On a quadratic window, a head-response budget controls the full response.
No weighted orthogonality is assumed. -/
theorem movingCorrection_weighted_energy_le_twice_head_add_half (k N L H : ℕ)
    (hH : (H : ℝ) ≤ ((L : ℝ) + 2) ^ 2) :
    weightedHeadEnergy k H (movingCorrection N) ≤
      2 * weightedHeadEnergy k H (headResponse N L) + (1 / 2 : ℝ) := by
  have hs := weightedHeadEnergy_add_le k H (headResponse N L) (tailResponse N L)
  rw [← response_split N L] at hs
  have ht := tailResponse_weighted_energy_le_quarter k N L H hH
  linarith

/-- Conversely, the complementary head response obeys the same budget transfer. -/
theorem headResponse_weighted_energy_le_twice_correction_add_half (k N L H : ℕ)
    (hH : (H : ℝ) ≤ ((L : ℝ) + 2) ^ 2) :
    weightedHeadEnergy k H (headResponse N L) ≤
      2 * weightedHeadEnergy k H (movingCorrection N) + (1 / 2 : ℝ) := by
  have hs := weightedHeadEnergy_add_le k H (movingCorrection N) (-tailResponse N L)
  rw [weightedHeadEnergy_neg] at hs
  change weightedHeadEnergy k H (headResponse N L) ≤ _ at hs
  have ht := tailResponse_weighted_energy_le_quarter k N L H hH
  linarith

end RiemannResearch.RH.QSquarefreeResponseEnergy
