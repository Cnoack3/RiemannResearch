/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimePowerSieveUniform
import RiemannResearch.RH.QPrimePowerSieveTwoStage
import RiemannResearch.RH.PrimePowerTargetMellinLower
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Uniform complete-Q obstruction to all moving two-stage sieves

Source: user-provided TwoStageSieveObstructionResearch20261020.md.
The actual arithmetic providers are discharged. The lower bound has no
RH, closure, slope-separation, or bounded-variation hypothesis.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QPrimePowerSieve
open ZetaTwoHilbert ZetaTwoProbability QMellinTransfer PrimePowerTarget

/-- Uniformity includes every second cutoff, with no lower bound on the slope gap. -/
theorem sieveTwoStageVector_mellin_uniform (p : ℕ) (hp : p.Prime)
    (σ : ℝ) (hσ : (1 / 2 : ℝ) < σ) (hσ1 : σ < 1) :
    ∀ ε > 0, ∃ N : ℕ, p ≤ N ∧ ∀ H ≥ N, ∀ K ≥ H,
      ‖(σ : ℂ) * qMellin (sieveTwoStageVector p H K) σ‖ < ε := by
  intro ε hε
  have hz : 0 < ‖riemannZeta (σ : ℂ)‖ + 1 := by positivity
  obtain ⟨N, hpN, hN⟩ := sieve_intercept_uniform p hp σ (by linarith) hσ1
    (ε / (‖riemannZeta (σ : ℂ)‖ + 1)) (div_pos hε hz)
  refine ⟨N, hpN, ?_⟩
  intro H hH K hK
  rw [sieveTwoStageVector_mellin_norm_exact p H K hp (hpN.trans hH)
    ((hpN.trans hH).trans hK) σ hσ (ne_of_lt hσ1)]
  have hb := (lt_div_iff₀ hz).mp (hN H hH K hK)
  have hn := abs_nonneg (PrimeSieveSecant.intercept
    (sieveSlope (primorial H) p) (sieveSlope (primorial K) p)
    (primePowerEulerFactor p H σ) (primePowerEulerFactor p K σ))
  nlinarith

/-- The actual complete-Q error lower bound, uniform over all nondegenerate later cutoffs. -/
theorem sieveTwoStageVector_quantitative_lower (p : ℕ) (hp : p.Prime)
    (σ : ℝ) (hσ : (1 / 2 : ℝ) < σ) (hσ1 : σ < 1) :
    ∃ N : ℕ, p ≤ N ∧ ∀ H ≥ N, ∀ K, H ≤ K →
      sieveSlope (primorial H) p ≠ sieveSlope (primorial K) p →
      ((2 * σ - 1) / (4 * zetaTwo * σ ^ 2 * ((p : ℝ) ^ σ - 1) ^ 2)) *
        (H : ℝ) ^ (2 * σ - 1) ≤ ‖sieveTwoStageVector p H K - qTarget p hp.one_lt‖ ^ 2 := by
  have hden : 0 < (p : ℝ) ^ σ - 1 := sub_pos.mpr
    (Real.one_lt_rpow (by exact_mod_cast hp.one_lt) (by linarith))
  obtain ⟨N, hpN, hN⟩ := sieveTwoStageVector_mellin_uniform p hp σ hσ hσ1
    (1 / (2 * ((p : ℝ) ^ σ - 1))) (by positivity)
  refine ⟨N, hpN, ?_⟩
  intro H hH K hK hgap
  exact qTarget_head_match_quantitative_lower p hp.one_lt (sieveTwoStageVector p H K)
    σ hσ H (by have := hp.two_le; omega)
    (fun n hn => qSequence_sieveTwoStageVector_head p H K n hp (hpN.trans hH) hK hn hgap)
    (hN H hH K hK).le

/-- Every moving nondegenerate pair has divergent complete-Q norm.
No separation condition on the two positive sieve slopes is imposed. -/
theorem sieveTwoStageVector_norm_tendsto_atTop
    (p : ℕ) (hp : p.Prime) (σ : ℝ) (hσ : (1 / 2 : ℝ) < σ) (hσ1 : σ < 1)
    (H K : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (horder : ∀ᶠ j : ℕ in atTop, H j ≤ K j)
    (hgap : ∀ᶠ j : ℕ in atTop,
      sieveSlope (primorial (H j)) p ≠ sieveSlope (primorial (K j)) p) :
    Tendsto (fun j : ℕ => ‖sieveTwoStageVector p (H j) (K j)‖) atTop atTop := by
  let c : ℝ := (2 * σ - 1) /
    (4 * zetaTwo * σ ^ 2 * ((p : ℝ) ^ σ - 1) ^ 2)
  have hc : 0 < c := qTarget_obstruction_constant_pos p hp.one_lt σ hσ
  obtain ⟨N, _, hbound⟩ := sieveTwoStageVector_quantitative_lower p hp σ hσ hσ1
  have hpower : Tendsto (fun j : ℕ => (H j : ℝ) ^ (2 * σ - 1)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < 2 * σ - 1)).comp
      (tendsto_natCast_atTop_atTop.comp hH)
  apply tendsto_atTop.2
  intro b
  let B : ℝ := max b 0 + ‖qTarget p hp.one_lt‖
  have hB : 0 ≤ B := add_nonneg (le_max_right b 0) (norm_nonneg _)
  filter_upwards [hH.eventually (eventually_ge_atTop N), horder, hgap,
    hpower.eventually (eventually_ge_atTop (B ^ 2 / c))] with j hNj hHK hgapj hj
  have hscaled : B ^ 2 ≤ c * (H j : ℝ) ^ (2 * σ - 1) := by
    simpa only [mul_comm] using (div_le_iff₀ hc).mp hj
  have hlower : c * (H j : ℝ) ^ (2 * σ - 1) ≤
      ‖sieveTwoStageVector p (H j) (K j) - qTarget p hp.one_lt‖ ^ 2 :=
    hbound (H j) hNj (K j) hHK hgapj
  have herr : B ≤ ‖sieveTwoStageVector p (H j) (K j) - qTarget p hp.one_lt‖ := by
    have he0 := norm_nonneg (sieveTwoStageVector p (H j) (K j) - qTarget p hp.one_lt)
    have hsq := hscaled.trans hlower
    nlinarith
  have htri := norm_sub_le (sieveTwoStageVector p (H j) (K j)) (qTarget p hp.one_lt)
  have hb := le_max_left b 0
  dsimp only [B] at herr
  linarith


end RiemannResearch.RH.QPrimePowerSieve
