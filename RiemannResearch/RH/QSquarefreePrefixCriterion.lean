/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreePrefixAbel
import RiemannResearch.RH.QSquarefreeHeadLeakage
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import RiemannResearch.RH.QSquarefreePrefixDispersion
import RiemannResearch.RH.QSquarefreeShortHeadBlocks
import RiemannResearch.RH.QSquarefreeShortHeadCriterion
import RiemannResearch.RH.QSquarefreeShortHeadResponse
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith

/-!
# Compensated prefix block criterion for RH

Source: the user-requested continuation of `SquarefreeShortHeadLean20261031.md`.
This is an exact reformulation of the existing short-head block criterion,
not a discharge of its common arithmetic bound. Every substantive hypothesis
is retained in the conditional theorem type.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QSquarefreePrefixCriterion
open QSquarefreePrefixAbel QSquarefreeShortHeadResponse QSquarefreeShortHeadCriterion
open QSquarefreeShortHeadBlocks

/-- Exact reformulation of the short-head block budget. The arithmetic bound
is still Open; the signed dispersion is kept on the right-hand side. -/
theorem block_bound_iff (N H M : ℕ) (R : ℝ) :
    (∑ i ∈ Finset.range M, response N H (M + i + 1) ^ 2) ≤ R ↔
      (∑ i ∈ Finset.range M,
        abelMass H (M + i + 1) * abelEnergy N H (M + i + 1)) ≤
        R + ∑ i ∈ Finset.range M, abelDispersion N H (M + i + 1) := by
  have he := block_energy_dispersion_exact N H M
  constructor <;> intro h <;> linarith

/-- Conditional research reduction for the complete canonical squarefree
dictionary. A common dyadic compensated-prefix bound remains an Open provider.
Each block may use its own unbounded set of stages. -/
theorem riemannHypothesis_of_frequently_dyadic_prefix_dispersion
    (m : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ j : ℕ, ∃ᶠ N : ℕ in atTop,
      (∑ i ∈ Finset.range (2 ^ j),
        abelMass (logarithmicCutoff (2 ^ j)) (2 ^ j + i + 1) *
          abelEnergy N (logarithmicCutoff (2 ^ j)) (2 ^ j + i + 1)) ≤
        C * ((2 ^ j : ℕ) : ℝ) * (6 + Real.log ((2 ^ j : ℕ) : ℝ)) ^ (2 * m) +
          ∑ i ∈ Finset.range (2 ^ j),
            abelDispersion N (logarithmicCutoff (2 ^ j)) (2 ^ j + i + 1)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_frequently_dyadic_shortHead_meanSquare m C hC
  intro j
  exact (hb j).mono (fun N hN =>
    (block_bound_iff N (logarithmicCutoff (2 ^ j)) (2 ^ j) _).mpr hN)

open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage QShiftedReciprocal
open QSquarefreeHeadLeakage

/-- Conditional research reduction. Open: the actual cofinal source-weighted
compression-defect budget, with one common constant and logarithmic exponent. -/
theorem riemannHypothesis_of_frequently_dyadic_head_leakage
    (m : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ j : ℕ, ∃ᶠ N : ℕ in atTop,
      (((2 ^ j : ℕ) : ℝ) *
        (‖leakage N (logarithmicCutoff (2 ^ j)) (B (residual N))‖ ^ 2 +
          ‖leakage N (logarithmicCutoff (2 ^ j)) (residual N)‖ ^ 2 /
            (((2 ^ j : ℕ) : ℝ) + 2) ^ 2)) ≤
        C * (6 + Real.log ((2 ^ j : ℕ) : ℝ)) ^ (2 * m)) :
    RiemannHypothesis := by
  have hZ := zetaTwo_pos
  apply riemannHypothesis_of_frequently_dyadic_prefix_dispersion
    m (8 * zetaTwo * C)
    (by positivity)
  intro j
  apply (hb j).mono
  intro N hN
  have hM : 0 < (2 : ℕ) ^ j := pow_pos (by norm_num) j
  have h := compensated_block_le_leakage N (logarithmicCutoff (2 ^ j)) (2 ^ j)
    (logarithmicCutoff_le _ hM)
  rw [Finset.sum_sub_distrib] at h
  have hh := mul_le_mul_of_nonneg_left hN
    (show 0 ≤ 8 * zetaTwo * ((2 ^ j : ℕ) : ℝ) by positivity)
  nlinarith only [h, hh]

end RiemannResearch.RH.QSquarefreePrefixCriterion
