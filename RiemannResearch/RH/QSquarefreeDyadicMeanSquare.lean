/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.LogTailWeights
import RiemannResearch.RH.QPolylogBlockEnergy
import RiemannResearch.RH.QPolylogTailEnergy
import RiemannResearch.RH.QSquarefreeLogResidualTail
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import RiemannResearch.RH.QHilbertConvergence
import RiemannResearch.RH.QAnnihilatorTailEscape
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Dyadic mean-square criteria for the actual squarefree correction

Source: SquarefreeShortHeadSchurResearch20261030.md, section 6.
These are conditional research reductions. The common arithmetic block envelope
remains Open. The existing limiting correction and RH consumers are used without
changing the complete squarefree dictionary or discarding any physical tail.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.QSquarefreeDyadicMeanSquare
open ZetaTwoHilbert ZetaTwoProbability QAnnihilatorTailEscape
open QSquarefreeSmoothedProjection QSquarefreeLogResidualTail QPolylogTailEnergy
open RiemannResearch.Analysis.LogTailWeights

/-- Conditional research reduction: dyadic block mean squares of the limiting
canonical response suffice; their common arithmetic envelope is Open. -/
theorem riemannHypothesis_of_dyadic_correction_meanSquare
    (m : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ j : ℕ,
      (∑ i ∈ Finset.range (2 ^ j), qSequence correction (2 ^ j + i + 1) ^ 2) ≤
        C * ((2 ^ j : ℕ) : ℝ) * (6 + Real.log ((2 ^ j : ℕ) : ℝ)) ^ (2 * m)) :
    RiemannHypothesis := by
  let k := 2 * m + 2
  have hs := weightedEnergy_summable_of_dyadic_meanSquare correction m C hC hb
  let D := ((k : ℝ) + 6) ^ k * (∑' n : ℕ, polylogWeightedEnergyTerm k correction n)
  have ht (N : ℕ) : logWeight k N * ‖tail N correction‖ ^ 2 ≤ D := by
    calc
      _ ≤ (((k : ℝ) + 6) ^ k * polylogTailProfile k N) * ‖tail N correction‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (logWeight_le_polylogTailProfile k N) (sq_nonneg _)
      _ = ((k : ℝ) + 6) ^ k * (polylogTailProfile k N * ‖tail N correction‖ ^ 2) := by ring
      _ ≤ D := mul_le_mul_of_nonneg_left (profile_mul_tail_energy_le k N correction hs)
        (pow_nonneg (by positivity : 0 ≤ (k : ℝ) + 6) k)
  exact riemannHypothesis_of_cofinal_correction_log_tail_bound k id tendsto_id D ht

/-- Each physical block may choose its own unbounded set of stages.
No common finite-stage threshold or pointwise bound is required. -/
theorem riemannHypothesis_of_frequently_dyadic_moving_meanSquare
    (m : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ j : ℕ, ∃ᶠ N : ℕ in atTop,
      (∑ i ∈ Finset.range (2 ^ j), qSequence (movingCorrection N) (2 ^ j + i + 1) ^ 2) ≤
        C * ((2 ^ j : ℕ) : ℝ) * (6 + Real.log ((2 ^ j : ℕ) : ℝ)) ^ (2 * m)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_dyadic_correction_meanSquare m C hC
  intro j
  have ht : Tendsto
      (fun N => ∑ i ∈ Finset.range (2 ^ j), qSequence (movingCorrection N) (2 ^ j + i + 1) ^ 2)
      atTop (𝓝 (∑ i ∈ Finset.range (2 ^ j), qSequence correction (2 ^ j + i + 1) ^ 2)) := by
    apply tendsto_finsetSum
    intro i hi
    exact (qSequence_tendsto_of_tendsto movingCorrection_tendsto (2 ^ j + i + 1)).pow 2
  by_contra hbad
  have hlt := lt_of_not_ge hbad
  have he := (tendsto_order.1 ht).1 _ hlt
  obtain ⟨N, hN, hgt⟩ := ((hb j).and_eventually he).exists
  exact (not_lt_of_ge hN) hgt

end RiemannResearch.RH.QSquarefreeDyadicMeanSquare
