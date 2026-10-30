/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.DiscreteGronwall
import RiemannResearch.Analysis.SubpolynomialWindowGrowth
import RiemannResearch.RH.QExactHeadSubpolynomial
import RiemannResearch.RH.QCRTPredictionBudget
import RiemannResearch.RH.QCRTPeriodHeadBalance
import RiemannResearch.RH.QSquarefreeEnergyTransitions
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Conditional growth routes for the actual dense minimum-energy family

Source: user-provided innovation-space research agenda, Milestones 3 and 4.
The recurrence and its cumulative bounds are explicit Open arithmetic
providers. No unconditional subpolynomial estimate or RH proof is claimed.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QCRTOptimizerGrowth
open ZetaTwoHilbert QCRTPeriodHeadBalance QSquarefreeEnergyTransitions
open QCRTPredictionBudget
open RiemannResearch.Analysis.SubpolynomialWindow

/-- Direct actual-energy consumer, retaining any cancellation between stages. -/
theorem riemannHypothesis_of_subpolynomial_stageEnergy
    (hsub : Tendsto (fun N =>
      Real.log (1 + stageEnergy denseSchedule N) /
        Real.log ((N + 2 : ℕ) : ℝ)) atTop (𝓝 0)) : RiemannHypothesis := by
  let C : ℕ → ℝ := fun N => 1 + 2 * stageEnergy denseSchedule N
  have henergy (N : ℕ) : 0 ≤ stageEnergy denseSchedule N := sq_nonneg _
  have hC (N : ℕ) : 0 ≤ C N := by dsimp [C]; positivity [henergy N]
  have hn : Tendsto (fun N : ℕ => ((N + 2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hcsub := relativeLog_tendsto_zero_of_scaled_budget C
    (stageEnergy denseSchedule) (fun N => ((N + 2 : ℕ) : ℝ)) 2
    (by norm_num) hC henergy hn
    (Eventually.of_forall (fun N => by dsimp [C]; linarith)) hsub
  apply QExactHeadSubpolynomial.riemannHypothesis_of_cofinal_exact_head_subpolynomial
    trial (fun N => N + 2) C hn trial_legal trial_head hC
  · intro N
    have hnorm := norm_sub_le qOne (trial N)
    rw [qOne_norm] at hnorm
    change ‖qOne - trial N‖ ^ 2 ≤ (1 + 2 * ‖trial N‖ ^ 2) + 1
    nlinarith [norm_nonneg (qOne - trial N), norm_nonneg (trial N),
      sq_nonneg (‖trial N‖ - 1)]
  · exact hcsub

/-- Conditional research reduction. The displayed actual recurrence and the
two relative growth estimates remain Open until arithmetic providers are proved. -/
theorem riemannHypothesis_of_stageEnergy_gronwall
    (α β : ℕ → ℝ) (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i)
    (hstep : ∀ i, stageEnergy denseSchedule (i + 1) ≤
      (1 + α i) * stageEnergy denseSchedule i + β i)
    (hlogα : Tendsto
      (fun N => (∑ i ∈ Finset.range N, α i) / Real.log ((N + 2 : ℕ) : ℝ))
      atTop (𝓝 0))
    (hlogβ : Tendsto
      (fun N => Real.log (1 + ∑ i ∈ Finset.range N, β i) /
        Real.log ((N + 2 : ℕ) : ℝ)) atTop (𝓝 0)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_subpolynomial_stageEnergy
  exact RiemannResearch.Analysis.DiscreteGronwall.relativeLog_tendsto_zero
    (stageEnergy denseSchedule) α β (fun N => ((N + 2 : ℕ) : ℝ))
    (fun _ => sq_nonneg _) hα hβ hstep
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)) hlogα hlogβ

end RiemannResearch.RH.QCRTOptimizerGrowth


namespace RiemannResearch.RH.QCRTOptimizerGrowth
open ZetaTwoHilbert QCRTPeriodHeadBalance QSquarefreeEnergyTransitions
open QCRTPredictionBudget
open RiemannResearch.Analysis.SubpolynomialWindow

/-- A cofinal sequence of physical heads suffices; interpolation estimates
between those heads are unnecessary. The energy limit is an Open provider. -/
theorem riemannHypothesis_of_cofinal_subpolynomial_stageEnergy
    (S : ℕ → ℕ) (hS : Tendsto S atTop atTop)
    (hsub : Tendsto (fun N =>
      Real.log (1 + stageEnergy denseSchedule (S N)) /
        Real.log ((S N + 2 : ℕ) : ℝ)) atTop (𝓝 0)) : RiemannHypothesis := by
  let C : ℕ → ℝ := fun N => 1 + 2 * stageEnergy denseSchedule (S N)
  have henergy (N : ℕ) : 0 ≤ stageEnergy denseSchedule (S N) := sq_nonneg _
  have hC (N : ℕ) : 0 ≤ C N := by dsimp [C]; linarith [henergy N]
  have hn : Tendsto (fun N : ℕ => ((S N + 2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 2).comp hS)
  have hcsub := relativeLog_tendsto_zero_of_scaled_budget C
    (fun N => stageEnergy denseSchedule (S N)) (fun N => ((S N + 2 : ℕ) : ℝ)) 2
    (by norm_num) hC henergy hn
    (Eventually.of_forall (fun N => by dsimp [C]; linarith)) hsub
  apply QExactHeadSubpolynomial.riemannHypothesis_of_cofinal_exact_head_subpolynomial
    (fun N => trial (S N)) (fun N => S N + 2) C hn
    (fun N => trial_legal (S N)) (fun N => trial_head (S N)) hC
  · intro N
    have hnorm := norm_sub_le qOne (trial (S N))
    rw [qOne_norm] at hnorm
    change ‖qOne - trial (S N)‖ ^ 2 ≤ (1 + 2 * ‖trial (S N)‖ ^ 2) + 1
    nlinarith [norm_nonneg (qOne - trial (S N)), norm_nonneg (trial (S N)),
      sq_nonneg (‖trial (S N)‖ - 1)]
  · exact hcsub
end RiemannResearch.RH.QCRTOptimizerGrowth
