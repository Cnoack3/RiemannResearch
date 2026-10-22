/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.GainBudgetConsumer
import RiemannResearch.RH.QRationalStageGain
import RiemannResearch.RH.QRationalMinimumLimit
import RiemannResearch.RH.QSquarefreePrimorialCofinality
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Order.Monotone.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith

/-!
# Conditional exhaustion from actual rational gain providers

Source: user-provided signed-tail and metric-refinement handoff, 20 October 2026,
Priority 2. The arithmetic lower bound is retained as an explicit hypothesis;
no such provider is constructed here.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.QRationalCoprimeTail
open ZetaTwoProbability ZetaTwoHilbert
open QSquarefreePrimorialCofinality QSquarefreeInverseCapacity
open Pareto.SquarefreeStageExhaustion

/-- Conditional research reduction: a divergent cumulative fraction of residual
energy, with summable error, exhausts the actual complete-Q defect. The hypothesis
`hprovider` is the still-open arithmetic estimate. -/
theorem qOne_mem_closure_of_chain_gain_provider
    (σ k : ℕ → ℕ) (c e : ℕ → ℝ)
    (hσ : Monotone σ) (hcofinal : Tendsto σ atTop atTop)
    (hperiod : ∀ j, primorialPeriod (σ (j + 1)) = primorialPeriod (σ j) * k j)
    (hk : ∀ j, 14 ≤ k j)
    (hc : ∀ j, 0 ≤ c j) (he : ∀ j, 0 ≤ e j)
    (hprovider : ∀ j,
      c j * rationalMinimum (primorialPeriod (σ j)) - e j ≤
        rationalGap (primorialPeriod (σ j))
          (qSequence (rationalMinimizer (primorialPeriod (σ j)))) / 2 +
        rationalStageDisplacement (σ j) (σ (j + 1)))
    (hdiv : Tendsto (fun N => ∑ j ∈ Finset.range N, c j) atTop atTop)
    (hsum : Summable e) :
    qOne ∈ qSquarefreeCRTSpan.topologicalClosure := by
  have hR (j : ℕ) : 0 ≤ rationalMinimum (primorialPeriod (σ j)) :=
    (mul_nonneg zetaTwo_pos.le (primorialError_pos (σ j)).le).trans
      (rationalMinimum_lower (σ j))
  have hmono : Antitone (fun j => rationalMinimum (primorialPeriod (σ j))) := by
    apply antitone_nat_of_succ_le
    intro j
    exact rationalMinimum_le_of_large_refinement (hσ (Nat.le_succ j))
      (hperiod j) (le_trans (by decide : 7 ≤ 14) (hk j))
  have hzero := Analysis.GainBudget.limit_eq_zero_of_provider
    hR hmono (rationalMinimum_tendsto.comp hcofinal)
    hc he hprovider (rationalMinimum_chain_budget σ k hσ hperiod hk) hdiv hsum
  apply rationalMinimum_tendsto_zero_iff.mp
  simpa only [hzero] using rationalMinimum_tendsto

end RiemannResearch.RH.QRationalCoprimeTail
