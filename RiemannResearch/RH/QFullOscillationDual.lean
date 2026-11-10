/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QMatchedOscillationKernel
import RiemannResearch.Analysis.ResidueOscillation
import RiemannResearch.RH.QFullDivisorProjection
import RiemannResearch.RH.QFullCRTDisplacement
import RiemannResearch.RH.QFullDisplacement
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.QHilbertConvergence
import RiemannResearch.RH.QParetoClosedProjectionComparison
import RiemannResearch.RH.NormalizedResidueExactHeadCharges
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoParetoTransfer
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Full-conductor oscillation from matched screened kernels

Source: user-provided fixed-modulus oscillation audit, 9 November 2026.
The exact identity combines both actual projection normal equations with
all signed carries, including the endpoint and escaping prime powers.
The conditional RH theorem requires a uniform product bound on expanding
physical heads, at ONE FIXED positive residue modulus. That arithmetic
estimate is Open. Finite periodicity or Hilbert convergence is not used as
its provider.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QFullOscillationDual
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QParetoClosedProjectionComparison QMatchedOscillationKernel
open QFullResidueProjection QFullDisplacement

theorem carry_screened_identity (L t k : ℕ) :
    zetaTwo * (qSequence displacement (k * L) +
      ∑ q ∈ Finset.Icc 1 (k * L + t),
        if ¬ q ∣ L ∧ q ≤ (k * L) % q + t % q
        then Pareto.mobiusDifference q (qSequence displacement) else 0) =
      inner ℝ (toPareto pResidual)
        (screenedPairKernel closure paretoClosure (k * L + t) t) := by
  rw [← QFullCRTDisplacement.displacement_carry_translation]
  exact matched_pair_identity closure paretoClosure toPareto_mem_iff qOne _ _

/-- Conditional research reduction. The computable, complete-norm kernel
product on the cofinal physical heads is Open. -/
theorem riemannHypothesis_of_head_kernel_product
    (R : ℕ → ℕ+) (hnest : ∀ i j, i ≤ j → (R i : ℕ) ∣ (R j : ℕ))
    (hcofinal : ∀ q : ℕ, 1 < q → ∃ j, q ∣ (R j : ℕ))
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (L : ℕ) (hL : 0 < L) (C : ℝ)
    (hb : ∀ j n m, 0 < n → 0 < m → n ≤ H j → m ≤ H j →
      n % L = m % L →
      ‖toPareto (qOne - QFullDivisorProjection.pOptimizer (R j))‖ *
        ‖screenedPairKernel (QSquarefreeLatticePackets.divisorStage (R j : ℕ))
          (QFullDivisorProjection.paretoStage (R j)) n m‖ ≤ zetaTwo * C) :
    RiemannHypothesis := by
  apply QFullCRTDisplacement.riemannHypothesis_of_finite_residue_oscillation L hL C
  apply RiemannResearch.Analysis.ResidueOscillation.bound_of_expanding_head_limit
    (fun j n => qSequence (QFullDivisorProjection.displacement (R j)) n)
    _ L C H hH
  · intro n
    exact qSequence_tendsto_of_tendsto
      (QFullDivisorProjection.displacement_tendsto R hnest hcofinal) n
  · intro j n m hn hm hjn hjm hnm
    have h := matched_pair_bound
      (QSquarefreeLatticePackets.divisorStage (R j : ℕ))
      (QFullDivisorProjection.paretoStage (R j))
      (QFullDivisorProjection.toPareto_mem_stage_iff (R j)) qOne n m
    have hbound := h.trans (hb j n m hn hm hjn hjm hnm)
    change zetaTwo * |qSequence (QFullDivisorProjection.displacement (R j)) n -
      qSequence (QFullDivisorProjection.displacement (R j)) m| ≤ zetaTwo * C at hbound
    nlinarith [zetaTwo_pos]

/-- A concrete higher prime power survives a period divisible by 2, 3, and 5. -/
theorem prime_power_escape_example :
    ¬ (8 : ℕ) ∣ 60 ∧
      (8 : ℕ) ≤ 60 % 8 + 4 % 8 ∧
      Pareto.mobiusDifference 8 (ArithmeticCumulative.residueFraction 8) = -1 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  simpa using Pareto.mobiusDifference_residueFraction 8 8 (by norm_num)

/-- The endpoint and carry have opposite signs and neither can be dropped. -/
theorem endpoint_carry_cancellation_example :
    ArithmeticCumulative.residueFraction 8 60 = (1 / 2 : ℝ) ∧
    ArithmeticCumulative.residueFraction 8 64 -
      ArithmeticCumulative.residueFraction 8 4 = (1 / 2 : ℝ) + (-1) := by
  norm_num [ArithmeticCumulative.residueFraction]

end RiemannResearch.RH.QFullOscillationDual
