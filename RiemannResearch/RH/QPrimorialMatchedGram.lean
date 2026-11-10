/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QPrimorialMatchedDisplacement
import RiemannResearch.RH.QCovarianceInvertibility
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The complete Gram row for the matched primorial prime test

Source: *Squarefree projection displacement and infinite CRT carries*,
9 November 2026, Section 12.1. The two inverse solves use the same divisor
index. Their Gram entries are complete Hilbert inner products in the
respective metrics.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.QPrimorialMatchedGram

open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QParetoEquivalence QParetoClosedProjectionComparison
open QSquarefreePrimorialCofinality QPrimorialMatchedDisplacement
open RiemannResearch.Analysis.FiniteHilbertGram

def paretoDivisorAtom (n : ℕ) (i : DivisorIndex n) : ThresholdHilbert :=
  toPareto (qResidue (divisorConductor n i))

theorem paretoDivisorAtom_independent (n : ℕ) :
    LinearIndependent ℝ (paretoDivisorAtom n) :=
  (QCovarianceInvertibility.qResidue_linearIndependent (divisorConductor n)
    (divisorConductor_gt_one n) (divisorConductor_injective n)).map'
      paretoEquiv.toLinearMap (LinearMap.ker_eq_bot.mpr paretoEquiv.injective)

def paretoCoefficients (n : ℕ) : DivisorIndex n → ℝ :=
  inverseCoeff (paretoDivisorAtom_independent n) (toPareto qOne)

theorem paretoCoefficients_normal (n : ℕ) (i : DivisorIndex n) :
    gram (paretoDivisorAtom n) (paretoCoefficients n) i =
      cross (paretoDivisorAtom n) (toPareto qOne) i :=
  inverseCoeff_normal (paretoDivisorAtom_independent n) (toPareto qOne) i

theorem pOptimizer_expansion (n : ℕ) :
    pOptimizer n = QCovarianceInverse.qSynthesis (divisorConductor n) (paretoCoefficients n) := by
  have hs : synthesisSpan (paretoDivisorAtom n) = paretoStage n := by
    unfold synthesisSpan paretoStage paretoDivisorAtom
    rw [← divisor_span_eq_primorialStage]
    exact (map_span_range _).symm
  have h := synthesis_inverseCoeff_eq_projection (paretoDivisorAtom_independent n) (toPareto qOne)
  have h' :
      Fintype.linearCombination ℝ (paretoDivisorAtom n) (paretoCoefficients n) =
        (paretoStage n).starProjection (toPareto qOne) := by
    simpa only [hs, paretoCoefficients] using h
  apply paretoEquiv.injective
  change toPareto (pFit (paretoStage n) qOne) =
    toParetoLinear (QCovarianceInverse.qSynthesis (divisorConductor n) (paretoCoefficients n))
  rw [toPareto_pFit, ← h', Fintype.linearCombination_apply]
  simp only [QCovarianceInverse.qSynthesis, map_sum, map_smul, paretoDivisorAtom] <;> rfl

def displacementCoefficients (n : ℕ) (i : DivisorIndex n) : ℝ :=
  divisorCoefficients n i - paretoCoefficients n i

theorem stageDisplacement_expansion (n : ℕ) :
    stageDisplacement n =
      ∑ i, displacementCoefficients n i • qResidue (divisorConductor n i) := by
  rw [stageDisplacement, ← divisorCandidate_eq_primorialOptimizer, divisorCandidate,
    pOptimizer_expansion]
  simp only [QCovarianceInverse.qSynthesis, displacementCoefficients, sub_smul,
    Finset.sum_sub_distrib]

/-- The measured datum is the signed row of the complete Q Gram matrix
against the difference of the complete Q and Pareto inverse solves. -/
theorem normalizedPairing_gram (n m : ℕ) :
    normalizedPairing n m = (zetaTwo * (m : ℝ)) *
      ∑ i, displacementCoefficients n i *
        inner ℝ (qResidue m) (qResidue (divisorConductor n i)) := by
  rw [normalizedPairing, stageDisplacement_expansion]
  simp only [inner_sum, real_inner_smul_right]

private theorem primesLE_nonempty (n : ℕ) : (Nat.primesLE (n + 3)).Nonempty :=
  ⟨2, Nat.mem_primesLE.mpr ⟨by omega, Nat.prime_two⟩⟩

/-- The largest prime of the actual cutoff stage. -/
def largestPrime (n : ℕ) : ℕ := (Nat.primesLE (n + 3)).max' (primesLE_nonempty n)

theorem largestPrime_mem (n : ℕ) : largestPrime n ∈ Nat.primesLE (n + 3) :=
  Finset.max'_mem _ _

theorem largestPrime_tendsto : Tendsto largestPrime atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  obtain ⟨p, hbp, hp⟩ := Nat.exists_infinite_primes b
  filter_upwards [eventually_ge_atTop p] with n hn
  have hpn : p ∈ Nat.primesLE (n + 3) := Nat.mem_primesLE.mpr ⟨by omega, hp⟩
  exact hbp.trans (Finset.le_max' _ _ hpn)

theorem normalizedLargestPrimePairing_tendsto :
    Tendsto (fun n => normalizedPairing n (largestPrime n)) atTop
      (𝓝 (‖toPareto QSquarefreeDisplacementRigidity.pResidual‖ ^ 2)) :=
  normalizedPrimePairing_tendsto id largestPrime tendsto_id largestPrime_tendsto
    (Eventually.of_forall fun n =>
      ⟨Nat.prime_of_mem_primesLE (largestPrime_mem n),
        Nat.le_of_mem_primesLE (largestPrime_mem n)⟩)

end RiemannResearch.RH.QPrimorialMatchedGram
