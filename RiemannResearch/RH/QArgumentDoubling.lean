/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFloorDilation
import RiemannResearch.RH.ArgumentDoublingGenerators
import RiemannResearch.RH.QParityBasis
import Mathlib.Tactic.Linarith

/-!
# Physical argument doubling under the complete inverse-square law

Source: independently derived continuation of the user's prime-resampling and
physical-doubling research request, 27 October 2026. The bounded operator is
transported through the existing equivalent Pareto realization. Its weighted
mean identity uses the complete infinite even progression, not a truncation.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QArgumentDoubling
open ZetaTwoHilbert ZetaTwoParitySignal ZetaTwoParetoTransfer

/-- Physical even sampling, distinct from floor dilation and prime resampling. -/
def doubling : QHilbert →L[ℝ] QHilbert :=
  QFloorDilation.fromParetoCLM.comp (Pareto.argumentDoublingContinuous.comp toParetoCLM)

@[simp] theorem doubling_sequence (f : QHilbert) :
    qSequence (doubling f) = fun n => qSequence f (2 * n) := by
  simp only [doubling, ContinuousLinearMap.comp_apply,
    QFloorDilation.fromParetoCLM_apply, QFloorDilation.fromPareto_sequence,
    Pareto.argumentDoublingContinuous_apply, Pareto.hilbertArgumentDoubling_sequence,
    toParetoCLM_apply, toPareto_sequence]

@[simp] theorem doubling_qOne : doubling qOne = qOne := by
  apply qSequence_injective
  funext n
  simp [doubling_sequence, qSequence_qOne, qOneSequence]

@[simp] theorem doubling_qResidue_two : doubling (qResidue 2) = 0 := by
  apply qSequence_injective
  funext n
  rw [doubling_sequence, qSequence_qResidue]
  change ArithmeticCumulative.residueFraction 2 (2 * n) = qSequenceLinear 0 n
  simp [ArithmeticCumulative.residueFraction]

/-- Exact dual action at the constant target. -/
theorem doubling_mean (f : QHilbert) :
    inner ℝ (doubling f) qOne = 4 * inner ℝ f qEven := by
  have he := qInner_even_reindex f
  simp_rw [ZetaTwoParitySignal.positiveQWeight_mul] at he
  norm_num only [Nat.cast_ofNat] at he
  have hm : inner ℝ f qEven = (1 / 4 : ℝ) * inner ℝ (doubling f) qOne := by
    rw [he, qInner_one_tsum, doubling_sequence, ← tsum_mul_left]
    apply tsum_congr
    intro n
    ring
  linarith

/-- A pointwise decrease implies a decrease of the actual complete Q mean. -/
theorem doubling_mean_le_of_pointwise (f : QHilbert)
    (h : ∀ n, qSequence f (2 * n) ≤ qSequence f n) :
    inner ℝ (doubling f) qOne ≤ inner ℝ f qOne := by
  rw [qInner_one_tsum, qInner_one_tsum]
  apply (qWeighted_summable (doubling f)).tsum_le_tsum _ (qWeighted_summable f)
  intro n
  rw [doubling_sequence]
  exact mul_le_mul_of_nonneg_left (h n) (positiveQWeight_nonneg n)

end RiemannResearch.RH.QArgumentDoubling
