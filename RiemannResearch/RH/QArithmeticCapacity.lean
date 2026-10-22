import RiemannResearch.RH.QDivisorHilbertBasis
import RiemannResearch.RH.QSquarefreeCapacity

/-!
# The squarefree optimizer in Q arithmetic coordinates

Source: the user's Q prime-structure research program, 13 October 2026.
The coefficients chosen here solve the actual finite squarefree Gram
system. The energy is the full infinite Jordan-weighted sum of their
Möbius/divisibility-coordinate residuals, with no arithmetic tail omitted.

Parseval identifies this literal arithmetic energy with the actual Q
approximation error. Its vanishing is equivalent to squarefree closure
and covariance-capacity divergence, and implies Mathlib's RH. The reverse
RH implication is stated only with its explicit analytic forward provider.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.QArithmeticCapacity

open ZetaTwoHilbert ZetaTwoProbability QCovarianceInverse QDivisorHilbert
open QSquarefreeCapacity

/-- Choose actual finite normal-equation coefficients. Zero masked
coordinates need not have unique coefficients; their synthesis is fixed. -/
def optimizerCoefficients (n : ℕ) : Fin n → ℝ :=
  Classical.choose (exists_normal_optimizer n)

theorem optimizerCoefficients_synthesis (n : ℕ) :
    qSynthesis (fun i : Fin n => conductor i) (optimizerCoefficients n) =
      ZetaTwoOptimizerStage.optimizer n :=
  (Classical.choose_spec (exists_normal_optimizer n)).1

theorem optimizerCoefficients_normal (n : ℕ) (i : Fin n) :
    RiemannResearch.LinearAlgebra.CenteredNormalEquations.action
      (qGram (fun j : Fin n => conductor j)) (optimizerCoefficients n) i =
        qMean (fun j : Fin n => conductor j) i :=
  (Classical.choose_spec (exists_normal_optimizer n)).2 i

/-- Full arithmetic residual energy: the target is the single r=1 mode. -/
def arithmeticEnergy (n : ℕ) : ℝ :=
  ∑' r : ℕ+, ((if r = 1 then (1 : ℝ) else 0) -
    ∑ i : Fin n, optimizerCoefficients n i *
      qResidueDivisorCoefficient (conductor i) (r : ℕ)) ^ 2 /
        qJordanTwo (r : ℕ)

theorem arithmeticEnergy_eq_error (n : ℕ) :
    arithmeticEnergy n = ZetaTwoOptimizerStage.error n := by
  unfold arithmeticEnergy
  rw [qSynthesis_error_parseval, optimizerCoefficients_synthesis]
  rfl

theorem arithmeticEnergy_pos (n : ℕ) : 0 < arithmeticEnergy n := by
  rw [arithmeticEnergy_eq_error]
  exact ZetaTwoOptimizerStage.error_pos n

/-- The inverse-Gram capacity has an exact expression in prime/divisor coordinates. -/
theorem capacity_eq_arithmeticEnergy (n : ℕ) :
    capacity n = (1 - arithmeticEnergy n) / arithmeticEnergy n := by
  rw [arithmeticEnergy_eq_error]
  rfl

theorem arithmeticEnergy_eq_reciprocal_capacity (n : ℕ) :
    arithmeticEnergy n = 1 / (1 + capacity n) := by
  rw [arithmeticEnergy_eq_error]
  exact error_eq_reciprocal_capacity n

theorem arithmeticEnergy_tendsto_iff_capacity :
    Tendsto arithmeticEnergy atTop (𝓝 0) ↔ Tendsto capacity atTop atTop := by
  rw [show arithmeticEnergy = ZetaTwoOptimizerStage.error from
    funext arithmeticEnergy_eq_error]
  exact capacity_tendsto_iff_error_tendsto.symm

theorem arithmeticEnergy_tendsto_iff_squarefree_closure :
    Tendsto arithmeticEnergy atTop (𝓝 0) ↔
      qOne ∈ qSquarefreeCRTSpan.topologicalClosure :=
  arithmeticEnergy_tendsto_iff_capacity.trans
    capacity_tendsto_iff_squarefree_closure

theorem arithmeticEnergy_tendsto_iff_exact_head_tail_bound :
    Tendsto arithmeticEnergy atTop (𝓝 0) ↔ Pareto.SquarefreeExactHeadTailBound :=
  arithmeticEnergy_tendsto_iff_capacity.trans
    capacity_tendsto_iff_exact_head_tail_bound

/-- Controlling the full arithmetic energy suffices for actual RH. -/
theorem riemannHypothesis_of_arithmeticEnergy_tendsto
    (h : Tendsto arithmeticEnergy atTop (𝓝 0)) : RiemannHypothesis :=
  riemannHypothesis_of_capacity_tendsto (arithmeticEnergy_tendsto_iff_capacity.mp h)

/-- Conditional analytic assembly: the RH-to-squarefree-density provider
`hforward` is required explicitly, and is not proved or postulated here. -/
theorem arithmeticEnergy_tendsto_iff_riemannHypothesis
    (hforward : RiemannHypothesis →
      qOne ∈ qSquarefreeCRTSpan.topologicalClosure) :
    Tendsto arithmeticEnergy atTop (𝓝 0) ↔ RiemannHypothesis :=
  arithmeticEnergy_tendsto_iff_capacity.trans
    (capacity_tendsto_iff_riemannHypothesis hforward)

end RiemannResearch.RH.QArithmeticCapacity
