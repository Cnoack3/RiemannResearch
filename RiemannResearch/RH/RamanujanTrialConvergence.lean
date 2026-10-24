import RiemannResearch.Analysis.NonnegativeErrorConvergence
import RiemannResearch.RH.RamanujanNormalDefect
import RiemannResearch.RH.QRamanujanSaturationCriteria
import RiemannResearch.RH.QParetoGramComparison
import RiemannResearch.RH.QParetoMetric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

/-!
# Arbitrary trial packet arrays: exact defects and cofinal convergence

Source: user-requested third Ramanujan transfer program, 23 October 2026.
Trial coefficients may depend on an arbitrary cofinal filter and need not
solve any normal equation. Norm convergence is exactly canonical saturation
plus vanishing of the complete inverse-Gram defect. The same physical trial
has equivalent convergence under P and Q, although its two optimal reference
vectors and two defect energies are different.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.RamanujanTrialConvergence
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QParetoEquivalence
open RamanujanNormalDefect
open RiemannResearch.Analysis.FiniteHilbertGram

open RiemannResearch.Analysis.NonnegativeErrorConvergence

def paretoTrial (n : ℕ) (a : Fin n → ℝ) : ThresholdHilbert :=
  Fintype.linearCombination ℝ
    (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a

def qTrial (n : ℕ) (a : Fin n → ℝ) : QHilbert :=
  Fintype.linearCombination ℝ (QRamanujanCanonicalOptimizer.packetFamily n) a

theorem toPareto_qTrial (n : ℕ) (a : Fin n → ℝ) :
    toPareto (qTrial n a) = paretoTrial n a := by
  have hf : QParetoGramComparison.paretoFamily
      (QRamanujanCanonicalOptimizer.packetFamily n) =
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) := by
    funext i
    exact RamanujanPrimeCoordinates.toPareto_packet _
  have h := QParetoGramComparison.toPareto_synthesis
    (QRamanujanCanonicalOptimizer.packetFamily n) a
  rw [hf] at h
  exact h

theorem toPareto_trial_residual (n : ℕ) (a : Fin n → ℝ) :
    toPareto (qOne - qTrial n a) = hilbertOne - paretoTrial n a := by
  change toParetoLinear (qOne - qTrial n a) = _
  rw [map_sub]
  exact congrArg₂ HSub.hSub toPareto_qOne (toPareto_qTrial n a)

/-- The exact two-metric budget for one arbitrary physical trial. -/
theorem trial_metric_identity (n : ℕ) (a : Fin n → ℝ) :
    zetaTwo * (1 - QRamanujanCanonicalOptimizer.packetMass n + qDefectEnergy n a) =
      1 - RamanujanCanonicalOptimizer.packetMass n + paretoDefectEnergy n a +
        QParetoMetric.metricCorrection (qOne - qTrial n a) := by
  have h := QParetoMetric.norm_identity (qOne - qTrial n a)
  rw [toPareto_trial_residual] at h
  simpa only [qTrial, paretoTrial, q_trial_error, pareto_trial_error] using h

/-- This equivalence allows moving stages, coefficients, and non-sequential filters. -/
theorem pareto_trial_norm_iff {α : Type*} {l : Filter α} [NeBot l]
    (N : α → ℕ) (hN : Tendsto N l atTop) (a : ∀ i, Fin (N i) → ℝ) :
    Tendsto (fun i => ‖hilbertOne - paretoTrial (N i) (a i)‖) l (𝓝 0) ↔
      CoefficientStabilization.limitEnergy = 0 ∧
        Tendsto (fun i => paretoDefectEnergy (N i) (a i)) l (𝓝 0) := by
  have he : Tendsto (fun i => 1 - RamanujanCanonicalOptimizer.packetMass (N i))
      l (𝓝 CoefficientStabilization.limitEnergy) := by
    simpa only [Function.comp_def, RamanujanCanonicalOptimizer.packet_energy_eq_original]
      using CoefficientStabilization.energy_tendsto.comp hN
  have he0 : Tendsto (fun i => 1 - RamanujanCanonicalOptimizer.packetMass (N i))
      l (𝓝 0) ↔ CoefficientStabilization.limitEnergy = 0 := by
    constructor
    · exact fun h => tendsto_nhds_unique he h
    · intro h
      simpa only [h] using he
  have hn : ∀ i, 0 ≤ 1 - RamanujanCanonicalOptimizer.packetMass (N i) := by
    intro i
    exact (sub_pos.mpr (RamanujanCanonicalOptimizer.packetMass_bounds (N i)).2).le
  rw [norm_zero_iff_square]
  simp only [paretoTrial, pareto_trial_error]
  exact (nonnegative_add_zero_iff _ _ hn
    (fun i => defectEnergy_nonneg (finitePacket_independent (N i)) hilbertOne (a i))).trans
      (and_congr he0 Iff.rfl)

theorem q_trial_norm_iff {α : Type*} {l : Filter α} [NeBot l]
    (N : α → ℕ) (hN : Tendsto N l atTop) (a : ∀ i, Fin (N i) → ℝ) :
    Tendsto (fun i => ‖qOne - qTrial (N i) (a i)‖) l (𝓝 0) ↔
      QRamanujanCanonicalOptimizer.packetLimitEnergy = 0 ∧
        Tendsto (fun i => qDefectEnergy (N i) (a i)) l (𝓝 0) := by
  have he : Tendsto (fun i => 1 - QRamanujanCanonicalOptimizer.packetMass (N i))
      l (𝓝 QRamanujanCanonicalOptimizer.packetLimitEnergy) := by
    exact QRamanujanCanonicalOptimizer.packetError_tendsto.comp hN
  have he0 : Tendsto (fun i => 1 - QRamanujanCanonicalOptimizer.packetMass (N i))
      l (𝓝 0) ↔ QRamanujanCanonicalOptimizer.packetLimitEnergy = 0 := by
    constructor
    · exact fun h => tendsto_nhds_unique he h
    · intro h
      simpa only [h] using he
  have hn : ∀ i, 0 ≤ 1 - QRamanujanCanonicalOptimizer.packetMass (N i) :=
    fun i => (QRamanujanCanonicalOptimizer.packetError_pos (N i)).le
  rw [norm_zero_iff_square]
  simp only [qTrial, q_trial_error]
  exact (nonnegative_add_zero_iff _ _ hn
    (fun i => defectEnergy_nonneg
      (QRamanujanCanonicalOptimizer.packet_independent (N i)) qOne (a i))).trans
      (and_congr he0 Iff.rfl)

/-- No cofinality or optimality is needed for convergence of the same trial in both measures. -/
theorem trial_norm_pareto_iff_q {α : Type*} {l : Filter α}
    (N : α → ℕ) (a : ∀ i, Fin (N i) → ℝ) :
    Tendsto (fun i => ‖hilbertOne - paretoTrial (N i) (a i)‖) l (𝓝 0) ↔
      Tendsto (fun i => ‖qOne - qTrial (N i) (a i)‖) l (𝓝 0) := by
  constructor
  · intro hp
    have ht : Tendsto (fun i => Real.sqrt (2 / zetaTwo) *
        ‖hilbertOne - paretoTrial (N i) (a i)‖) l (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hp
    apply squeeze_zero (fun i => norm_nonneg _) _ ht
    intro i
    have hb := toQ_norm_le (toPareto (qOne - qTrial (N i) (a i)))
    rw [toQ_toPareto] at hb
    rw [toPareto_trial_residual] at hb
    exact hb
  · intro hq
    have ht : Tendsto (fun i => Real.sqrt zetaTwo *
        ‖qOne - qTrial (N i) (a i)‖) l (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hq
    apply squeeze_zero (fun i => norm_nonneg _) _ ht
    intro i
    simpa only [toPareto_trial_residual] using
      toPareto_norm_le (qOne - qTrial (N i) (a i))

/-- The full RH equivalence makes the unresolved saturation requirement explicit. -/
theorem pareto_trial_norm_iff_rh_and_defect
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    {α : Type*} {l : Filter α} [NeBot l]
    (N : α → ℕ) (hN : Tendsto N l atTop) (a : ∀ i, Fin (N i) → ℝ) :
    Tendsto (fun i => ‖hilbertOne - paretoTrial (N i) (a i)‖) l (𝓝 0) ↔
      RiemannHypothesis ∧
        Tendsto (fun i => paretoDefectEnergy (N i) (a i)) l (𝓝 0) := by
  have he := (RamanujanCanonicalOptimizer.packet_cofinal_mass_iff id tendsto_id).symm.trans
    (RamanujanCanonicalOptimizer.packet_cofinal_rh_equivalences
      hBaezDuarte id tendsto_id).1
  exact (pareto_trial_norm_iff N hN a).trans (and_congr he Iff.rfl)

theorem q_trial_norm_iff_rh_and_defect
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    {α : Type*} {l : Filter α} [NeBot l]
    (N : α → ℕ) (hN : Tendsto N l atTop) (a : ∀ i, Fin (N i) → ℝ) :
    Tendsto (fun i => ‖qOne - qTrial (N i) (a i)‖) l (𝓝 0) ↔
      RiemannHypothesis ∧
        Tendsto (fun i => qDefectEnergy (N i) (a i)) l (𝓝 0) := by
  have he := (QRamanujanCanonicalOptimizer.packet_cofinal_mass_iff id tendsto_id).symm.trans
    (QRamanujanCanonicalOptimizer.packet_cofinal_rh_equivalences
      hBaezDuarte id tendsto_id).1
  exact (q_trial_norm_iff N hN a).trans (and_congr he Iff.rfl)

/-- Under canonical saturation, the two different normal-defect energies vanish together. -/
theorem pareto_defect_iff_q_of_rh
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    (hRH : RiemannHypothesis)
    {α : Type*} {l : Filter α} [NeBot l]
    (N : α → ℕ) (hN : Tendsto N l atTop) (a : ∀ i, Fin (N i) → ℝ) :
    Tendsto (fun i => paretoDefectEnergy (N i) (a i)) l (𝓝 0) ↔
      Tendsto (fun i => qDefectEnergy (N i) (a i)) l (𝓝 0) := by
  have hp := pareto_trial_norm_iff_rh_and_defect hBaezDuarte N hN a
  have hq := q_trial_norm_iff_rh_and_defect hBaezDuarte N hN a
  simp only [hRH, true_and] at hp hq
  exact hp.symm.trans ((trial_norm_pareto_iff_q N a).trans hq)

end RiemannResearch.RH.RamanujanTrialConvergence
