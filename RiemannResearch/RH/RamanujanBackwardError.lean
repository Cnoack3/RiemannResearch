import RiemannResearch.Analysis.FiniteGramBackwardError
import RiemannResearch.RH.RamanujanTrialConvergence

/-!
# Inexact arithmetic packet solves in the actual P and Q metrics

Source: user-requested fourth Ramanujan transfer program, 23 October 2026.
The computed Gram matrices, sources, and solver outputs may move with the
stage. The exact signed backward budget is equivalent to the actual trial
excess. Full RH converses retain the explicit Baez-Duarte analytic provider.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.RamanujanBackwardError
open Pareto ZetaTwoHilbert
open RamanujanTrialConvergence RamanujanNormalDefect
open RiemannResearch.Analysis.FiniteGramBackwardError

def paretoBudget (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (b a : Fin n → ℝ) : ℝ :=
  backwardBudget (finitePacket_independent n) hilbertOne A b a

def qBudget (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (b a : Fin n → ℝ) : ℝ :=
  backwardBudget (QRamanujanCanonicalOptimizer.packet_independent n) qOne A b a

theorem pareto_error_exact (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (b a : Fin n → ℝ) :
    ‖hilbertOne - paretoTrial n a‖ ^ 2 =
      1 - RamanujanCanonicalOptimizer.packetMass n + paretoBudget n A b a := by
  rw [paretoBudget, backwardBudget_eq_defectEnergy]
  exact pareto_trial_error n a

theorem q_error_exact (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (b a : Fin n → ℝ) :
    ‖qOne - qTrial n a‖ ^ 2 =
      1 - QRamanujanCanonicalOptimizer.packetMass n + qBudget n A b a := by
  rw [qBudget, backwardBudget_eq_defectEnergy]
  exact q_trial_error n a

/-- Arbitrary computed arithmetic data are allowed: only the true signed budget matters. -/
theorem pareto_norm_iff_rh_and_budget
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    {α : Type*} {l : Filter α} [NeBot l]
    (N : α → ℕ) (hN : Tendsto N l atTop)
    (A : ∀ i, Matrix (Fin (N i)) (Fin (N i)) ℝ) (b a : ∀ i, Fin (N i) → ℝ) :
    Tendsto (fun i => ‖hilbertOne - paretoTrial (N i) (a i)‖) l (𝓝 0) ↔
      RiemannHypothesis ∧ Tendsto (fun i => paretoBudget (N i) (A i) (b i) (a i)) l (𝓝 0) := by
  simpa only [paretoBudget, backwardBudget_eq_defectEnergy, paretoDefectEnergy] using
    pareto_trial_norm_iff_rh_and_defect hBaezDuarte N hN a

theorem q_norm_iff_rh_and_budget
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    {α : Type*} {l : Filter α} [NeBot l]
    (N : α → ℕ) (hN : Tendsto N l atTop)
    (A : ∀ i, Matrix (Fin (N i)) (Fin (N i)) ℝ) (b a : ∀ i, Fin (N i) → ℝ) :
    Tendsto (fun i => ‖qOne - qTrial (N i) (a i)‖) l (𝓝 0) ↔
      RiemannHypothesis ∧ Tendsto (fun i => qBudget (N i) (A i) (b i) (a i)) l (𝓝 0) := by
  simpa only [qBudget, backwardBudget_eq_defectEnergy, qDefectEnergy] using
    q_trial_norm_iff_rh_and_defect hBaezDuarte N hN a

/-- Vanishing of the three nonnegative component energies suffices, even for inexact solves. -/
theorem pareto_norm_of_component_errors
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    (hRH : RiemannHypothesis)
    {α : Type*} {l : Filter α} [NeBot l]
    (N : α → ℕ) (hN : Tendsto N l atTop)
    (A : ∀ i, Matrix (Fin (N i)) (Fin (N i)) ℝ) (b a : ∀ i, Fin (N i) → ℝ)
    (hcomponents : Tendsto (fun i => componentBudget (finitePacket_independent (N i))
      hilbertOne (A i) (b i) (a i)) l (𝓝 0)) :
    Tendsto (fun i => ‖hilbertOne - paretoTrial (N i) (a i)‖) l (𝓝 0) := by
  apply (pareto_norm_iff_rh_and_budget hBaezDuarte N hN A b a).mpr
  refine ⟨hRH, ?_⟩
  exact backwardBudget_tendsto_zero_of_components
    (κ := fun i => Fin (N i))
    (fun i j => ramanujanPacketHilbert (j.val + 2))
    (fun i => finitePacket_independent (N i)) (fun _ => hilbertOne) A b a hcomponents

theorem q_norm_of_component_errors
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    (hRH : RiemannHypothesis)
    {α : Type*} {l : Filter α} [NeBot l]
    (N : α → ℕ) (hN : Tendsto N l atTop)
    (A : ∀ i, Matrix (Fin (N i)) (Fin (N i)) ℝ) (b a : ∀ i, Fin (N i) → ℝ)
    (hcomponents : Tendsto (fun i => componentBudget
      (QRamanujanCanonicalOptimizer.packet_independent (N i)) qOne (A i) (b i) (a i)) l (𝓝 0)) :
    Tendsto (fun i => ‖qOne - qTrial (N i) (a i)‖) l (𝓝 0) := by
  apply (q_norm_iff_rh_and_budget hBaezDuarte N hN A b a).mpr
  refine ⟨hRH, ?_⟩
  exact backwardBudget_tendsto_zero_of_components
    (κ := fun i => Fin (N i))
    (fun i => QRamanujanCanonicalOptimizer.packetFamily (N i))
    (fun i => QRamanujanCanonicalOptimizer.packet_independent (N i))
    (fun _ => qOne) A b a hcomponents

end RiemannResearch.RH.RamanujanBackwardError
