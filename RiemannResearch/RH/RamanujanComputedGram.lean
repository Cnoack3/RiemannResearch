import RiemannResearch.Analysis.ComputedGramStability
import RiemannResearch.RH.RamanujanTrialConvergence

/-!
# Certified computed Gram errors for actual Pareto and Q Ramanujan trials

Source: user-requested fifth Ramanujan transfer program, 24 October 2026.
The computed finite Gram dictionaries may change with every stage. Full
trial-error intervals retain the respective actual P or Q optimal residual.
The RH converses explicitly require the open Baez--Duarte provider.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.RamanujanComputedGram
open Pareto ZetaTwoHilbert RamanujanNormalDefect RamanujanTrialConvergence
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteHilbertConstraints
open RiemannResearch.Analysis.FiniteGramBackwardError
open RiemannResearch.Analysis.ComputedGramStability

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- The interval includes the actual Pareto optimum, not only its coefficient defect. -/
theorem pareto_trial_error_computed_interval (n : ℕ) (w : Fin n → K)
    (hw : LinearIndependent ℝ w) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hrel : RelativeFormBound
      (fun j : Fin n => ramanujanPacketHilbert (j.val + 2)) w ε) (a : Fin n → ℝ) :
    1 - RamanujanCanonicalOptimizer.packetMass n +
        computedDefectEnergy hw
          (fun j : Fin n => ramanujanPacketHilbert (j.val + 2)) hilbertOne a / (1 + ε) ≤
      ‖hilbertOne - paretoTrial n a‖ ^ 2 ∧
    ‖hilbertOne - paretoTrial n a‖ ^ 2 ≤
      1 - RamanujanCanonicalOptimizer.packetMass n +
        computedDefectEnergy hw
          (fun j : Fin n => ramanujanPacketHilbert (j.val + 2)) hilbertOne a / (1 - ε) := by
  have h := residual_error_computed_interval (finitePacket_independent n) hw
    ε hε hε1 hrel hilbertOne a
  change ‖hilbertOne - RamanujanCanonicalOptimizer.packetCandidate n‖ ^ 2 + _ ≤ _ ∧
    _ ≤ ‖hilbertOne - RamanujanCanonicalOptimizer.packetCandidate n‖ ^ 2 + _ at h
  rw [RamanujanCanonicalOptimizer.packet_error] at h
  exact h

/-- The Q reference optimum is its own metric optimum and source vector. -/
theorem q_trial_error_computed_interval (n : ℕ) (w : Fin n → K)
    (hw : LinearIndependent ℝ w) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hrel : RelativeFormBound (QRamanujanCanonicalOptimizer.packetFamily n) w ε)
    (a : Fin n → ℝ) :
    1 - QRamanujanCanonicalOptimizer.packetMass n +
        computedDefectEnergy hw (QRamanujanCanonicalOptimizer.packetFamily n) qOne a /
          (1 + ε) ≤ ‖qOne - qTrial n a‖ ^ 2 ∧
    ‖qOne - qTrial n a‖ ^ 2 ≤
      1 - QRamanujanCanonicalOptimizer.packetMass n +
        computedDefectEnergy hw (QRamanujanCanonicalOptimizer.packetFamily n) qOne a /
          (1 - ε) := by
  have h := residual_error_computed_interval
    (QRamanujanCanonicalOptimizer.packet_independent n) hw ε hε hε1 hrel qOne a
  change ‖qOne - QRamanujanCanonicalOptimizer.packetCandidate n‖ ^ 2 + _ ≤ _ ∧
    _ ≤ ‖qOne - QRamanujanCanonicalOptimizer.packetCandidate n‖ ^ 2 + _ at h
  rw [QRamanujanCanonicalOptimizer.packet_error] at h
  exact h

/-- An arbitrary computed family, with a uniform certificate, yields a complete criterion. -/
theorem pareto_trial_norm_iff_computed
    {α : Type*} {l : Filter α} [NeBot l]
    (N : α → ℕ) (hN : Tendsto N l atTop) (a : ∀ i, Fin (N i) → ℝ)
    (w : ∀ i, Fin (N i) → K) (hw : ∀ i, LinearIndependent ℝ (w i))
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hrel : ∀ i, RelativeFormBound
      (fun j : Fin (N i) => ramanujanPacketHilbert (j.val + 2)) (w i) ε) :
    Tendsto (fun i => ‖hilbertOne - paretoTrial (N i) (a i)‖) l (𝓝 0) ↔
      CoefficientStabilization.limitEnergy = 0 ∧
        Tendsto (fun i => computedDefectEnergy (hw i)
          (fun j : Fin (N i) => ramanujanPacketHilbert (j.val + 2)) hilbertOne (a i))
          l (𝓝 0) := by
  have hd := defectEnergy_tendsto_iff_computed (l := l)
    (fun i => fun j : Fin (N i) => ramanujanPacketHilbert (j.val + 2)) w
    (fun i => finitePacket_independent (N i)) hw ε hε hε1 hrel (fun _ => hilbertOne) a
  exact (pareto_trial_norm_iff N hN a).trans (and_congr Iff.rfl hd)

theorem q_trial_norm_iff_computed
    {α : Type*} {l : Filter α} [NeBot l]
    (N : α → ℕ) (hN : Tendsto N l atTop) (a : ∀ i, Fin (N i) → ℝ)
    (w : ∀ i, Fin (N i) → K) (hw : ∀ i, LinearIndependent ℝ (w i))
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hrel : ∀ i, RelativeFormBound (QRamanujanCanonicalOptimizer.packetFamily (N i)) (w i) ε) :
    Tendsto (fun i => ‖qOne - qTrial (N i) (a i)‖) l (𝓝 0) ↔
      QRamanujanCanonicalOptimizer.packetLimitEnergy = 0 ∧
        Tendsto (fun i => computedDefectEnergy (hw i)
          (QRamanujanCanonicalOptimizer.packetFamily (N i)) qOne (a i)) l (𝓝 0) := by
  have hd := defectEnergy_tendsto_iff_computed (l := l)
    (fun i => QRamanujanCanonicalOptimizer.packetFamily (N i)) w
    (fun i => QRamanujanCanonicalOptimizer.packet_independent (N i)) hw ε hε hε1 hrel
    (fun _ => qOne) a
  exact (q_trial_norm_iff N hN a).trans (and_congr Iff.rfl hd)

theorem pareto_trial_norm_iff_rh_and_computed
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    {α : Type*} {l : Filter α} [NeBot l]
    (N : α → ℕ) (hN : Tendsto N l atTop) (a : ∀ i, Fin (N i) → ℝ)
    (w : ∀ i, Fin (N i) → K) (hw : ∀ i, LinearIndependent ℝ (w i))
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hrel : ∀ i, RelativeFormBound
      (fun j : Fin (N i) => ramanujanPacketHilbert (j.val + 2)) (w i) ε) :
    Tendsto (fun i => ‖hilbertOne - paretoTrial (N i) (a i)‖) l (𝓝 0) ↔
      RiemannHypothesis ∧ Tendsto (fun i => computedDefectEnergy (hw i)
        (fun j : Fin (N i) => ramanujanPacketHilbert (j.val + 2)) hilbertOne (a i)) l (𝓝 0) := by
  have hd := defectEnergy_tendsto_iff_computed (l := l)
    (fun i => fun j : Fin (N i) => ramanujanPacketHilbert (j.val + 2)) w
    (fun i => finitePacket_independent (N i)) hw ε hε hε1 hrel (fun _ => hilbertOne) a
  exact (pareto_trial_norm_iff_rh_and_defect hBaezDuarte N hN a).trans
    (and_congr Iff.rfl hd)

theorem q_trial_norm_iff_rh_and_computed
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    {α : Type*} {l : Filter α} [NeBot l]
    (N : α → ℕ) (hN : Tendsto N l atTop) (a : ∀ i, Fin (N i) → ℝ)
    (w : ∀ i, Fin (N i) → K) (hw : ∀ i, LinearIndependent ℝ (w i))
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hrel : ∀ i, RelativeFormBound (QRamanujanCanonicalOptimizer.packetFamily (N i)) (w i) ε) :
    Tendsto (fun i => ‖qOne - qTrial (N i) (a i)‖) l (𝓝 0) ↔
      RiemannHypothesis ∧ Tendsto (fun i => computedDefectEnergy (hw i)
        (QRamanujanCanonicalOptimizer.packetFamily (N i)) qOne (a i)) l (𝓝 0) := by
  have hd := defectEnergy_tendsto_iff_computed (l := l)
    (fun i => QRamanujanCanonicalOptimizer.packetFamily (N i)) w
    (fun i => QRamanujanCanonicalOptimizer.packet_independent (N i)) hw ε hε hε1 hrel
    (fun _ => qOne) a
  exact (q_trial_norm_iff_rh_and_defect hBaezDuarte N hN a).trans
    (and_congr Iff.rfl hd)

/-- Certified inexact computed P solves reduce approximation exactly to canonical saturation. -/
theorem pareto_certified_trial_norm_iff_saturation
    {α : Type*} {l : Filter α} [NeBot l]
    (N : α → ℕ) (hN : Tendsto N l atTop) (a b : ∀ i, Fin (N i) → ℝ)
    (w : ∀ i, Fin (N i) → K) (hw : ∀ i, LinearIndependent ℝ (w i))
    (ε : ℝ) (hε1 : ε < 1) (δ : α → ℝ) (hδ : ∀ i, 0 ≤ δ i)
    (hδε : ∀ i, δ i ≤ ε)
    (hrel : ∀ i, RelativeFormBound
      (fun j : Fin (N i) => ramanujanPacketHilbert (j.val + 2)) (w i) (δ i))
    (herr : Tendsto (fun i => ‖minimumVector (hw i)
      (computedResidual (w i) (b i) (a i) + sourceError
        (fun j : Fin (N i) => ramanujanPacketHilbert (j.val + 2)) hilbertOne (b i))‖) l (𝓝 0))
    (hmetric : Tendsto (fun i => δ i * ‖Fintype.linearCombination ℝ (w i) (a i)‖)
      l (𝓝 0)) :
    Tendsto (fun i => ‖hilbertOne - paretoTrial (N i) (a i)‖) l (𝓝 0) ↔
      CoefficientStabilization.limitEnergy = 0 := by
  have hd := defectEnergy_tendsto_zero_of_certified_errors
    (fun i => fun j : Fin (N i) => ramanujanPacketHilbert (j.val + 2)) w
    (fun i => finitePacket_independent (N i)) hw ε hε1 δ hδ hδε hrel
    (fun _ => hilbertOne) b a herr hmetric
  exact (pareto_trial_norm_iff N hN a).trans (and_iff_left hd)

/-- The same certified-computation criterion holds for the distinct actual Q Gram. -/
theorem q_certified_trial_norm_iff_saturation
    {α : Type*} {l : Filter α} [NeBot l]
    (N : α → ℕ) (hN : Tendsto N l atTop) (a b : ∀ i, Fin (N i) → ℝ)
    (w : ∀ i, Fin (N i) → K) (hw : ∀ i, LinearIndependent ℝ (w i))
    (ε : ℝ) (hε1 : ε < 1) (δ : α → ℝ) (hδ : ∀ i, 0 ≤ δ i)
    (hδε : ∀ i, δ i ≤ ε)
    (hrel : ∀ i, RelativeFormBound (QRamanujanCanonicalOptimizer.packetFamily (N i))
      (w i) (δ i))
    (herr : Tendsto (fun i => ‖minimumVector (hw i)
      (computedResidual (w i) (b i) (a i) +
        sourceError (QRamanujanCanonicalOptimizer.packetFamily (N i)) qOne (b i))‖) l (𝓝 0))
    (hmetric : Tendsto (fun i => δ i * ‖Fintype.linearCombination ℝ (w i) (a i)‖)
      l (𝓝 0)) :
    Tendsto (fun i => ‖qOne - qTrial (N i) (a i)‖) l (𝓝 0) ↔
      QRamanujanCanonicalOptimizer.packetLimitEnergy = 0 := by
  have hd := defectEnergy_tendsto_zero_of_certified_errors
    (fun i => QRamanujanCanonicalOptimizer.packetFamily (N i)) w
    (fun i => QRamanujanCanonicalOptimizer.packet_independent (N i)) hw
    ε hε1 δ hδ hδε hrel (fun _ => qOne) b a herr hmetric
  exact (q_trial_norm_iff N hN a).trans (and_iff_left hd)

end RiemannResearch.RH.RamanujanComputedGram
