import RiemannResearch.Analysis.ProjectionWalkSaturation
import RiemannResearch.RH.RamanujanCorrelationCompleteness
import RiemannResearch.RH.RamanujanInexactWalk

/-!
# Adaptive Ramanujan RH equivalences and inexact legal solvers

Source: sixth Ramanujan transfer program, 24 October 2026.
Every successful visited walk implies RH unconditionally. For the reverse RH
implications the open analytic Baez-Duarte provider remains an explicit input.
Correlation completeness, weaker than exhaustive enumeration, transfers RH
to arbitrary selected walks, their captured norms, total innovation energies,
and all actual continuous signed Mobius coordinates. Solver defects are kept.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.RamanujanAdaptiveRH
open Pareto ZetaTwoHilbert SquarefreeMobiusProjection
open RamanujanVisitedWalk RamanujanCorrelationCompleteness
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.ProjectionVariation
open RiemannResearch.Analysis.ProjectionWalkSaturation
open RiemannResearch.Analysis.ProjectionCorrelationCompleteness

theorem pareto_rh_of_visited_norm {α : Type*} {l : Filter α} [NeBot l]
    (draw : ℕ → ℕ) (N : α → ℕ) (hN : Tendsto N l atTop)
    (h : Tendsto (fun i => ‖hilbertOne - paretoCandidate draw (N i)‖) l (𝓝 0)) :
    RiemannHypothesis := by
  have he := pareto_full_saturation_of_visited draw
    ((cofinal_norm_zero_iff paretoPacket draw hilbertOne N hN).mp h)
  exact RamanujanCanonicalOptimizer.packet_riemannHypothesis_of_saturation
    ((RamanujanCanonicalOptimizer.packet_cofinal_mass_iff id tendsto_id).mpr he)

theorem q_rh_of_visited_norm {α : Type*} {l : Filter α} [NeBot l]
    (draw : ℕ → ℕ) (N : α → ℕ) (hN : Tendsto N l atTop)
    (h : Tendsto (fun i => ‖qOne - qCandidate draw (N i)‖) l (𝓝 0)) :
    RiemannHypothesis := by
  have he := q_full_saturation_of_visited draw
    ((cofinal_norm_zero_iff qPacket draw qOne N hN).mp h)
  have hp := CoefficientStabilization.limitEnergy_zero_iff_mem.mpr
    (QRamanujanCanonicalOptimizer.closure_iff_pareto.mp
      (QRamanujanCanonicalOptimizer.packetLimitEnergy_zero_iff_closure.mp he))
  exact RamanujanCanonicalOptimizer.packet_riemannHypothesis_of_saturation
    ((RamanujanCanonicalOptimizer.packet_cofinal_mass_iff id tendsto_id).mpr hp)

theorem pareto_adaptive_coefficients_iff {α : Type*} {l : Filter α} [NeBot l]
    (draw : ℕ → ℕ) (h : CorrelationsVanish paretoPacket draw hilbertOne)
    (N : α → ℕ) (hN : Tendsto N l atTop) :
    (∀ m : ℕ, 1 < m → Tendsto
      (fun i => CoefficientStabilization.coefficientCLM m (paretoCandidate draw (N i))) l
        (𝓝 (-(ArithmeticFunction.moebius m : ℝ)))) ↔
      CoefficientStabilization.limitEnergy = 0 := by
  have hp : Tendsto (fun i => paretoCandidate draw (N i)) l
      (𝓝 (visitedProjection paretoPacket draw hilbertOne)) := by
    simpa only [Function.comp_def] using (paretoCandidate_tendsto draw).comp hN
  rw [(pareto_adaptive_complete_iff draw).mpr h] at hp
  have ht (m : ℕ) : Tendsto
      (fun i => CoefficientStabilization.coefficientCLM m (paretoCandidate draw (N i))) l
      (𝓝 (CoefficientStabilization.limitCoefficient m)) := by
    simpa only [Function.comp_def, CoefficientStabilization.limitCoefficient] using
      (CoefficientStabilization.coefficientCLM m).continuous.continuousAt.tendsto.comp hp
  have hc := CoefficientStabilization.limitCoefficients_eq_mobius_iff_residual_zero.trans
    CoefficientStabilization.limitResidual_zero_iff_energy_zero
  constructor
  · intro hh
    apply hc.mp
    intro m hm
    exact tendsto_nhds_unique (ht m) (hh m hm)
  · intro hh m hm
    simpa only [hc.mpr hh m hm] using ht m

theorem q_adaptive_coordinates_iff {α : Type*} {l : Filter α} [NeBot l]
    (draw : ℕ → ℕ) (h : CorrelationsVanish qPacket draw qOne)
    (N : α → ℕ) (hN : Tendsto N l atTop) :
    (∀ m : ℕ, 1 < m → Tendsto
      (fun i => qCoefficientCLM m (qCandidate draw (N i))) l
        (𝓝 (-(ArithmeticFunction.moebius m : ℝ)))) ↔
      QRamanujanCanonicalOptimizer.packetLimitEnergy = 0 := by
  have hp : Tendsto (fun i => qCandidate draw (N i)) l
      (𝓝 (visitedProjection qPacket draw qOne)) := by
    simpa only [Function.comp_def] using (qCandidate_tendsto draw).comp hN
  rw [(q_adaptive_complete_iff draw).mpr h] at hp
  have ht (m : ℕ) : Tendsto
      (fun i => qCoefficientCLM m (qCandidate draw (N i))) l
      (𝓝 (QRamanujanCanonicalOptimizer.limitCoordinate m)) := by
    simpa only [Function.comp_def, QRamanujanCanonicalOptimizer.limitCoordinate] using
      (qCoefficientCLM m).continuous.continuousAt.tendsto.comp hp
  have hc := QRamanujanCanonicalOptimizer.limitCoordinates_eq_moebius_iff_closure.trans
    QRamanujanCanonicalOptimizer.packetLimitEnergy_zero_iff_closure.symm
  constructor
  · intro hh
    apply hc.mp
    intro m hm
    exact tendsto_nhds_unique (ht m) (hh m hm)
  · intro hh m hm
    simpa only [hc.mpr hh m hm] using ht m

private theorem pareto_visited_zero_iff_rh
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    (draw : ℕ → ℕ) (h : CorrelationsVanish paretoPacket draw hilbertOne) :
    visitedError paretoPacket draw hilbertOne = 0 ↔ RiemannHypothesis := by
  rw [(pareto_adaptive_error_iff draw).mpr h]
  exact (RamanujanCanonicalOptimizer.packet_cofinal_mass_iff id tendsto_id).symm.trans
    (RamanujanCanonicalOptimizer.packet_cofinal_rh_equivalences hBaezDuarte id tendsto_id).1

private theorem q_visited_zero_iff_rh
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    (draw : ℕ → ℕ) (h : CorrelationsVanish qPacket draw qOne) :
    visitedError qPacket draw qOne = 0 ↔ RiemannHypothesis := by
  rw [(q_adaptive_error_iff draw).mpr h]
  exact (QRamanujanCanonicalOptimizer.packet_cofinal_mass_iff id tendsto_id).symm.trans
    (QRamanujanCanonicalOptimizer.packet_cofinal_rh_equivalences hBaezDuarte id tendsto_id).1

/-- RH iff each of four actual adaptive Pareto Ramanujan saturation tests. -/
theorem pareto_adaptive_rh_chain
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    {α : Type*} {l : Filter α} [NeBot l]
    (draw : ℕ → ℕ) (h : CorrelationsVanish paretoPacket draw hilbertOne)
    (N : α → ℕ) (hN : Tendsto N l atTop) :
    (Tendsto (fun i => ‖hilbertOne - paretoCandidate draw (N i)‖) l (𝓝 0) ↔ RiemannHypothesis) ∧
    (Tendsto (fun i => ‖paretoCandidate draw (N i)‖ ^ 2) l (𝓝 1) ↔ RiemannHypothesis) ∧
    ((∑' n, ‖paretoCandidate draw (n + 1) - paretoCandidate draw n‖ ^ 2) = 1 ↔ RiemannHypothesis) ∧
    ((∀ m : ℕ, 1 < m → Tendsto
      (fun i => CoefficientStabilization.coefficientCLM m (paretoCandidate draw (N i))) l
        (𝓝 (-(ArithmeticFunction.moebius m : ℝ)))) ↔ RiemannHypothesis) := by
  have hv := pareto_visited_zero_iff_rh hBaezDuarte draw h
  have he : CoefficientStabilization.limitEnergy = 0 ↔ RiemannHypothesis :=
    (RamanujanCanonicalOptimizer.packet_cofinal_mass_iff id tendsto_id).symm.trans
      (RamanujanCanonicalOptimizer.packet_cofinal_rh_equivalences hBaezDuarte id tendsto_id).1
  refine ⟨(cofinal_norm_zero_iff paretoPacket draw hilbertOne N hN).trans hv, ?_, ?_,
    (pareto_adaptive_coefficients_iff draw h N hN).trans he⟩
  · simpa only [hilbertOne_norm_sq, paretoCandidate] using
      (cofinal_mass_iff paretoPacket draw hilbertOne N hN).trans hv
  · simpa only [hilbertOne_norm_sq, paretoCandidate, increment] using
      (gain_saturation_iff paretoPacket draw hilbertOne).trans hv

/-- RH iff each of four actual adaptive Q Ramanujan saturation tests. -/
theorem q_adaptive_rh_chain
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    {α : Type*} {l : Filter α} [NeBot l]
    (draw : ℕ → ℕ) (h : CorrelationsVanish qPacket draw qOne)
    (N : α → ℕ) (hN : Tendsto N l atTop) :
    (Tendsto (fun i => ‖qOne - qCandidate draw (N i)‖) l (𝓝 0) ↔ RiemannHypothesis) ∧
    (Tendsto (fun i => ‖qCandidate draw (N i)‖ ^ 2) l (𝓝 1) ↔ RiemannHypothesis) ∧
    ((∑' n, ‖qCandidate draw (n + 1) - qCandidate draw n‖ ^ 2) = 1 ↔ RiemannHypothesis) ∧
    ((∀ m : ℕ, 1 < m → Tendsto
      (fun i => qCoefficientCLM m (qCandidate draw (N i))) l
        (𝓝 (-(ArithmeticFunction.moebius m : ℝ)))) ↔ RiemannHypothesis) := by
  have hv := q_visited_zero_iff_rh hBaezDuarte draw h
  have he : QRamanujanCanonicalOptimizer.packetLimitEnergy = 0 ↔ RiemannHypothesis :=
    (QRamanujanCanonicalOptimizer.packet_cofinal_mass_iff id tendsto_id).symm.trans
      (QRamanujanCanonicalOptimizer.packet_cofinal_rh_equivalences hBaezDuarte id tendsto_id).1
  refine ⟨(cofinal_norm_zero_iff qPacket draw qOne N hN).trans hv, ?_, ?_,
    (q_adaptive_coordinates_iff draw h N hN).trans he⟩
  · simpa only [qOne_norm_sq, qCandidate] using
      (cofinal_mass_iff qPacket draw qOne N hN).trans hv
  · simpa only [qOne_norm_sq, qCandidate, increment] using
      (gain_saturation_iff qPacket draw qOne).trans hv

theorem pareto_inexact_norm_iff_rh_and_solver
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    {α : Type*} {l : Filter α} [NeBot l]
    (draw : ℕ → ℕ) (h : CorrelationsVanish paretoPacket draw hilbertOne)
    (N : α → ℕ) (hN : Tendsto N l atTop) (u : α → ThresholdHilbert)
    (hu : ∀ i, u i ∈ walkSpan paretoPacket draw (N i)) :
    Tendsto (fun i => ‖hilbertOne - u i‖) l (𝓝 0) ↔
      RiemannHypothesis ∧ Tendsto (fun i => ‖paretoCandidate draw (N i) - u i‖) l (𝓝 0) :=
  (RamanujanInexactWalk.pareto_trial_norm_zero_iff draw N hN u hu).trans
    (and_congr (pareto_visited_zero_iff_rh hBaezDuarte draw h) Iff.rfl)

theorem q_inexact_norm_iff_rh_and_solver
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    {α : Type*} {l : Filter α} [NeBot l]
    (draw : ℕ → ℕ) (h : CorrelationsVanish qPacket draw qOne)
    (N : α → ℕ) (hN : Tendsto N l atTop) (u : α → QHilbert)
    (hu : ∀ i, u i ∈ walkSpan qPacket draw (N i)) :
    Tendsto (fun i => ‖qOne - u i‖) l (𝓝 0) ↔
      RiemannHypothesis ∧ Tendsto (fun i => ‖qCandidate draw (N i) - u i‖) l (𝓝 0) :=
  (RamanujanInexactWalk.q_trial_norm_zero_iff draw N hN u hu).trans
    (and_congr (q_visited_zero_iff_rh hBaezDuarte draw h) Iff.rfl)

end RiemannResearch.RH.RamanujanAdaptiveRH
