import RiemannResearch.RH.RamanujanDualCertificates
import RiemannResearch.RH.RamanujanSaturationCriteria
import RiemannResearch.RH.ParetoTailAverageCriterion
import RiemannResearch.RH.MobiusCoefficientStabilization
import Mathlib.Tactic.Linarith

/-!
# Tail regularity of the complete Ramanujan dual

Source: the user's second ten-transfer program, 23 October 2026, and
S. Waleed Noor, "A Hardy space analysis of the Baez-Duarte criterion for the RH",
https://arxiv.org/abs/1809.09577, Theorems 9 and 12. The source supports the
shifted-density/regularity strategy already checked in ParetoTailAverageCriterion.
The packet annihilator statements cover arbitrary Hilbert vectors. Regularity
of the canonical residual is equivalent to saturation; it is not asserted.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.RamanujanCanonicalOptimizer
open Pareto Pareto.CoefficientStabilization RamanujanTransfer
open ZetaTwoHilbert QRamanujanPackets

/-- The actual residual of projection onto the complete legal packet space. -/
def packetLimitResidual : ThresholdHilbert :=
  hilbertOne - (pPacketClosedSpan {q : ℕ | 1 < q}).starProjection hilbertOne

theorem packetLimitResidual_eq : packetLimitResidual = limitResidual := by
  simp only [packetLimitResidual, p_fullPacketClosedSpan_eq_closedSpace,
    limitResidual, limitProjection]

theorem packetResidual_tendsto :
    Tendsto (fun n => hilbertOne - packetCandidate n) atTop (𝓝 packetLimitResidual) := by
  simp_rw [packetCandidate_eq_projection, packetLimitResidual_eq]
  exact tendsto_const_nhds.sub projection_tendsto

/-- Noor regularity kills every full packet annihilator, not only the canonical one. -/
theorem packet_annihilator_eq_zero_of_tailRegular (h : ThresholdHilbert)
    (ha : ∀ q : ℕ, 1 < q → inner ℝ h (ramanujanPacketHilbert q) = 0)
    (hreg : TailRegular h) : h = 0 := by
  have ho : h ∈ (pPacketClosedSpan {q : ℕ | 1 < q})ᗮ :=
    (p_annihilator_iff _ h).mpr ha
  rw [p_fullPacketClosedSpan_eq_closedSpace] at ho
  exact eq_zero_of_orthogonal_tailRegular h ho hreg

/-- The actual inverse adjoint, with its metric-dependent weight, is the Q test. -/
theorem q_packet_annihilator_eq_zero_of_dual_tailRegular (h : QHilbert)
    (ha : ∀ q : ℕ, 1 < q → inner ℝ h (qRamanujanPacket q) = 0)
    (hreg : TailRegular (pDualFromQ h)) : h = 0 := by
  have ho : pDualFromQ h ∈ (pPacketClosedSpan {q : ℕ | 1 < q})ᗮ :=
    (pDualFromQ_annihilator_iff _ h).mpr ((q_annihilator_iff _ h).mpr ha)
  have hz : pDualFromQ h = 0 := packet_annihilator_eq_zero_of_tailRegular _
    ((p_annihilator_iff _ _).mp ho) hreg
  have hh := congrArg qDualFromPareto hz
  rw [qDualFromPareto_pDualFromQ] at hh
  change h = ZetaTwoParetoTransfer.toParetoCLM.adjoint 0 at hh
  simpa only [map_zero] using hh

theorem packetLimitResidual_zero_iff_energy_zero :
    packetLimitResidual = 0 ↔ limitEnergy = 0 := by
  simpa only [packetLimitResidual_eq] using limitResidual_zero_iff_energy_zero

theorem packetLimitResidual_zero_iff_tailRegular :
    packetLimitResidual = 0 ↔ TailRegular packetLimitResidual := by
  simpa only [packetLimitResidual_eq] using limitResidual_zero_iff_tailRegular

/-- Exact Parseval identity, retaining the endpoint term. -/
theorem packet_tail_difference_energy :
    (∑' n, |tailAverage packetLimitResidual n -
      tailAverage packetLimitResidual (n + 1)| ^ 2) =
      ‖packetLimitResidual‖ ^ 2 - (‖packetLimitResidual‖ ^ 2) ^ 2 := by
  simpa only [packetLimitResidual_eq, limitEnergy, limitResidual, limitProjection,
    RiemannResearch.Analysis.ExhaustiveWalk.limitingError] using
    limitResidual_tail_difference_energy

theorem packet_tailRegular_iff_mass :
    TailRegular packetLimitResidual ↔ Tendsto packetMass atTop (𝓝 1) :=
  packetLimitResidual_zero_iff_tailRegular.symm.trans
    (packetLimitResidual_zero_iff_energy_zero.trans
      (packet_cofinal_mass_iff id tendsto_id).symm)

/-- A concrete infinite signed-tail condition, with the full physical tail. -/
theorem packet_tail_average_summable_iff_mass :
    (∃ L : ℝ, Summable (fun n : ℕ =>
      |((n : ℝ) + 1) *
        (∑' k, paretoWeight (k + n) * hilbertSequence packetLimitResidual (k + n + 1))
        - L| ^ 2)) ↔ Tendsto packetMass atTop (𝓝 1) := by
  have h := limitResidual_zero_iff_tail_average_summable
  rw [← packetLimitResidual_eq] at h
  exact h.symm.trans (packetLimitResidual_zero_iff_energy_zero.trans
    (packet_cofinal_mass_iff id tendsto_id).symm)

theorem riemannHypothesis_of_packet_tailRegular
    (hreg : TailRegular packetLimitResidual) : RiemannHypothesis :=
  packet_riemannHypothesis_of_saturation (packet_tailRegular_iff_mass.mp hreg)

theorem packet_tailRegular_iff_riemannHypothesis
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation) :
    TailRegular packetLimitResidual ↔ RiemannHypothesis :=
  packet_tailRegular_iff_mass.trans
    (packet_cofinal_rh_equivalences hBaezDuarte id tendsto_id).1

end RiemannResearch.RH.RamanujanCanonicalOptimizer
