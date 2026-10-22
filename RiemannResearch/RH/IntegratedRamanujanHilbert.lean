import RiemannResearch.RH.MobiusHilbertCoordinates
import RiemannResearch.RH.ParetoCovariance

/-!
# Actual integrated Ramanujan packets in the complete Pareto Hilbert space

Source: user-provided `RH_Controlled_Conductor_Schur_2026-09-10.md`,
Sections 2 and 6. The carrier uses the complete Pareto weights and the
existing square-summability theorem. Its physical sequence and continuous
Möbius coordinate are identified with the actual arithmetic packet.
-/

open scoped BigOperators
noncomputable section
namespace RiemannResearch.RH.Pareto

/-- The genuine integrated Ramanujan packet in the complete Pareto space. -/
def ramanujanPacketHilbert (q : ℕ) : ThresholdHilbert :=
  sequenceHilbert (ramanujanPacket q) (by
    simpa only [pow_two] using ramanujanPacket_product_weighted_summable q q)

@[simp] theorem hilbertSequence_ramanujanPacketHilbert (q : ℕ) :
    hilbertSequence (ramanujanPacketHilbert q) = ramanujanPacket q := by
  apply hilbertSequence_sequenceHilbert
  simp [ramanujanPacket, residue]

/-- Actual arithmetic packet incidence, as a continuous Hilbert coordinate. -/
theorem mobiusDifferenceCLM_ramanujanPacketHilbert (m q : ℕ)
    (hm : 1 < m) (hq : 0 < q) :
    mobiusDifferenceCLM m (ramanujanPacketHilbert q) =
      if m ∣ q then -(m : ℝ) * (ArithmeticFunction.moebius (q / m) : ℝ)
      else 0 := by
  rw [mobiusDifferenceCLM_apply, hilbertSequence_ramanujanPacketHilbert]
  exact mobiusDifference_packet m q hm hq

end RiemannResearch.RH.Pareto
