import RiemannResearch.RH.ParetoLCMZeroCertificate
import RiemannResearch.RH.ParetoLCMRamanujanCertificate
import RiemannResearch.RH.IntegratedRamanujanHilbert
import RiemannResearch.RH.ParetoResidueMean
import RiemannResearch.RH.ThresholdHilbertMean
import RiemannResearch.Analysis.ProjectionSourceImprovement
import RiemannResearch.Analysis.AffineObservationProjection
import Mathlib.Tactic.Linarith

/-!
# Legal packet refits and exact LCM remainder transitions

Source: standard Hilbert projection and scalar square completion, reusing
the repository's checked ProjectionSourceImprovement. The RH consumer is
the complete LCM target vacancy from the user-provided 9 November 2026
Ramanujan DPP handoff. This supplies an explicit legal finite correction,
with every signed certificate term and optimizer displacement retained.
An asymptotic lower bound for the accumulated gains is not proved.
-/

noncomputable section

namespace RiemannResearch.RH.Pareto.ResidueMellin
open RiemannResearch.Analysis.SingleObservationProjection (affine_target_error_split)
open RiemannResearch.Analysis.ProjectionSourceImprovement

/-- Remove the component of a new packet already in the old legal space. -/
def lcmPacketInnovation (M q : ℕ) : ThresholdHilbert :=
  residual (trialSpace (Nat.lcmUpto M)) (ramanujanPacketHilbert q)

/-- The signed residual source, which need not be supported on prime powers. -/
def lcmPacketCorrelation (M q : ℕ) : ℝ :=
  inner ℝ (hilbertOne - lcmBest M) (ramanujanPacketHilbert q)

/-- The optimal scalar correction in one screened packet direction. -/
def lcmPacketRefit (M q : ℕ) : ThresholdHilbert :=
  lcmBest M + (lcmPacketCorrelation M q / ‖lcmPacketInnovation M q‖ ^ 2) •
    lcmPacketInnovation M q

theorem lcmPacketCorrelation_eq (M q : ℕ) :
    lcmPacketCorrelation M q = ArithmeticFunction.vonMangoldt q -
      inner ℝ (lcmBest M) (ramanujanPacketHilbert q) := by
  have hm : inner ℝ (ramanujanPacketHilbert q) hilbertOne =
      ArithmeticFunction.vonMangoldt q := by
    rw [hilbert_inner_one, hilbertSequence_ramanujanPacketHilbert, paretoMean_ramanujanPacket]
  have hc : inner ℝ hilbertOne (ramanujanPacketHilbert q) =
      ArithmeticFunction.vonMangoldt q := (real_inner_comm _ _).trans hm
  rw [lcmPacketCorrelation, inner_sub_left, hc]

/-- Mixed conductors can have nonzero residual source even when the target source vanishes. -/
theorem lcmPacketCorrelation_of_vonMangoldt_zero (M q : ℕ)
    (hq : ArithmeticFunction.vonMangoldt q = 0) :
    lcmPacketCorrelation M q = -inner ℝ (lcmBest M) (ramanujanPacketHilbert q) := by
  rw [lcmPacketCorrelation_eq, hq, zero_sub]

theorem lcmPacketRefit_mem {M K q : ℕ} (hMK : M ≤ K)
    (hq : q ∈ packetIndex (Nat.lcmUpto K)) :
    lcmPacketRefit M q ∈ trialSpace (Nat.lcmUpto K) :=
  refit_mem (trialSpace (Nat.lcmUpto M)) (trialSpace (Nat.lcmUpto K))
    (lcm_trial_mono hMK) hilbertOne (ramanujanPacketHilbert q)
    (packet_mem_trial _ q hq) _

/-- The correction has exactly the screened Rayleigh gain in the complete Pareto norm. -/
theorem lcmPacketRefit_gain (M q : ℕ) (hq : lcmPacketInnovation M q ≠ 0) :
    lcmError M = ‖hilbertOne - lcmPacketRefit M q‖ ^ 2 +
      (lcmPacketCorrelation M q) ^ 2 / ‖lcmPacketInnovation M q‖ ^ 2 := by
  have h := optimal_refit_gain (trialSpace (Nat.lcmUpto M))
    hilbertOne (ramanujanPacketHilbert q) hq
  change lcmError M - ‖hilbertOne - lcmPacketRefit M q‖ ^ 2 =
    (lcmPacketCorrelation M q) ^ 2 / ‖lcmPacketInnovation M q‖ ^ 2 at h
  linarith only [h]

/-- Exact improvement identity, retaining the difference from the enlarged optimizer. -/
theorem lcmPacketRefit_error_completion {M K q : ℕ} (hMK : M ≤ K)
    (hqK : q ∈ packetIndex (Nat.lcmUpto K)) (hq : lcmPacketInnovation M q ≠ 0) :
    lcmError M = lcmError K +
      (lcmPacketCorrelation M q) ^ 2 / ‖lcmPacketInnovation M q‖ ^ 2 +
      ‖lcmPacketRefit M q - lcmBest K‖ ^ 2 := by
  have h := affine_target_error_split (trialSpace (Nat.lcmUpto K)) hilbertOne
    (lcmPacketRefit M q) (lcmPacketRefit_mem hMK hqK)
  change ‖hilbertOne - lcmPacketRefit M q‖ ^ 2 =
    lcmError K + ‖lcmPacketRefit M q - lcmBest K‖ ^ 2 at h
  linarith only [h, lcmPacketRefit_gain M q hq]

/-- A computable finite upper estimate obtained from an actual legal correction. -/
theorem lcmError_le_packet_refit {M K q : ℕ} (hMK : M ≤ K)
    (hqK : q ∈ packetIndex (Nat.lcmUpto K)) (hq : lcmPacketInnovation M q ≠ 0) :
    lcmError K ≤ lcmError M -
      (lcmPacketCorrelation M q) ^ 2 / ‖lcmPacketInnovation M q‖ ^ 2 := by
  have h := lcmPacketRefit_error_completion hMK hqK hq
  linarith [sq_nonneg ‖lcmPacketRefit M q - lcmBest K‖]

/-- Passing to a larger modulus and a different zero family keeps both signed energy changes. -/
theorem lcm_remainder_packet_refit_transition
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {M K q : ℕ} (hMK : M ≤ K)
    (hqK : q ∈ packetIndex (Nat.lcmUpto K)) (hq : lcmPacketInnovation M q ≠ 0)
    (z : ι → ℂ) (y : κ → ℂ)
    (hzs : ∀ i, 0 < (z i).re) (hz1 : ∀ i, z i ≠ 1) (hz : ∀ i, riemannZeta (z i) = 0)
    (hys : ∀ i, 0 < (y i).re) (hy1 : ∀ i, y i ≠ 1) (hy : ∀ i, riemannZeta (y i) = 0) :
    lcmRemainder y K +
        (lcmPacketCorrelation M q) ^ 2 / ‖lcmPacketInnovation M q‖ ^ 2 +
        ‖lcmPacketRefit M q - lcmBest K‖ ^ 2 =
      lcmRemainder z M +
        (classWeight (lcmResidueIndex M) (Fin.last (lcmResidueIndex M)) -
         classWeight (lcmResidueIndex K) (Fin.last (lcmResidueIndex K))) +
        (certificateEnergy (lcmResidueIndex M) z -
         certificateEnergy (lcmResidueIndex K) y) := by
  have h := lcmPacketRefit_error_completion hMK hqK hq
  unfold lcmError at h
  rw [lcm_best_error_eq M z hzs hz1 hz, lcm_best_error_eq K y hys hy1 hy] at h
  linarith only [h]

end RiemannResearch.RH.Pareto.ResidueMellin
