import RiemannResearch.Analysis.SequenceHeadTail
import RiemannResearch.RH.ExactHeadResidualTail
import RiemannResearch.RH.ParetoResidualShell
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Signed finite-head and complete-tail error budgets

Source: user-requested fourth Ramanujan transfer program, 23 October 2026.
The head need not interpolate the target. Its signed pairing with the actual
canonical residual remains in the identity and in the sharp tail lower bound.
No tail or mixed term is replaced by a truncated norm.
-/

noncomputable section
open Filter
open scoped BigOperators Topology


namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis.SequenceHeadTail

theorem hilbert_head_tail_energy (f : ThresholdHilbert) (N : ℕ) :
    ‖f‖ ^ 2 = headSquare N f + ‖hilbertTailShift f N‖ ^ 2 := by
  rw [hilbertTailShift_norm_sq]
  unfold headSquare
  ring

theorem hilbert_headSquare_le (f : ThresholdHilbert) (N : ℕ) :
    headSquare N f ≤ ‖f‖ ^ 2 := by
  rw [hilbert_head_tail_energy f N]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Cauchy--Schwarz on the genuine complete tails, without exact-head assumptions. -/
theorem hilbert_tail_pairing_sq_le (f g : ThresholdHilbert) (N : ℕ) :
    (inner ℝ (hilbertTailShift f N) (hilbertTailShift g N)) ^ 2 ≤
      ‖hilbertTailShift f N‖ ^ 2 * ‖hilbertTailShift g N‖ ^ 2 := by
  have h := abs_real_inner_le_norm (hilbertTailShift f N) (hilbertTailShift g N)
  have hs := (sq_le_sq₀ (abs_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  simpa only [sq_abs, mul_pow] using hs

namespace CoefficientStabilization

def residualErrorHeadPairing (N : ℕ) (f : ThresholdHilbert) : ℝ :=
  headPair N limitResidual (hilbertOne - f : ThresholdHilbert)

def approximateHeadEnergy (N : ℕ) (f : ThresholdHilbert) : ℝ :=
  headSquare N (hilbertOne - f : ThresholdHilbert)

theorem approximateHeadEnergy_nonneg (N : ℕ) (f : ThresholdHilbert) :
    0 ≤ approximateHeadEnergy N f := headSquare_nonneg _ _

theorem approximateHeadEnergy_physical (N : ℕ) (f : ThresholdHilbert) :
    approximateHeadEnergy N f =
      ∑ n ∈ Finset.range N, positiveWeight (n + 1) *
        (1 - hilbertSequence f (n + 1)) ^ 2 := by
  unfold approximateHeadEnergy headSquare
  apply Finset.sum_congr rfl
  intro n hn
  change ((hilbertOne - f : ThresholdHilbert) n) ^ 2 = _
  rw [← hilbertSequence_weighted_square]
  congr 1
  change (hilbertSequenceLinear (hilbertOne - f) (n + 1)) ^ 2 = _
  rw [map_sub]
  change (hilbertSequence hilbertOne (n + 1) - hilbertSequence f (n + 1)) ^ 2 = _
  rw [hilbertOne_sequence]
  simp [zeroAnchor]

/-- The canonical residual energy splits into a signed head term and complete tail pairing. -/
theorem residual_signed_head_tail (N : ℕ) {f : ThresholdHilbert} (hf : f ∈ closedSpace) :
    limitEnergy = residualErrorHeadPairing N f +
      inner ℝ (hilbertTailShift limitResidual N) (hilbertTailShift (hilbertOne - f) N) := by
  simpa only [residual_error_pairing hf, residualErrorHeadPairing, headPair,
    hilbertShellPairing, Nat.add_zero] using
    (hilbert_head_tail_pairing limitResidual (hilbertOne - f) N).symm

/-- Sharp complete-tail lower bound with the signed head pairing retained. -/
theorem residual_approximate_head_tail_bound (N : ℕ) {f : ThresholdHilbert}
    (hf : f ∈ closedSpace) :
    (limitEnergy - residualErrorHeadPairing N f) ^ 2 ≤
      residualTailEnergy N * (‖hilbertOne - f‖ ^ 2 - approximateHeadEnergy N f) := by
  have hi := residual_signed_head_tail N hf
  have he : inner ℝ (hilbertTailShift limitResidual N)
      (hilbertTailShift (hilbertOne - f) N) = limitEnergy - residualErrorHeadPairing N f := by
    linarith
  have h := hilbert_tail_pairing_sq_le limitResidual (hilbertOne - f) N
  rw [he, hilbertTailShift_norm_sq (hilbertOne - f) N] at h
  exact h

theorem residual_approximate_head_full_bound (N : ℕ) {f : ThresholdHilbert}
    (hf : f ∈ closedSpace) :
    (limitEnergy - residualErrorHeadPairing N f) ^ 2 ≤
      residualTailEnergy N * ‖hilbertOne - f‖ ^ 2 := by
  apply (residual_approximate_head_tail_bound N hf).trans
  exact mul_le_mul_of_nonneg_left (sub_le_self _ (approximateHeadEnergy_nonneg N f))
    (residualTailEnergy_nonneg N)

/-- The complementary head estimate uses exactly the head energy of the canonical residual. -/
theorem residual_head_pairing_bound (N : ℕ) (f : ThresholdHilbert) :
    (residualErrorHeadPairing N f) ^ 2 ≤
      (limitEnergy - residualTailEnergy N) * approximateHeadEnergy N f := by
  have he : headSquare N limitResidual = limitEnergy - residualTailEnergy N := by
    have h := hilbertTailShift_norm_sq limitResidual N
    change residualTailEnergy N = limitEnergy - headSquare N limitResidual at h
    linarith
  simpa only [residualErrorHeadPairing, approximateHeadEnergy, he] using
    headPair_sq_le N limitResidual (hilbertOne - f : ThresholdHilbert)

/-- A fully quantitative replacement for the exact-head obstruction. -/
theorem residual_approximate_head_energy_bound (N : ℕ) {f : ThresholdHilbert}
    (hf : f ∈ closedSpace) :
    limitEnergy ^ 2 ≤
      2 * (limitEnergy - residualTailEnergy N) * approximateHeadEnergy N f +
      2 * residualTailEnergy N * (‖hilbertOne - f‖ ^ 2 - approximateHeadEnergy N f) := by
  have hh := residual_head_pairing_bound N f
  have ht := residual_approximate_head_tail_bound N hf
  nlinarith [sq_nonneg (limitEnergy - 2 * residualErrorHeadPairing N f)]

theorem residual_approximate_head_soft_bound (N : ℕ) {f : ThresholdHilbert}
    (hf : f ∈ closedSpace) :
    limitEnergy ^ 2 ≤ 2 * limitEnergy * approximateHeadEnergy N f +
      2 * residualTailEnergy N * ‖hilbertOne - f‖ ^ 2 := by
  have h := residual_approximate_head_energy_bound N hf
  have hp := mul_nonneg (residualTailEnergy_nonneg N) (approximateHeadEnergy_nonneg N f)
  nlinarith

/-- A signed head-pairing tolerance gives a sharp robust version of the tail product test. -/
theorem residual_approximate_head_tolerance (N : ℕ) {f : ThresholdHilbert}
    (hf : f ∈ closedSpace) (η : ℝ) (hη : η ≤ limitEnergy)
    (hhead : |residualErrorHeadPairing N f| ≤ η) :
    (limitEnergy - η) ^ 2 ≤
      residualTailEnergy N * (‖hilbertOne - f‖ ^ 2 - approximateHeadEnergy N f) := by
  have hb : residualErrorHeadPairing N f ≤ η := (le_abs_self _).trans hhead
  have hleft : 0 ≤ limitEnergy - η := sub_nonneg.mpr hη
  have hright : 0 ≤ limitEnergy - residualErrorHeadPairing N f := by linarith
  apply le_trans _ (residual_approximate_head_tail_bound N hf)
  exact (sq_le_sq₀ hleft hright).mpr (by linarith)

end CoefficientStabilization
end RiemannResearch.RH.Pareto
