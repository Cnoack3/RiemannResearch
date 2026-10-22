import RiemannResearch.RH.StepCorrectionContinuum
import RiemannResearch.RH.FractionalPartNormConstant
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith

/-!
# Named constant and sharp complete correction-norm assembly

The actual continuum norm and every signed correction term are identified
before applying the complete transfer inequality. The constant is proved by
the factorial telescope and Mathlib's Stirling limit, not assumed.

Source: Christian Noack, RH_CRT_Optimized_Gains_and_Uniform_Obstruction_20261007.md, correction-norm section. The named constant is independently derived using Mathlib's proved Stirling and harmonic limits.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace RiemannResearch.RH.StepCorrectionNorm
open Pareto

theorem residueEnergy_eq_log_two_pi_sub_gamma :
    residueEnergy = Real.log (2 * Real.pi) - Real.eulerMascheroniConstant := by
  have hs := hasSum_rawResidueCellEnergy.tsum_eq
  change (∑' n, rawResidueCellEnergy n) =
    Real.log (2 * Real.pi) - Real.eulerMascheroniConstant - 1 at hs
  unfold residueEnergy
  rw [hs]
  ring

theorem residualEnergy_eq_log_two_pi_sub_gamma_sub_projection :
    residualEnergy = Real.log (2 * Real.pi) -
      Real.eulerMascheroniConstant - projectionEnergy := by
  rw [residualEnergy_eq, residueEnergy_eq_log_two_pi_sub_gamma]

theorem residualEnergy_gt_one : 1 < residualEnergy := by
  have hle := centeredEnergy_summable.le_tsum 0 (fun n _ => centeredEnergy_nonneg n)
  have hp := centeredEnergy_pos 0
  unfold residualEnergy
  linarith

/-- The initial interval and the first two strictly positive cell variances
give a strict explicit improvement, with the entire later tail retained. -/
theorem residualEnergy_gt_first_cell :
    2 - 2 * (Real.log 2) ^ 2 < residualEnergy := by
  have hs : Summable (fun n => centeredEnergy (n + 1)) :=
    (summable_nat_add_iff 1).2 centeredEnergy_summable
  have hle := hs.le_tsum 0 (fun n _ => centeredEnergy_nonneg (n + 1))
  have hp := centeredEnergy_pos 1
  unfold residualEnergy
  rw [centeredEnergy_summable.tsum_eq_zero_add, centeredEnergy_zero]
  norm_num only [zero_add] at hle
  linarith

theorem first_cell_residual_lower_pos : 0 < 2 - 2 * (Real.log 2) ^ 2 := by
  have hp := centeredEnergy_pos 0
  rw [centeredEnergy_zero] at hp
  linarith

/-- The literal full continuum fractional-part norm is the named constant. -/
theorem fract_energy_eq_log_two_pi_sub_gamma :
    (∫ x in Ioi 0, (Int.fract x) ^ 2 / x ^ 2) =
      Real.log (2 * Real.pi) - Real.eulerMascheroniConstant := by
  rw [fract_energy_integral, residueEnergy_eq_log_two_pi_sub_gamma]

/-- Exact norm assembly for every finite-energy step, with no assumed
analytic constant and no omitted correction term. -/
theorem continuumCorrection_assembly_gamma (f : ℕ → ℝ) (hf0 : f 0 = 0)
    (hf : Summable (fun n => positiveWeight (n + 1) * (f (n + 1)) ^ 2)) (a : ℝ) :
    (∫ x in Ioi 0, continuumCorrectionDensity f a x) =
      stepEnergy (fun n => f (n + 1)) -
        2 * a * correctionSource (fun n => f (n + 1)) +
        a ^ 2 * (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) := by
  rw [continuumCorrection_assembly f hf0 hf a, residueEnergy_eq_log_two_pi_sub_gamma]

/-- Full charge completion is an identity of actual continuum integrals. -/
theorem continuumCorrection_completed_square_gamma (f : ℕ → ℝ) (hf0 : f 0 = 0)
    (hf : Summable (fun n => positiveWeight (n + 1) * (f (n + 1)) ^ 2)) (a : ℝ) :
    (∫ x in Ioi 0, continuumCorrectionDensity f a x) =
      stepEnergy (fun n => f (n + 1)) -
        correctionSource (fun n => f (n + 1)) ^ 2 /
          (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) +
      (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) *
        (a - correctionSource (fun n => f (n + 1)) /
          (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant)) ^ 2 := by
  rw [continuumCorrection_integral f hf0 hf a,
    correctedEnergy_completed_square hf a, residueEnergy_eq_log_two_pi_sub_gamma]

/-- Sharp complete structural transfer with the actual variance denominator. -/
theorem continuumCorrection_transfer_gamma (f : ℕ → ℝ) (hf0 : f 0 = 0)
    (hf : Summable (fun n => positiveWeight (n + 1) * (f (n + 1)) ^ 2)) (a : ℝ) :
    stepEnergy (fun n => f (n + 1)) ≤
      ((Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) /
        (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant - projectionEnergy)) *
      (∫ x in Ioi 0, continuumCorrectionDensity f a x) := by
  rw [continuumCorrection_integral f hf0 hf a,
    ← residueEnergy_eq_log_two_pi_sub_gamma, ← residualEnergy_eq]
  exact correctedEnergy_transfer hf a

/-- The named-constant norm assembly is specialized to the canonical actual
Pareto Hilbert space, with square summability supplied by the Hilbert vector. -/
theorem continuumCorrection_hilbert_gamma (f : ThresholdHilbert) (a : ℝ) :
    (∫ x in Ioi 0, continuumCorrectionDensity (hilbertSequence f) a x) =
      ‖f‖ ^ 2 - 2 * a * correctionSource (fun n => hilbertSequence f (n + 1)) +
        a ^ 2 * (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) := by
  have hf : Summable (fun n => positiveWeight (n + 1) *
      (hilbertSequence f (n + 1)) ^ 2) := by
    simpa only [hilbertSequence_weighted_square] using hilbert_coordinate_square_summable f
  rw [continuumCorrection_assembly_gamma (hilbertSequence f)
    (hilbertSequence_zero f) hf a, stepEnergy_hilbert]

/-- A closed strict upper bound, proved from the first actual cell variance. -/
theorem correctionTransferFactor_lt_first_cell :
    residueEnergy / residualEnergy < residueEnergy / (2 - 2 * (Real.log 2) ^ 2) := by
  exact div_lt_div_of_pos_left residueEnergy_pos
    first_cell_residual_lower_pos residualEnergy_gt_first_cell

/-- Strict improvement over the original squared transfer factor. -/
theorem correctionTransferFactor_lt_residueEnergy :
    residueEnergy / residualEnergy < residueEnergy := by
  have hb : 0 < residualEnergy := by linarith [residualEnergy_ge_one]
  apply (div_lt_iff₀ hb).2
  nlinarith [mul_pos residueEnergy_pos (sub_pos.mpr residualEnergy_gt_one)]

end RiemannResearch.RH.StepCorrectionNorm
