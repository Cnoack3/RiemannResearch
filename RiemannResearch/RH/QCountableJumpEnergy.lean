/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.CountableJumpEnergy
import RiemannResearch.RH.QReciprocalWeightedEnergy

/-!
# Full countable raw-source Dirichlet control in the actual Q space

Source: the countable prime-resampling formalization requested by the user,
27 October 2026. The exact square-root weight identity precedes the source
estimate. The only generic inputs are symmetry and the full countable exit
rate; the arithmetic prime-kernel module is the intended unconditional consumer.
-/

noncomputable section
open scoped BigOperators ENNReal
namespace RiemannResearch.RH.QCountableJumpEnergy
open ZetaTwoHilbert ZetaTwoProbability QPolylogTailEnergy QShiftedReciprocal
open RiemannResearch.Analysis.LogTailWeights
open RiemannResearch.Analysis.CountableJumpEnergy

/-- The literal weighted physical sequence sqrt(n/(8+log n)^2) f(n). -/
def qWeightedSequence (f : QHilbert) (n : ℕ) : ℝ :=
  Real.sqrt (polylogTailProfile 2 n) * qSequence f n

theorem qWeightedSequence_sq (f : QHilbert) (n : ℕ) :
    qWeightedSequence f n ^ 2 = polylogTailProfile 2 n * qSequence f n ^ 2 := by
  rw [qWeightedSequence, mul_pow, Real.sq_sqrt (polylogTailProfile_nonneg 2 n)]

theorem qWeightedSequence_square_term (f : QHilbert) (n : ℕ) :
    positiveQWeight n * qWeightedSequence f n ^ 2 = polylogWeightedEnergyTerm 2 f n := by
  rw [qWeightedSequence_sq, polylogWeightedEnergyTerm]
  ring

theorem weighted_exit_square_term (f : QHilbert) (n : ℕ) :
    ENNReal.ofReal (positiveQWeight n * ((n : ℝ) + 1)) *
      ENNReal.ofReal (qWeightedSequence f n ^ 2) =
        ENNReal.ofReal (((n : ℝ) + 1) * polylogWeightedEnergyTerm 2 f n) := by
  rw [← ENNReal.ofReal_mul (mul_nonneg (positiveQWeight_nonneg n) (by positivity)),
    qWeightedSequence_sq, polylogWeightedEnergyTerm]
  congr 1
  ring

/-- A symmetric countable flow with the actual linear Q exit envelope gives
the paper's raw weighted source bound, with no finite-head truncation. -/
theorem countableRawSourceJumpEnergy_le
    (W : ℕ → ℕ → ℝ≥0∞) (f : QHilbert)
    (hsym : ∀ n m, W n m = W m n)
    (hrate : ∀ n, (∑' m, W n m) ≤
      ENNReal.ofReal (positiveQWeight n * ((n : ℝ) + 1))) :
    countableJumpEnergy W (qWeightedSequence (B f)) ≤ ENNReal.ofReal (‖f‖ ^ 2 / 32) := by
  let F (n : ℕ) : ℝ := ((n : ℝ) + 1) * polylogWeightedEnergyTerm 2 (B f) n
  have hF0 (n : ℕ) : 0 ≤ F n :=
    mul_nonneg (by positivity) (polylogWeightedEnergyTerm_nonneg 2 (B f) n)
  have hFs : Summable F :=
    reciprocal_rateWeightedEnergy_summable f (fun n => (n : ℝ) + 1)
      (fun n => by positivity) (fun n => le_rfl)
  have hFb : (∑' n, F n) ≤ ‖f‖ ^ 2 / 64 :=
    reciprocal_rateWeightedEnergy_le f (fun n => (n : ℝ) + 1)
      (fun n => by positivity) (fun n => le_rfl)
  calc
    _ ≤ 2 * ∑' n, ENNReal.ofReal (positiveQWeight n * ((n : ℝ) + 1)) *
        ENNReal.ofReal (qWeightedSequence (B f) n ^ 2) :=
      countableJumpEnergy_le_of_rate_le W _ _ hsym hrate
    _ = 2 * ENNReal.ofReal (∑' n, F n) := by
      congr 1
      rw [ENNReal.ofReal_tsum_of_nonneg hF0 hFs]
      apply tsum_congr
      intro n
      exact weighted_exit_square_term (B f) n
    _ ≤ 2 * ENNReal.ofReal (‖f‖ ^ 2 / 64) :=
      mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hFb) (by positivity)
    _ = ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal (‖f‖ ^ 2 / 64) := by
      exact congrArg (fun t : ℝ≥0∞ => t * ENNReal.ofReal (‖f‖ ^ 2 / 64))
        (by norm_num : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ))
    _ = ENNReal.ofReal (‖f‖ ^ 2 / 32) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring

theorem countableRawSourceJumpEnergy_ne_top
    (W : ℕ → ℕ → ℝ≥0∞) (f : QHilbert)
    (hsym : ∀ n m, W n m = W m n)
    (hrate : ∀ n, (∑' m, W n m) ≤
      ENNReal.ofReal (positiveQWeight n * ((n : ℝ) + 1))) :
    countableJumpEnergy W (qWeightedSequence (B f)) ≠ ⊤ := by
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (countableRawSourceJumpEnergy_le W f hsym hrate)

end RiemannResearch.RH.QCountableJumpEnergy
