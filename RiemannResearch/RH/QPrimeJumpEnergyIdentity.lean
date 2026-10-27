/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ReversibleCountableEnergyIdentity
import RiemannResearch.RH.PrimeResamplingKernel
import RiemannResearch.RH.QPrimeResamplingFormula

/-!
# Exact identity of actual prime-jump and conditional-projection energies

Source: the user's countable prime-resampling agenda, 27 October 2026.
The actual arithmetic conductance is identified with the actual geometric
conditional projection. All signed rearrangements use proved absolute
summability; the complete Dirichlet form is ENNReal-valued.
-/

noncomputable section
open scoped BigOperators ENNReal
namespace RiemannResearch.RH.PrimeResampling
open ZetaTwoHilbert
open RiemannResearch.Analysis.CountableJumpEnergy

/-- The actual complete countable prime-resampling Dirichlet form. -/
def dirichletEnergy (g : ℕ → ℝ) : ℝ≥0∞ := countableJumpEnergy primeFlow g

/-- The exact full sum of the one-prime forms, without a finiteness assumption. -/
theorem dirichletEnergy_eq_prime_sum (g : ℕ → ℝ) :
    dirichletEnergy g = ∑' p : ℕ,
      countableJumpEnergy (fun n m => ENNReal.ofReal (primeConductance p n m)) g := by
  exact countableJumpEnergy_tsum_weights
    (fun p n m => ENNReal.ofReal (primeConductance p n m)) g

end RiemannResearch.RH.PrimeResampling

namespace RiemannResearch.RH.QPrimeResampling
open ZetaTwoHilbert PrimeResampling
open RiemannResearch.Analysis.CountableJumpEnergy

/-- The exact signed generator row of one actual arithmetic prime update. -/
theorem primeConductance_residual_row (p n : ℕ) (hp : p.Prime) (f : QHilbert) :
    (∑' m, primeConductance p n m * (qSequence f n - qSequence f m)) =
      positiveQWeight n * (qSequence f n - qSequence (C p f) n) := by
  by_cases hn : n = 0
  · simp [hn, primeConductance_zero_left]
  rw [primeConductance_weighted_row_real p n hp hn
    (fun m => qSequence f n - qSequence f m) (sub_self _)]
  congr 1
  calc
    _ = ∑' k, (geometricMass p k * qSequence f n -
        geometricMass p k * qSequence f (replaceValuation p n k)) := by
      apply tsum_congr
      intro k
      ring
    _ = (∑' k, geometricMass p k * qSequence f n) -
        ∑' k, geometricMass p k * qSequence f (replaceValuation p n k) :=
      ((geometricMass_hasSum p hp).summable.mul_right (qSequence f n)).tsum_sub
        (geometricAverage_summable p n hp hn f)
    _ = _ := by
      rw [tsum_mul_right, geometricMass_tsum p hp, one_mul, qSequence_C p n hp hn f]

/-- Every one-prime kernel has a finite complete square budget on QHilbert. -/
theorem primeConductance_first_square_summable (p : ℕ) (f : QHilbert) :
    Summable (fun e : ℕ × ℕ => primeConductance p e.1 e.2 * (qSequence f e.1) ^ 2) := by
  exact kernel_first_square_summable (primeConductance p) (qSequence f) positiveQWeight
    (primeConductance_nonneg p) (primeConductance_row_summable p)
    (primeConductance_row_real_le_Q p) (qSequence_square_summable f)

/-- One actual geometric prime update has exactly the conditional-projection
residual energy, with the correct normalization one half. -/
theorem primeJumpEnergy_eq_projection_energy (p : ℕ) (hp : p.Prime) (f : QHilbert) :
    countableJumpEnergy (fun n m => ENNReal.ofReal (primeConductance p n m))
      (qSequence f) = ENNReal.ofReal (‖f - C p f‖ ^ 2) := by
  rw [countableJumpEnergy_eq_signed_rows (primeConductance p) (qSequence f)
    (primeConductance_nonneg p) (primeConductance_symm p)
    (primeConductance_first_square_summable p f)]
  simp_rw [primeConductance_residual_row p _ hp f]
  rw [C_energy_eq, qInner_weighted]
  congr 1
  apply tsum_congr
  intro n
  have hs : qSequence (f - C p f) n = qSequence f n - qSequence (C p f) n := by
    change qSequenceLinear (f - C p f) n = _
    rw [map_sub]
    rfl
  rw [hs]
  ring

/-- Exact identification with the full sum of actual coordinate projection
energies; no global summability assumption is made. -/
theorem dirichletEnergy_qSequence_eq (f : QHilbert) :
    dirichletEnergy (qSequence f) =
      ∑' p : ℕ, if p.Prime then ENNReal.ofReal (‖f - C p f‖ ^ 2) else 0 := by
  rw [dirichletEnergy_eq_prime_sum]
  apply tsum_congr
  intro p
  by_cases hp : p.Prime
  · rw [if_pos hp]
    exact primeJumpEnergy_eq_projection_energy p hp f
  · simp only [if_neg hp, countableJumpEnergy, primeConductance_nonprime p _ _ hp,
      ENNReal.ofReal_zero, zero_mul, tsum_zero]

end RiemannResearch.RH.QPrimeResampling
