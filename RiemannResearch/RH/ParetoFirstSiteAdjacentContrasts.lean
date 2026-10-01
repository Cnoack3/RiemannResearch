/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoFirstSiteAdjacentRegression
import RiemannResearch.RH.ParetoCoprimeDefectScreening
import RiemannResearch.Analysis.DyadicWeightedContrast

/-!
# Adjacent-weight contrasts and exact moving screened odd-charge certificates

Source: independently derived finite assembly of the user's October 1
continuation, Bessel's inequality, and ParetoCoprimeDefectScreening's exact
full-dictionary CRT row identity. These support the proof strategy and
statements, not a novelty or unconditional growth claim.

Cancellation of the diagonal source occurs before squaring. The complete
signed fixed-base cross term remains in the exact certificate equality.
Only at the summability level can Bessel remove the fixed base. The moving
row is equivalently a screened odd reciprocal-square charge; every old
inverse-Gram coefficient, including composite rows, remains.

The final finite unbounded-budget hypothesis is the explicit Open arithmetic
provider. No prime density estimate or raw-source positivity proves it.
-/

noncomputable section
open Filter
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.WeightedScalarEnergy
open RiemannResearch.Analysis.DyadicWeightedContrast
open RiemannResearch.Analysis.OrthogonalPairingEnergy
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.RH.Pareto.IntegerDPP

noncomputable def adjacentPrimeBalancedTest (N k : ℕ) (f : ℕ → ℝ) (i : ℕ) : ℝ :=
  f i - (product (Finset.range k) (fun q => adjacentPrimeRegressionWeight (N+q))
    (fun q => factorialPrimeDelta (N+q)) f / adjacentPrimeSurvivorSource N k) *
      factorialPrimeDelta (N+i)
noncomputable def adjacentPrimeContrastEnergy (N k : ℕ) (f : ℕ → ℝ) : ℝ :=
  square (Finset.range k) (fun i => adjacentPrimeRegressionWeight (N+i))
    (adjacentPrimeBalancedTest N k f)
noncomputable def adjacentPrimeContrastPairing (N k : ℕ) (f : ℕ → ℝ) : ℝ :=
  product (Finset.range k) (fun i => adjacentPrimeRegressionWeight (N+i))
    (adjacentPrimeBalancedTest N k f) (fun i => factorialPrimeError (N+i))
noncomputable def adjacentPrimeContrastCertificate (N k : ℕ) (f : ℕ → ℝ) : ℝ :=
  (adjacentPrimeContrastPairing N k f)^2 / adjacentPrimeContrastEnergy N k f

theorem adjacentPrimeBalancedTest_source_zero (N k : ℕ) (f : ℕ → ℝ) :
    product (Finset.range k) (fun i => adjacentPrimeRegressionWeight (N+i))
      (fun i => factorialPrimeDelta (N+i)) (adjacentPrimeBalancedTest N k f) = 0 :=
  centered_product_zero _ _ _ _ (fun i _ => adjacentPrimeRegressionWeight_nonneg (N+i))

theorem adjacentPrimeContrastPairing_eq_survivor (N k : ℕ) (f : ℕ → ℝ) :
    adjacentPrimeContrastPairing N k f =
      product (Finset.range k) (fun i => adjacentPrimeRegressionWeight (N+i))
        (adjacentPrimeBalancedTest N k f) (fun i => schurEta (N+i+1)) := by
  have hca : product (Finset.range k) (fun i => adjacentPrimeRegressionWeight (N+i))
      (adjacentPrimeBalancedTest N k f) (fun i => factorialPrimeDelta (N+i)) = 0 := by
    simpa only [product, mul_comm, mul_left_comm, mul_assoc] using
      adjacentPrimeBalancedTest_source_zero N k f
  have he : adjacentPrimeContrastPairing N k f =
      product (Finset.range k) (fun i => adjacentPrimeRegressionWeight (N+i))
        (adjacentPrimeBalancedTest N k f)
        (fun i => schurEta (N+i+1)-factorialPrimeDelta (N+i)) := by
    unfold adjacentPrimeContrastPairing product
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only
    by_cases hp : Nat.Prime (N+i+3)
    · have hh : schurEta (N+i+1) =
          factorialPrimeDelta (N+i)+factorialPrimeError (N+i) := by
        simpa only [factorialPrimeDelta] using factorialPrimeError_decomposition (N+i) hp
      rw [hh]
      ring
    · simp [adjacentPrimeRegressionWeight, hp]
  rw [he]
  have hh := product_sub_right (Finset.range k)
    (fun i => adjacentPrimeRegressionWeight (N+i)) (adjacentPrimeBalancedTest N k f)
    (fun i => schurEta (N+i+1)) (fun i => factorialPrimeDelta (N+i)) 1
  simpa only [one_mul, hca, sub_zero] using hh

theorem adjacentPrimeContrastCertificate_nonneg (N k : ℕ) (f : ℕ → ℝ) :
    0 ≤ adjacentPrimeContrastCertificate N k f :=
  div_nonneg (sq_nonneg _) (square_nonneg _ _ _
    (fun i _ => adjacentPrimeRegressionWeight_nonneg (N+i)))

theorem adjacentPrimeContrastCertificate_le_variance (N k : ℕ) (f : ℕ → ℝ) :
    adjacentPrimeContrastCertificate N k f ≤ adjacentPrimeSurvivorVariance N k := by
  unfold adjacentPrimeContrastCertificate
  rw [adjacentPrimeContrastPairing_eq_survivor]
  exact balanced_contrast_le_square _ _ _ _ _ _
    (fun i _ => adjacentPrimeRegressionWeight_nonneg (N+i))
    (adjacentPrimeBalancedTest_source_zero N k f)

noncomputable def adjacentPrimeFixedPairing (N k : ℕ) (f : ℕ → ℝ)
    (z : RiemannResearch.RH.Pareto.ThresholdHilbert) : ℝ :=
  product (Finset.range k) (fun i => adjacentPrimeRegressionWeight (N+i))
    (adjacentPrimeBalancedTest N k f) (fun i => inner ℝ (tailInnovation (N+i+1)) z)

set_option maxHeartbeats 1000000 in
theorem adjacentPrimeFixedPairing_dyadic_summable (f : ℕ → ℕ → ℝ)
    (z : RiemannResearch.RH.Pareto.ThresholdHilbert) :
    Summable (fun j => (adjacentPrimeFixedPairing (2^j) (2^j) (f j) z)^2 /
      adjacentPrimeContrastEnergy (2^j) (2^j) (f j)) := by
  have hs : Summable (fun n =>
      (inner ℝ (tailInnovation (n+1)) z)^2 / schurSigma (n+1)) :=
    (summable_nat_add_iff 1).mpr (tailInnovation_fixed_pairing_energy_summable z)
  have he : Summable (fun n => adjacentPrimeRegressionWeight n *
      (inner ℝ (tailInnovation (n+1)) z)^2) := by
    apply hs.of_nonneg_of_le
    · intro n
      exact mul_nonneg (adjacentPrimeRegressionWeight_nonneg n) (sq_nonneg _)
    · intro n
      calc
        _ ≤ primeSchurWeight n * (inner ℝ (tailInnovation (n+1)) z)^2 :=
          mul_le_mul_of_nonneg_right (adjacentPrimeRegressionWeight_le n) (sq_nonneg _)
        _ ≤ _ := by
          by_cases hp : Nat.Prime (n+3)
          · simp [primeSchurWeight, hp, div_eq_mul_inv, mul_comm]
          · simp only [primeSchurWeight, if_neg hp, zero_mul]
            exact div_nonneg (sq_nonneg _) (schurSigma_pos _).le
  exact dyadic_pairing_energy_summable adjacentPrimeRegressionWeight
    (fun n => inner ℝ (tailInnovation (n+1)) z)
    (fun j => adjacentPrimeBalancedTest (2^j) (2^j) (f j))
    adjacentPrimeRegressionWeight_nonneg he

noncomputable def adjacentPrimeMovingCRTContrastPairing (N k : ℕ) (f : ℕ → ℝ) : ℝ :=
  product (Finset.range k) (fun i => adjacentPrimeRegressionWeight (N+i))
    (adjacentPrimeBalancedTest N k f)
    (fun i => ∑ m ∈ Finset.range (N+i), factorialPrimeCrossGram (N+i) m)
noncomputable def adjacentPrimeMovingCRTContrastCertificate (N k : ℕ)
    (f : ℕ → ℝ) : ℝ :=
  (adjacentPrimeMovingCRTContrastPairing N k f)^2 / adjacentPrimeContrastEnergy N k f

theorem adjacentPrimeMovingCRTContrastPairing_eq_sub_base (N k : ℕ) (f : ℕ → ℝ) :
    adjacentPrimeMovingCRTContrastPairing N k f =
      adjacentPrimeContrastPairing N k f -
        adjacentPrimeFixedPairing N k f (infiniteCoprimeCertificate (Nat.factorial 2)) := by
  unfold adjacentPrimeMovingCRTContrastPairing adjacentPrimeContrastPairing
    adjacentPrimeFixedPairing product
  simp_rw [factorialPrimeError_eq_base_add_crossGram]
  simp only [mul_add, Finset.sum_add_distrib]
  ring

theorem adjacentPrimeMovingCRTContrast_dyadic_summable_iff (f : ℕ → ℕ → ℝ) :
    Summable (fun j => adjacentPrimeMovingCRTContrastCertificate (2^j) (2^j) (f j)) ↔
      Summable (fun j => adjacentPrimeContrastCertificate (2^j) (2^j) (f j)) := by
  have hb : Summable (fun j =>
      (-(adjacentPrimeFixedPairing (2^j) (2^j) (f j)
        (infiniteCoprimeCertificate (Nat.factorial 2))))^2 /
      adjacentPrimeContrastEnergy (2^j) (2^j) (f j)) := by
    simpa only [neg_sq] using adjacentPrimeFixedPairing_dyadic_summable f
      (infiniteCoprimeCertificate (Nat.factorial 2))
  unfold adjacentPrimeMovingCRTContrastCertificate adjacentPrimeContrastCertificate
  simp_rw [adjacentPrimeMovingCRTContrastPairing_eq_sub_base]
  simpa only [sub_eq_add_neg] using weighted_square_add_summable_iff
    (fun j => adjacentPrimeContrastPairing (2^j) (2^j) (f j))
    (fun j => -(adjacentPrimeFixedPairing (2^j) (2^j) (f j)
      (infiniteCoprimeCertificate (Nat.factorial 2))))
    (fun j => adjacentPrimeContrastEnergy (2^j) (2^j) (f j))
    (fun j => square_nonneg _ _ _ (fun i _ => adjacentPrimeRegressionWeight_nonneg (2^j+i))) hb

theorem riemannHypothesis_of_adjacentMovingCRTContrast_not_summable
    (f : ℕ → ℕ → ℝ)
    (hdiv : ¬ Summable (fun j =>
      adjacentPrimeMovingCRTContrastCertificate (2^j) (2^j) (f j))) : RiemannHypothesis := by
  have hc : ¬ Summable (fun j => adjacentPrimeContrastCertificate (2^j) (2^j) (f j)) :=
    fun hs => hdiv ((adjacentPrimeMovingCRTContrast_dyadic_summable_iff f).mpr hs)
  exact riemannHypothesis_of_dyadic_prime_block_lower_bound _
    (fun j => adjacentPrimeContrastCertificate_nonneg _ _ (f j)) hc
    (fun j => (adjacentPrimeContrastCertificate_le_variance _ _ (f j)).trans
      (adjacentPrimeSurvivorVariance_le _ _))

theorem adjacentPrimeMovingCRTContrastPairing_eq_full_row (N k : ℕ) (f : ℕ → ℝ) :
    adjacentPrimeMovingCRTContrastPairing N k f =
      product (Finset.range k) (fun i => adjacentPrimeRegressionWeight (N+i))
        (adjacentPrimeBalancedTest N k f) (fun i => factorialCrossGramRow (N+i)) := by
  have hca : product (Finset.range k) (fun i => adjacentPrimeRegressionWeight (N+i))
      (adjacentPrimeBalancedTest N k f) (fun i => factorialPrimeDelta (N+i)) = 0 := by
    simpa only [product, mul_comm, mul_left_comm, mul_assoc] using
      adjacentPrimeBalancedTest_source_zero N k f
  have he : product (Finset.range k) (fun i => adjacentPrimeRegressionWeight (N+i))
      (adjacentPrimeBalancedTest N k f) (fun i => factorialCrossGramRow (N+i)) =
      adjacentPrimeMovingCRTContrastPairing N k f +
        product (Finset.range k) (fun i => adjacentPrimeRegressionWeight (N+i))
          (adjacentPrimeBalancedTest N k f) (fun i => factorialPrimeDelta (N+i)) := by
    unfold factorialCrossGramRow adjacentPrimeMovingCRTContrastPairing product
    simp only [Finset.sum_range_succ, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hp : Nat.Prime (N+i+3)
    · rw [factorialPrimeCrossGram_diag (N+i) hp]
      ring
    · simp [adjacentPrimeRegressionWeight, hp]
  rw [hca, add_zero] at he
  exact he.symm

/-- The full moving CRT packet becomes one explicit screened odd charge.
Every inverse-Gram coefficient on the old full dictionary is retained. -/
theorem adjacentPrimeMovingCRTContrastPairing_eq_screened_charge
    (N k : ℕ) (f : ℕ → ℝ) :
    adjacentPrimeMovingCRTContrastPairing N k f =
      product (Finset.range k) (fun i => adjacentPrimeRegressionWeight (N+i))
        (adjacentPrimeBalancedTest N k f)
        (fun i => coprimeObservationDefect 2 (N+i+3) -
          ∑ q : Fin (N+i+1),
            inverseCoeff (finiteTailAtom_independent (N+i+1)) (tailAtom (N+i+1)) q *
              coprimeObservationDefect 2 (q.val+2)) := by
  rw [adjacentPrimeMovingCRTContrastPairing_eq_full_row]
  simp_rw [factorialCrossGramRow_eq_screened_defect]

theorem adjacentPrimeContrastCertificate_eq_moving_signed_square (N k : ℕ)
    (f : ℕ → ℝ) :
    adjacentPrimeContrastCertificate N k f =
      adjacentPrimeMovingCRTContrastCertificate N k f +
        2 * adjacentPrimeMovingCRTContrastPairing N k f *
          adjacentPrimeFixedPairing N k f (infiniteCoprimeCertificate (Nat.factorial 2)) /
            adjacentPrimeContrastEnergy N k f +
        (adjacentPrimeFixedPairing N k f
          (infiniteCoprimeCertificate (Nat.factorial 2)))^2 /
            adjacentPrimeContrastEnergy N k f := by
  have he := adjacentPrimeMovingCRTContrastPairing_eq_sub_base N k f
  have hp : adjacentPrimeContrastPairing N k f =
      adjacentPrimeMovingCRTContrastPairing N k f +
        adjacentPrimeFixedPairing N k f (infiniteCoprimeCertificate (Nat.factorial 2)) := by
    linarith
  unfold adjacentPrimeContrastCertificate adjacentPrimeMovingCRTContrastCertificate
  rw [hp]
  ring

/-- The weakest finite aggregate provider for this selected actual moving test:
its nonnegative certificate prefixes must be unbounded. -/
theorem riemannHypothesis_of_adjacentMovingCRTContrast_unbounded
    (f : ℕ → ℕ → ℝ)
    (hbudget : ∀ B : ℝ, ∃ J : ℕ, B <
      ∑ j ∈ Finset.range J, adjacentPrimeMovingCRTContrastCertificate (2^j) (2^j) (f j)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_adjacentMovingCRTContrast_not_summable f
  intro hs
  obtain ⟨J, hJ⟩ := hbudget (∑' j, adjacentPrimeMovingCRTContrastCertificate (2^j) (2^j) (f j))
  have hb : (∑ j ∈ Finset.range J,
      adjacentPrimeMovingCRTContrastCertificate (2^j) (2^j) (f j)) ≤
      ∑' j, adjacentPrimeMovingCRTContrastCertificate (2^j) (2^j) (f j) :=
    hs.sum_le_tsum (Finset.range J) (fun j _ =>
    div_nonneg (sq_nonneg _) (square_nonneg _ _ _
      (fun i _ => adjacentPrimeRegressionWeight_nonneg (2^j+i))))
  linarith

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
