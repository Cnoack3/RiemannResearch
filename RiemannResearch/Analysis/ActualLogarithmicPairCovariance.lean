import RiemannResearch.Analysis.ActualLogarithmicPairSampling
import RiemannResearch.Analysis.ActualPrimePowerWeightedRows

/-!
# Actual pair covariance with the arithmetic rows discharged

Every analytic zero occurrence and both arithmetic divisibility directions are
retained. The existing actual Landau theorem supplies the height error, and the
proved elementary Mertens row bound supplies both weighted arithmetic budgets.
The exponential density estimate is the sole remaining analytic hypothesis.
-/

noncomputable section
open Set
open scoped BigOperators

namespace RiemannResearch.Analysis.ActualDirichletPolynomialGram

open ActualZeroOrdinate ZeroSamplingQuadratic ActualPrimePowerWeightedRows

/-- Actual pair sampling, with no entry-error or arithmetic-row provider left
as a premise. The displayed exponential density estimate remains explicit. -/
theorem exists_actual_pair_covariance_of_exponential_density :
    ∃ C_A : ℝ, 0 < C_A ∧ ∀ (T L C_D : ℝ) (X : ℕ) (a : ℕ → ℂ),
      9 ≤ T → 0 ≤ C_D → 0 < L → Real.log (X : ℝ) ≤ L / 8 →
      (∀ v ∈ Icc (0 : ℝ) (1 / 2),
        strictTail T v ≤ 2 * C_D * T * L * Real.exp (-(L / 4) * v)) →
      ‖((actualPairSampledEnergy T (Finset.Icc 1 X) a / T ^ 2 -
          ((Zeta23.Ncount 0 T : ℝ) / T) ^ 2 *
            coefficientEnergy (Finset.Icc 1 X) a : ℝ) : ℂ) -
        form (Finset.Icc 1 X) (fun n m => (‖signedArithmetic n m‖ ^ 2 : ℂ)) a‖ ≤
        actualPairErrorCoefficient X (128 * C_D / 3) L
          ((C_A / T) * rationalLandauRpowEnvelope T (X : ℝ))
          (Real.log (X : ℝ) ^ 2 * arithmeticRowConstant X)
          (arithmeticRowConstant X) * coefficientEnergy (Finset.Icc 1 X) a := by
  obtain ⟨C_A, hC_A, hpair⟩ :=
    exists_actual_pair_sampled_covariance_of_exponential_density_and_rows
  refine ⟨C_A, hC_A, ?_⟩
  intro T L C_D X a hT hC_D hL hX hdensity
  exact hpair T L C_D X a reciprocalSqrtWeight
    (Real.log (X : ℝ) ^ 2 * arithmeticRowConstant X) (arithmeticRowConstant X)
    hT hC_D hL hX hdensity
    (fun n hn => reciprocalSqrtWeight_pos (Finset.mem_Icc.mp hn).1)
    (signedArithmetic_weighted_rows X).2 (signedArithmetic_weighted_rows X).1

end RiemannResearch.Analysis.ActualDirichletPolynomialGram
