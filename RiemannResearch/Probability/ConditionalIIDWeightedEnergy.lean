/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Probability.ConditionalIIDMarginal
import RiemannResearch.Probability.ConditionalIIDSampleMean

/-! Actual conditional variances and the weighted arithmetic energy identities. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.Probability.ConditionalIID
open RH.ArithmeticCumulative

/-- The finite-fiber variance is the actual conditional variance random variable. -/
theorem conditional_variance_ae (i : ℕ) (F : ℕ → ℝ)
    (hF : MemLp (fun ω => F (coordinate i ω)) 2 probability) :
    condVar latentSigma (fun ω => F (coordinate i ω)) probability =ᵐ[probability]
      (fun ω => variance F (uniformLaw (latentIndex ω))) := by
  have h := condVar_ae_eq_condExp_sq_sub_sq_condExp latentSigma_le hF
  have h1 := conditional_coordinate_expectation i F (hF.integrable one_le_two)
  have h2 := conditional_coordinate_expectation i (fun n => F n ^ 2) hF.integrable_sq
  filter_upwards [h, h1, h2] with ω hω h1ω h2ω
  rw [hω]
  simp only [Pi.sub_apply, Pi.pow_apply]
  change probability[(fun ω : Omega => F (coordinate i ω) ^ 2) | latentSigma] ω -
    probability[(fun ω : Omega => F (coordinate i ω)) | latentSigma] ω ^ 2 = _
  rw [h1ω, h2ω, uniform_variance_formula]
  rfl

/-- Sample averaging needs only a single marginal L2 assumption. -/
theorem average_error_condVar (F : ℕ → ℝ) (r : ℕ) (hr : 0 < r) (c : ℝ)
    (hF : MemLp (fun ω => F (coordinate 0 ω)) 2 probability) :
    (∫ ω : Omega, (c - pathAverage F r ω.2) ^ 2 ∂probability) =
      (∫ ω, (c - cesaro F (endpoint ω)) ^ 2 ∂probability) +
      (∫ ω, condVar latentSigma (fun ω => F (coordinate 0 ω)) probability ω ∂probability) /
        (r : ℝ) := by
  rw [average_error F r hr c (coordinate_memLp_of_zero F hF)]
  congr 1
  congr 1
  exact integral_congr_ae (conditional_variance_ae 0 F hF).symm

/-- Each atom of the pushforward law has exactly its Pareto mass, including zero mass at 0. -/
theorem coordinate_real_singleton (i n : ℕ) :
    (Measure.map (coordinate i) probability).real {n} = weight n := by
  unfold Measure.real
  rw [Measure.map_apply (coordinate_measurable i) (measurableSet_singleton n)]
  cases n with
  | zero => simp [coordinate_zero_mass, weight]
  | succ m =>
    rw [coordinate_positive_mass, ENNReal.toReal_ofReal (weight_nonneg _)]

/-- Countable integration is linked to the actual marginal, with integrability required. -/
theorem coordinate_integral (i : ℕ) (F : ℕ → ℝ)
    (hF : Integrable (fun ω => F (coordinate i ω)) probability) :
    (∫ ω, F (coordinate i ω) ∂probability) = ∑' n : ℕ, weight n * F n := by
  have hm : StronglyMeasurable F := (measurable_of_countable F).stronglyMeasurable
  have hi : Integrable F (Measure.map (coordinate i) probability) :=
    (integrable_map_measure hm.aestronglyMeasurable
      (coordinate_measurable i).aemeasurable).2 hF
  rw [← integral_map_of_stronglyMeasurable (coordinate_measurable i) hm,
    integral_countable hi]
  apply tsum_congr
  intro n
  rw [coordinate_real_singleton]
  rfl

/-- Latent-coordinate integration, with the zero-index shift explicit. -/
theorem latent_integral (F : ℕ → ℝ)
    (hF : Integrable (fun ω => F (latentIndex ω)) probability) :
    (∫ ω, F (latentIndex ω) ∂probability) =
      ∑' k : ℕ, mixtureWeight (k + 1) * F k := by
  have hm : StronglyMeasurable F := (measurable_of_countable F).stronglyMeasurable
  have hi : Integrable F (Measure.map latentIndex probability) :=
    (integrable_map_measure hm.aestronglyMeasurable latentIndex_measurable.aemeasurable).2 hF
  rw [map_latentIndex] at hi
  rw [← integral_map_of_stronglyMeasurable latentIndex_measurable hm,
    map_latentIndex, integral_countable hi]
  apply tsum_congr
  intro k
  simp only [Measure.real, latentLaw_singleton,
    ENNReal.toReal_ofReal (mixtureWeight_nonneg _), smul_eq_mul]

/-- The exact requested conditional-iid mean-square formula, now in weighted arithmetic notation. -/
theorem average_error_weighted (F : ℕ → ℝ) (r : ℕ) (hr : 0 < r) (c : ℝ)
    (hF : MemLp (fun ω => F (coordinate 0 ω)) 2 probability) :
    (∫ ω : Omega, (c - pathAverage F r ω.2) ^ 2 ∂probability) =
      (∑' k : ℕ, mixtureWeight (k + 1) * (c - cesaro F (k + 1)) ^ 2) +
      (∫ ω, condVar latentSigma (fun ω => F (coordinate 0 ω)) probability ω ∂probability) /
        (r : ℝ) := by
  rw [average_error_condVar F r hr c hF]
  congr 1
  exact latent_integral (fun k => (c - cesaro F (k + 1)) ^ 2)
    (conditionalMean_error_integrable F c hF)

/-- Cesaro averaging is a contraction in the exact weighted square energies. -/
theorem weighted_cesaro_energy_le (F : ℕ → ℝ)
    (hF : MemLp (fun ω => F (coordinate 0 ω)) 2 probability) :
    (∑' k : ℕ, mixtureWeight (k + 1) * cesaro F (k + 1) ^ 2) ≤
      ∑' n : ℕ, weight n * F n ^ 2 := by
  have h := conditionalMean_error_le_average_error F 1 (by omega) 0
    (coordinate_memLp_of_zero F hF)
  simp only [pathAverage_apply, Finset.sum_range_one, Nat.cast_one, inv_one,
    one_mul, zero_sub, neg_sq] at h
  rw [coordinate_integral 0 (fun n => F n ^ 2) hF.integrable_sq] at h
  have he := latent_integral (fun k => cesaro F (k + 1) ^ 2)
    (conditionalMean_sq_integrable F hF)
  exact he.symm ▸ h

end RiemannResearch.Probability.ConditionalIID
