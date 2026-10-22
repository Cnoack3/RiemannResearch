import RiemannResearch.Analysis.LaguerreCompleteness
import RiemannResearch.RH.ParetoExponentialRealization
import RiemannResearch.RH.ParetoApproximationRatio

/-!
# Parseval for the actual arithmetic Laguerre coefficients

Source: the user's ActualParsevalTarget in RamanujanLaguerreResearchTargets.
The coefficient integrals, full Pareto error, and summability are unchanged.
The proof uses the complete ordinary Laguerre basis for exponential measure.
No RH, uniform-energy, or completeness hypothesis is assumed.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.RamanujanLaguerre
open RiemannResearch.Analysis

theorem memLp_exponentialLift_of_bounded {F : ℕ → ℝ} {C : ℝ}
    (hF : ∀ k, |F k| ≤ C) :
    MemLp (exponentialLift F) 2 laguerreMeasure := by
  apply (memLp_two_iff_integrable_sq (exponentialLift_measurable F).aestronglyMeasurable).2
  rw [integrable_laguerreMeasure_iff]
  have hsqb : ∀ k, |F k ^ 2| ≤ C * C := by
    simpa only [pow_two] using bounded_product hF hF
  simpa [exponentialLift] using allMomentsIntegrable_of_bounded hsqb 0

theorem coefficient_eq_inner_exponentialLift {F : ℕ → ℝ}
    (hF : MemLp (exponentialLift F) 2 laguerreMeasure) (k : ℕ) :
    coefficient F k = inner ℝ (hF.toLp (exponentialLift F)) (laguerreVector k) := by
  rw [laguerreVector, inner_toLp_laguerreMeasure]
  rfl

/-- The full coefficient series is summable and includes the exact constant mode. -/
theorem hasSum_coefficient_sq_of_bounded {F : ℕ → ℝ} {C : ℝ}
    (hF : ∀ k, |F k| ≤ C) :
    HasSum (fun k => coefficient F k ^ 2) (paretoInner F F) := by
  let hL := memLp_exponentialLift_of_bounded hF
  have h := hasSum_laguerre_inner_sq (hL.toLp (exponentialLift F))
  simp_rw [← coefficient_eq_inner_exponentialLift hL] at h
  rw [norm_toLp_sq_laguerreMeasure] at h
  have hsqb : ∀ k, |F k ^ 2| ≤ C * C := by
    simpa only [pow_two] using bounded_product hF hF
  rw [exponentialLift_square_identity F (weighted_summable_of_bounded hsqb)] at h
  simpa only [paretoInner, pow_two] using h

theorem coefficient_zero_of_bounded {F : ℕ → ℝ} {C : ℝ}
    (hF : ∀ k, |F k| ≤ C) : coefficient F 0 = paretoMean F := by
  rw [coefficient_eq_momentTransform F (allMomentsIntegrable_of_bounded hF),
    laguerreMomentTransform_zero]
  exact ordinaryMoment_zero_of_bounded hF

/-- Actual Parseval with no conditional analytic provider. -/
theorem actualParsevalTarget : ActualParsevalTarget := by
  intro F hF hmean
  obtain ⟨C, hC⟩ := legalSeedSpan_bounded ({2, 3} : Set ℕ)
    (by intro a ha; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with rfl | rfl <;> norm_num) hF
  have hs := hasSum_coefficient_sq_of_bounded hC
  have htail : Summable (fun k : ℕ => coefficient F (k + 1) ^ 2) :=
    (summable_nat_add_iff 1).2 hs.summable
  refine ⟨htail, ?_⟩
  have hsplit := hs.summable.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, coefficient_zero_of_bounded hC, hmean, one_pow] at hsplit
  rw [hs.tsum_eq] at hsplit
  have herr := paretoError_eq_variance_add_bias_sq hC
  rw [paretoVariance_eq hC, hmean] at herr
  linarith

end RiemannResearch.RH.Pareto.RamanujanLaguerre
