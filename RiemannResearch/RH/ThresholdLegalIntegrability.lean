import RiemannResearch.RH.ThresholdDilationAlgebra
import RiemannResearch.RH.ParetoDilation
import RiemannResearch.RH.ParetoResidueDuality

/-!
# Integrability of every finite legal seed synthesis

Source: Christian Noack, `RH_Two_Seed_Threshold.tex`, September 8, 2026,
Sections 2 and 10. These lemmas establish boundedness and absolute summability
for every element of the actual algebraic dilation span. They discharge the
integrability prerequisites of the existing Pareto mean and inner-product
identities, without assuming a finite expression as extra data.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Every finite legal synthesis of positive residue seeds is bounded. -/
theorem legalSeedSpan_bounded (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    {f : ℕ → ℝ} (hf : f ∈ legalSeedSpan A) :
    ∃ C : ℝ, ∀ k, |f k| ≤ C := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, ha, m, hm, rfl⟩ := hf
    exact ⟨(m : ℝ) * a, dilation_abs_le (fun k => residue_abs_le a k (hA a ha)) m⟩
  | zero => exact ⟨0, by simp⟩
  | add f g hf hg ihf ihg =>
    obtain ⟨C, hC⟩ := ihf
    obtain ⟨D, hD⟩ := ihg
    refine ⟨C + D, fun k => ?_⟩
    exact le_trans (abs_add_le _ _) (add_le_add (hC k) (hD k))
  | smul c f hf ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨|c| * C, fun k => ?_⟩
    simpa only [Pi.smul_apply, smul_eq_mul, abs_mul] using
      mul_le_mul_of_nonneg_left (hC k) (abs_nonneg c)

/-- Legal vectors have absolutely summable Pareto means. -/
theorem legalSeedSpan_weighted_summable (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    {f : ℕ → ℝ} (hf : f ∈ legalSeedSpan A) :
    Summable (fun k => positiveWeight k * f k) := by
  obtain ⟨C, hC⟩ := legalSeedSpan_bounded A hA hf
  exact weighted_summable_of_bounded hC

/-- Every mixed Gram term between legal vectors is absolutely summable. -/
theorem legalSeedSpan_mixed_summable (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    {f g : ℕ → ℝ} (hf : f ∈ legalSeedSpan A) (hg : g ∈ legalSeedSpan A) :
    Summable (fun k => positiveWeight k * (f k * g k)) := by
  obtain ⟨C, hC⟩ := legalSeedSpan_bounded A hA hf
  obtain ⟨D, hD⟩ := legalSeedSpan_bounded A hA hg
  exact weighted_summable_of_bounded (bounded_product hC hD)

/-- The full target approximation error, including the infinite tail, exists. -/
theorem legalSeedSpan_error_summable (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    {f : ℕ → ℝ} (hf : f ∈ legalSeedSpan A) :
    Summable (fun k => positiveWeight k * (1 - f k) ^ 2) := by
  obtain ⟨C, hC⟩ := legalSeedSpan_bounded A hA hf
  exact weighted_summable_of_bounded (error_square_bounded hC)

end
end RiemannResearch.RH.Pareto
