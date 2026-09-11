/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ThresholdLegalIntegrability

/-!
# The affine structure of normalized legal witnesses

Source: Christian Noack, September 11, 2026, conversation on the vector and
affine structures of finite two-seed Pareto witnesses.

The complete Pareto mean is a real linear map on the actual finite legal span.
Its mean-one fiber is preserved by every real affine combination. No sign
restriction is imposed on the affine parameter.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Addition is compatible with the complete Pareto mean on the legal span. -/
theorem paretoMean_add_of_legal (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    {f g : ℕ → ℝ} (hf : f ∈ legalSeedSpan A) (hg : g ∈ legalSeedSpan A) :
    paretoMean (f + g) = paretoMean f + paretoMean g := by
  unfold paretoMean
  simp only [Pi.add_apply, mul_add]
  exact (legalSeedSpan_weighted_summable A hA hf).tsum_add
    (legalSeedSpan_weighted_summable A hA hg)

/-- Scalar multiplication is compatible with the complete Pareto mean. -/
theorem paretoMean_smul_of_legal (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    {f : ℕ → ℝ} (hf : f ∈ legalSeedSpan A) (c : ℝ) :
    paretoMean (c • f) = c * paretoMean f := by
  unfold paretoMean
  calc
    _ = ∑' k, c * (positiveWeight k * f k) := by
      apply tsum_congr
      intro k
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    _ = _ := (legalSeedSpan_weighted_summable A hA hf).tsum_mul_left c

/-- The actual Pareto mean, restricted to the legal vector space, is linear. -/
def legalSeedMeanLinear (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) :
    legalSeedSpan A →ₗ[ℝ] ℝ where
  toFun f := paretoMean f
  map_add' f g := paretoMean_add_of_legal A hA f.property g.property
  map_smul' c f := by
    change paretoMean (c • (f : ℕ → ℝ)) = c * paretoMean (f : ℕ → ℝ)
    exact paretoMean_smul_of_legal A hA f.property c

/-- Mean-one legal witnesses are closed under all real affine combinations. -/
theorem legalSeedSpan_mean_one_affine (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    {f g : ℕ → ℝ} (hf : f ∈ legalSeedSpan A) (hg : g ∈ legalSeedSpan A)
    (hmf : paretoMean f = 1) (hmg : paretoMean g = 1) (t : ℝ) :
    (1 - t) • f + t • g ∈ legalSeedSpan A ∧
      paretoMean ((1 - t) • f + t • g) = 1 := by
  have hcf := (legalSeedSpan A).smul_mem (1 - t) hf
  have htg := (legalSeedSpan A).smul_mem t hg
  refine ⟨(legalSeedSpan A).add_mem hcf htg, ?_⟩
  rw [paretoMean_add_of_legal A hA hcf htg,
    paretoMean_smul_of_legal A hA hf, paretoMean_smul_of_legal A hA hg, hmf, hmg]
  ring

end
end RiemannResearch.RH.Pareto
