import RiemannResearch.Analysis.WeightedMellinLogarithmicKernel
import RiemannResearch.Analysis.WeightedMellinTopologyTargets

/-!
# Full-zero jet bounds from the actual weighted Mellin topology

Prepared as a mathematical source continuation for coordinator checking.
Current checking evidence and remaining obligations are recorded in
`RiemannResearch/ANNULAR_FORMALIZATION_20261010.md`.
This historical preparation note is not a current verification claim.

The logarithmic-kernel and derivative-topology companion proofs supply
the two derivative interfaces. Their estimates are uniform
in every nonnegative integer derivative order and every full strip zero.
They require actual weighted energy membership of the vector. They do
not assert such membership for an untruncated arithmetic signal.
-/

set_option autoImplicit false
noncomputable section

namespace RiemannResearch.Analysis.WeightedMellinTopology
open MeasureTheory.WeightedMellin
open RiemannResearch.RH.AnnularZeroSpectral

/-- Both named derivative obligations are now supplied by analytic proofs. -/
theorem higherDerivativeIntegralProvider (a : ℝ) : HigherDerivativeIntegralProvider a := by
  intro f hf k z hz
  exact iteratedDeriv_transform_eq_logarithmicTransform hf k
    (by linarith : (2 * a) / 2 < z.re)

theorem derivativeEvaluationBoundProvider (a : ℝ) : DerivativeEvaluationBoundProvider a := by
  intro f hf k z hz
  have h := iteratedDeriv_transform_norm_sq_le hf k
    (by linarith : (2 * a) / 2 < z.re)
  simpa only [normSquared,
    show 2 * z.re - 2 * a = 2 * (z.re - a) by ring] using h

/-- All full-zero jets are bounded, uniformly in the zero ordinate and
real part, in the negative-weight topology H_a. The zero set is complete
as encoded by FullZeroData; no RH line restriction is substituted. -/
theorem fullZero_iteratedDeriv_uniform_of_negative_weight
    {ι : Type*} (D : FullZeroData ι) {f : ℝ → ℂ} {a : ℝ}
    (hf : Ha a f) (ha : a < 0) (k : ℕ) :
    ∀ i : ι, ‖iteratedDeriv k (transform f) (D.rho i)‖ ^ 2 ≤
      normSquared a f * ((2 * k).factorial : ℝ) / (-2 * a) ^ (2 * k + 1) := by
  intro i
  have h := iteratedDeriv_transform_norm_sq_le_of_margin hf k
    (by linarith : (2 * a) / 2 < (0 : ℝ)) (D.strip_left i).le
  simpa only [normSquared, show 2 * (0 : ℝ) - 2 * a = -2 * a by ring] using h

/-- Quantitative continuity of every jet, for the actual weighted
difference seminorm. All signed differences are retained exactly. -/
theorem fullZero_iteratedDeriv_difference_uniform_of_negative_weight
    {ι : Type*} (D : FullZeroData ι) {f g : ℝ → ℂ} {a : ℝ}
    (hf : Ha a f) (hg : Ha a g) (ha : a < 0) (k : ℕ) (i : ι) :
    ‖iteratedDeriv k (transform f) (D.rho i) -
      iteratedDeriv k (transform g) (D.rho i)‖ ^ 2 ≤
        normSquared a (fun x => f x - g x) * ((2 * k).factorial : ℝ) /
          (-2 * a) ^ (2 * k + 1) := by
  have hz : (2 * a) / 2 < (D.rho i).re := by
    have hzero := D.strip_left i
    linarith
  have hsub := finiteEnergy_sub hf hg
  rw [iteratedDeriv_transform_eq_logarithmicTransform hf k hz,
    iteratedDeriv_transform_eq_logarithmicTransform hg k hz,
    ← logarithmicTransform_sub hf hg k hz,
    ← iteratedDeriv_transform_eq_logarithmicTransform hsub k hz]
  exact fullZero_iteratedDeriv_uniform_of_negative_weight D hsub ha k i

end RiemannResearch.Analysis.WeightedMellinTopology
