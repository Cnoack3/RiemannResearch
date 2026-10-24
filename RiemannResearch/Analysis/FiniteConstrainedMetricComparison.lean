import RiemannResearch.Analysis.FiniteGramMultipleConstraint
import Mathlib.Tactic.Linarith

/-!
# Exact comparison of constrained optimizers in two metrics

Source: user-requested fifth Ramanujan dual continuation, 24 October 2026.
The same coefficient observations are imposed in two independent finite
dictionaries. A signed metric correction yields two exact identities and a
balance law containing both optimizer displacement squares. No diagonal
approximation or positivity of the correction is used in these identities.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteConstrainedMetricComparison
open FiniteGramMultipleConstraint

variable {ι κ E F : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {u : ι → E} {v : ι → F}
  (hu : LinearIndependent ℝ u) (hv : LinearIndependent ℝ v)
  (B : κ → ι → ℝ)
  (hBu : LinearIndependent ℝ (sourceRows hu B))
  (hBv : LinearIndependent ℝ (sourceRows hv B))
  (f : E) (g : F) (t : κ → ℝ)
  (scale : ℝ) (D : (ι → ℝ) → ℝ)
  (hmetric : ∀ a : ι → ℝ,
    scale * ‖g - Fintype.linearCombination ℝ v a‖ ^ 2 =
      ‖f - Fintype.linearCombination ℝ u a‖ ^ 2 + D a)

include hmetric

local notation "p" => coefficients hu B hBu f t
local notation "q" => coefficients hv B hBv g t

/-- The exact lower comparison, including the displaced first-metric fit. -/
theorem lower_identity :
    scale * ‖g - Fintype.linearCombination ℝ v q‖ ^ 2 =
      ‖f - Fintype.linearCombination ℝ u p‖ ^ 2 +
        ‖Fintype.linearCombination ℝ u (q - p)‖ ^ 2 + D q := by
  rw [hmetric]
  rw [coefficients_completion hu B hBu f t q
    (coefficients_source hv B hBv g t)]

/-- The exact upper comparison includes the displaced second-metric fit. -/
theorem upper_identity :
    ‖f - Fintype.linearCombination ℝ u p‖ ^ 2 + D p =
      scale * ‖g - Fintype.linearCombination ℝ v q‖ ^ 2 +
        scale * ‖Fintype.linearCombination ℝ v (p - q)‖ ^ 2 := by
  rw [← hmetric]
  rw [coefficients_completion hv B hBv g t p
    (coefficients_source hu B hBu f t), mul_add]

/-- The entire change in metric correction pays for both displacements. -/
theorem correction_balance :
    D p = D q + ‖Fintype.linearCombination ℝ u (q - p)‖ ^ 2 +
      scale * ‖Fintype.linearCombination ℝ v (p - q)‖ ^ 2 := by
  have hl := lower_identity hu hv B hBu hBv f g t scale D hmetric
  have hh := upper_identity hu hv B hBu hBv f g t scale D hmetric
  linarith

theorem correction_le (hscale : 0 ≤ scale) : D q ≤ D p := by
  have hb := correction_balance hu hv B hBu hBv f g t scale D hmetric
  have hn := mul_nonneg hscale (sq_nonneg
    ‖Fintype.linearCombination ℝ v (p - q)‖)
  linarith [sq_nonneg ‖Fintype.linearCombination ℝ u (q - p)‖]

/-- Equality of corrections is exactly agreement of all optimizer coefficients. -/
theorem correction_equal_iff (hscale : 0 ≤ scale) : D p = D q ↔ p = q := by
  constructor
  · intro he
    have hb := correction_balance hu hv B hBu hBv f g t scale D hmetric
    have hn := mul_nonneg hscale (sq_nonneg
      ‖Fintype.linearCombination ℝ v (p - q)‖)
    have hz : ‖Fintype.linearCombination ℝ u (q - p)‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖Fintype.linearCombination ℝ u (q - p)‖]
    have hz' := norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
    have hc : q - p = 0 := by
      apply hu.fintypeLinearCombination_injective
      simpa only [map_zero] using hz'
    exact (sub_eq_zero.mp hc).symm
  · intro he
    rw [he]

theorem minimum_bounds (hscale : 0 ≤ scale) (hD : 0 ≤ D q) :
    ‖f - Fintype.linearCombination ℝ u p‖ ^ 2 ≤
      scale * ‖g - Fintype.linearCombination ℝ v q‖ ^ 2 ∧
    scale * ‖g - Fintype.linearCombination ℝ v q‖ ^ 2 ≤
      ‖f - Fintype.linearCombination ℝ u p‖ ^ 2 + D p := by
  constructor
  · rw [lower_identity hu hv B hBu hBv f g t scale D hmetric]
    linarith [sq_nonneg ‖Fintype.linearCombination ℝ u (q - p)‖]
  · have hh := upper_identity hu hv B hBu hBv f g t scale D hmetric
    have hn := mul_nonneg hscale (sq_nonneg
      ‖Fintype.linearCombination ℝ v (p - q)‖)
    linarith

end RiemannResearch.Analysis.FiniteConstrainedMetricComparison
