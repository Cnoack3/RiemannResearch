import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# A projection formula for an isometric multiplier

This is the abstract Hilbert-space argument used in J.-F. Burnol,
*A note on Nyman's equivalent formulation of the Riemann Hypothesis*,
Lemma 2.4, <https://arxiv.org/pdf/math/9910055>.

The analytic application takes `U` to be multiplication by an inner
function and `e` to be a reproducing kernel. The hypothesis `hreproduce`
records the required adjoint eigenvector identity explicitly. This module
does not construct Hardy space, its reproducing kernel, or Burnol's
Blaschke product, and does not assert those analytic hypotheses.
-/

noncomputable section

namespace RiemannResearch.Analysis.InnerMultiplierProjection

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]

/-- If the adjoint of an isometry sends `e` to `c • e`, the projection of
`e` onto its range is `U (c • e)`. The hypothesis is stated through inner
products so that an adjoint operator need not be constructed separately. -/
theorem projection_eq_of_reproducing (U : E →ₗᵢ[𝕜] E)
    [U.toLinearMap.range.HasOrthogonalProjection] (e : E) (c : 𝕜)
    (hreproduce : ∀ y : E, inner 𝕜 e (U y) = inner 𝕜 (c • e) y) :
    U.toLinearMap.range.starProjection e = U (c • e) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨c • e, rfl⟩
  · rintro w ⟨y, rfl⟩
    change inner 𝕜 (e - U (c • e)) (U y) = 0
    rw [inner_sub_left, U.inner_map_map, hreproduce, sub_self]

/-- The range-projection energy is the squared scalar modulus times the
kernel energy. -/
theorem norm_sq_projection_eq (U : E →ₗᵢ[𝕜] E)
    [U.toLinearMap.range.HasOrthogonalProjection] (e : E) (c : 𝕜)
    (hreproduce : ∀ y : E, inner 𝕜 e (U y) = inner 𝕜 (c • e) y) :
    ‖U.toLinearMap.range.starProjection e‖ ^ 2 = ‖c‖ ^ 2 * ‖e‖ ^ 2 := by
  rw [projection_eq_of_reproducing U e c hreproduce, U.norm_map, norm_smul,
    mul_pow]

/-- The unit-kernel form of the abstract Burnol projection computation. -/
theorem norm_sq_projection_eq_of_unit (U : E →ₗᵢ[𝕜] E)
    [U.toLinearMap.range.HasOrthogonalProjection] (e : E) (he : ‖e‖ = 1)
    (c : 𝕜)
    (hreproduce : ∀ y : E, inner 𝕜 e (U y) = inner 𝕜 (c • e) y) :
    ‖U.toLinearMap.range.starProjection e‖ ^ 2 = ‖c‖ ^ 2 := by
  rw [norm_sq_projection_eq U e c hreproduce, he, one_pow, mul_one]

end RiemannResearch.Analysis.InnerMultiplierProjection
