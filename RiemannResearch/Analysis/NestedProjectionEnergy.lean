import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic.Linarith

/-!
# Exact comparison of nested orthogonal projections

For `U ≤ V`, the difference between the two captured squared norms is
exactly `‖P_V x - P_U x‖²`. The same term measures the difference between
the two residual squared norms. In particular, inclusion alone does not
identify the two projection norms.

Application source: J.-F. Burnol, *A note on Nyman's equivalent formulation
of the Riemann Hypothesis*, Theorem 1.2 and Lemma 2.4,
<https://arxiv.org/pdf/math/9910055>. The statements below are general
Hilbert-space consequences of Pythagoras, not a proof of Burnol's analytic
identification of the Nyman space or its zero product.
-/

noncomputable section

namespace RiemannResearch.Analysis.NestedProjectionEnergy

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]
variable {U V : Submodule 𝕜 E}
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- Projection onto a smaller space absorbs projection onto a larger one. -/
theorem project_project_of_le (hUV : U ≤ V) (x : E) :
    U.starProjection (V.starProjection x) = U.starProjection x := by
  have h := congrArg (fun f : E →L[𝕜] E => f x)
    (Submodule.starProjection_comp_starProjection_of_le hUV)
  exact h

/-- The usual Pythagorean identity, written using the actual residual. -/
theorem norm_sq_eq_projection_add_residual (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (x : E) :
    ‖x‖ ^ 2 = ‖U.starProjection x‖ ^ 2 + ‖x - U.starProjection x‖ ^ 2 := by
  simpa only [Submodule.starProjection_orthogonal_val] using
    Submodule.norm_sq_eq_add_norm_sq_starProjection x U

/-- The precise captured-energy gain when the projection space increases. -/
theorem captured_energy_eq_add_gap (hUV : U ≤ V) (x : E) :
    ‖V.starProjection x‖ ^ 2 = ‖U.starProjection x‖ ^ 2 +
      ‖V.starProjection x - U.starProjection x‖ ^ 2 := by
  simpa only [project_project_of_le hUV x] using
    norm_sq_eq_projection_add_residual U (V.starProjection x)

/-- The smaller-space error is the larger-space error plus the exact gap. -/
theorem residual_energy_eq_add_gap (hUV : U ≤ V) (x : E) :
    ‖x - U.starProjection x‖ ^ 2 = ‖x - V.starProjection x‖ ^ 2 +
      ‖V.starProjection x - U.starProjection x‖ ^ 2 := by
  have hU := norm_sq_eq_projection_add_residual U x
  have hV := norm_sq_eq_projection_add_residual V x
  have hgap := captured_energy_eq_add_gap hUV x
  linarith

theorem captured_energy_mono (hUV : U ≤ V) (x : E) :
    ‖U.starProjection x‖ ^ 2 ≤ ‖V.starProjection x‖ ^ 2 := by
  have h := captured_energy_eq_add_gap hUV x
  nlinarith [sq_nonneg ‖V.starProjection x - U.starProjection x‖]

theorem residual_energy_antimono (hUV : U ≤ V) (x : E) :
    ‖x - V.starProjection x‖ ^ 2 ≤ ‖x - U.starProjection x‖ ^ 2 := by
  have h := residual_energy_eq_add_gap hUV x
  nlinarith [sq_nonneg ‖V.starProjection x - U.starProjection x‖]

/-- Captured energies agree precisely when the two projected vectors agree. -/
theorem captured_energy_eq_iff (hUV : U ≤ V) (x : E) :
    ‖V.starProjection x‖ ^ 2 = ‖U.starProjection x‖ ^ 2 ↔
      V.starProjection x = U.starProjection x := by
  constructor
  · intro h
    have hg := captured_energy_eq_add_gap hUV x
    have hz : ‖V.starProjection x - U.starProjection x‖ = 0 := by nlinarith
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  · intro h
    rw [h]

/-- Equal residual energies also force equality of the projected vectors. -/
theorem residual_energy_eq_iff (hUV : U ≤ V) (x : E) :
    ‖x - U.starProjection x‖ ^ 2 = ‖x - V.starProjection x‖ ^ 2 ↔
      V.starProjection x = U.starProjection x := by
  constructor
  · intro h
    have hg := residual_energy_eq_add_gap hUV x
    have hz : ‖V.starProjection x - U.starProjection x‖ = 0 := by nlinarith
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  · intro h
    rw [h]

/-- An externally supplied captured-energy formula transfers with its exact
nonnegative remainder, without assuming equality of the two spaces. -/
theorem residual_energy_eq_sub_add_gap (hUV : U ≤ V) (x : E) (p : ℝ)
    (hp : ‖V.starProjection x‖ ^ 2 = p) :
    ‖x - U.starProjection x‖ ^ 2 = ‖x‖ ^ 2 - p +
      ‖V.starProjection x - U.starProjection x‖ ^ 2 := by
  have hV := norm_sq_eq_projection_add_residual V x
  have hgap := residual_energy_eq_add_gap hUV x
  linarith

/-- For a unit target, the zero-product distance expression is supplemented
by the exact loss incurred by projecting onto the smaller space. -/
theorem unit_residual_energy_eq_sub_add_gap (hUV : U ≤ V) (x : E)
    (hx : ‖x‖ = 1) (p : ℝ) (hp : ‖V.starProjection x‖ ^ 2 = p) :
    ‖x - U.starProjection x‖ ^ 2 = 1 - p +
      ‖V.starProjection x - U.starProjection x‖ ^ 2 := by
  simpa only [hx, one_pow] using residual_energy_eq_sub_add_gap hUV x p hp

end RiemannResearch.Analysis.NestedProjectionEnergy
