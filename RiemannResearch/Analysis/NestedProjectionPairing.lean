import RiemannResearch.Analysis.NestedProjectionEnergy
import Mathlib.Tactic.Ring

/-!
# Signed pairings for nested orthogonal projections

Source: independently assembled from orthogonal projection identities and
Cauchy--Schwarz in Mathlib, in response to the user's inverse-Gram correction
question, 28 September 2026. No novelty claim is made for these Hilbert-space
inequalities. The concrete RH consumer is RH.ResidueCorrectionCovariance.

For a residual pairing, discard the projected part of the test vector.
For a nested projection difference, discard both parts outside the gap.
This retains the test-vector energy missing from a norm-only bound.
-/

noncomputable section
namespace RiemannResearch.Analysis.NestedProjectionPairing
open RiemannResearch.Analysis.NestedProjectionEnergy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Squared real Cauchy--Schwarz. -/
theorem real_pairing_sq_le (x y : E) :
    (inner ℝ x y)^2 ≤ ‖x‖^2 * ‖y‖^2 := by
  have h := norm_inner_le_norm (𝕜 := ℝ) x y
  rw [Real.norm_eq_abs] at h
  have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg x) (norm_nonneg y))).mpr h
  simpa only [sq_abs, mul_pow] using hs

/-- Orthogonality removes the captured part of the test vector. -/
theorem residual_pairing_eq (U : Submodule ℝ E) [U.HasOrthogonalProjection] (x y : E) :
    inner ℝ (x - U.starProjection x) y =
      inner ℝ (x - U.starProjection x) (y - U.starProjection y) := by
  rw [inner_sub_right, Submodule.starProjection_inner_eq_zero x _
    (U.starProjection_apply_mem y), sub_zero]

/-- Bound a residual pairing using the remaining, rather than full, dual energy. -/
theorem residual_pairing_sq_le (U : Submodule ℝ E) [U.HasOrthogonalProjection] (x y : E) :
    (inner ℝ (x - U.starProjection x) y)^2 ≤
      ‖x - U.starProjection x‖^2 * (‖y‖^2 - ‖U.starProjection y‖^2) := by
  rw [residual_pairing_eq U x y]
  have he := norm_sq_eq_projection_add_residual U y
  have hb := real_pairing_sq_le (x - U.starProjection x) (y - U.starProjection y)
  have hy : ‖y‖^2 - ‖U.starProjection y‖^2 = ‖y - U.starProjection y‖^2 := by linarith
  rw [hy]
  exact hb

/-- A nested projection difference only sees the same difference in the test vector. -/
theorem nested_pairing_eq {U V : Submodule ℝ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hUV : U ≤ V) (x y : E) :
    inner ℝ (V.starProjection x - U.starProjection x) y =
      inner ℝ (V.starProjection x - U.starProjection x)
        (V.starProjection y - U.starProjection y) := by
  have hm : V.starProjection x - U.starProjection x ∈ V :=
    V.sub_mem (V.starProjection_apply_mem x) (hUV (U.starProjection_apply_mem x))
  have hoV : inner ℝ (V.starProjection x - U.starProjection x)
      (y - V.starProjection y) = 0 :=
    (V.mem_orthogonal _).mp (Submodule.sub_starProjection_mem_orthogonal y) _ hm
  have hoU : inner ℝ (V.starProjection x - U.starProjection x)
      (U.starProjection y) = 0 := by
    rw [inner_sub_left, V.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr (hUV (U.starProjection_apply_mem y))]
    have h := Submodule.starProjection_inner_eq_zero x _
      (U.starProjection_apply_mem y)
    simpa only [inner_sub_left] using h
  rw [inner_sub_right] at hoV
  rw [inner_sub_right, hoU, sub_zero]
  linarith

/-- The product of the two projection-gap energies controls the signed pairing. -/
theorem nested_pairing_sq_le {U V : Submodule ℝ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hUV : U ≤ V) (x y : E) :
    (inner ℝ (V.starProjection x - U.starProjection x) y)^2 ≤
      ‖V.starProjection x - U.starProjection x‖^2 *
        ‖V.starProjection y - U.starProjection y‖^2 := by
  rw [nested_pairing_eq hUV x y]
  exact real_pairing_sq_le _ _
end RiemannResearch.Analysis.NestedProjectionPairing
