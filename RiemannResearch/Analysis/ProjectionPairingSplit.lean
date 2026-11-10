import RiemannResearch.Analysis.ResidualizedProjectionKernel
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-!
# Signed projection pairings and exact inverse-Gram remainders

Source: standard real Hilbert-space orthogonal decomposition, assembled for the
user's residue/zero Gram and matched-displacement question, 9 November 2026.
The concrete consumers are ParetoResidueZeroScreening and QMatchedGramScreening.
Every residual norm-square subtraction and the signed captured pairing are kept.
The split absolute bound is proved no larger than the original Cauchy bound.
No arithmetic uniform estimate or density conclusion is assumed here.
-/

open scoped BigOperators
namespace RiemannResearch.Analysis.ProjectionPairingSplit
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (S : Submodule ℝ E) [S.HasOrthogonalProjection]
theorem pairing_split (x y : E) :
    inner ℝ x y = inner ℝ (S.starProjection x) (S.starProjection y) +
      inner ℝ (x - S.starProjection x) (y - S.starProjection y) := by
  have hp := ResidualizedProjectionKernel.projection_inner S x y
  have hpp := ResidualizedProjectionKernel.projection_inner S (S.starProjection x) y
  rw [Submodule.starProjection_eq_self_iff.mpr (S.starProjection_apply_mem x)] at hpp
  simp only [inner_sub_left, inner_sub_right]
  linarith
theorem residual_pairing_sq_le (x y : E) :
    (inner ℝ x y - inner ℝ (S.starProjection x) (S.starProjection y)) ^ 2 ≤
      (‖x‖ ^ 2 - ‖S.starProjection x‖ ^ 2) *
      (‖y‖ ^ 2 - ‖S.starProjection y‖ ^ 2) := by
  rw [pairing_split S x y, add_sub_cancel_left,
    ← ResidualizedProjectionKernel.residual_norm_sq S x,
    ← ResidualizedProjectionKernel.residual_norm_sq S y]
  have h := abs_real_inner_le_norm (x - S.starProjection x) (y - S.starProjection y)
  have hh := mul_le_mul h h (abs_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  simpa only [← pow_two, sq_abs, mul_pow] using hh
theorem abs_pairing_le (x y : E) :
    |inner ℝ x y| ≤ |inner ℝ (S.starProjection x) (S.starProjection y)| +
      ‖x - S.starProjection x‖ * ‖y - S.starProjection y‖ := by
  rw [pairing_split S x y]
  exact (abs_add_le _ _).trans (add_le_add le_rfl (abs_real_inner_le_norm _ _))
theorem split_bound_le_cauchy (x y : E) :
    |inner ℝ (S.starProjection x) (S.starProjection y)| +
      ‖x - S.starProjection x‖ * ‖y - S.starProjection y‖ ≤ ‖x‖ * ‖y‖ := by
  have hx := ResidualizedProjectionKernel.residual_norm_sq S x
  have hy := ResidualizedProjectionKernel.residual_norm_sq S y
  have hp := abs_real_inner_le_norm (S.starProjection x) (S.starProjection y)
  have hprod : ‖S.starProjection x‖ * ‖S.starProjection y‖ +
      ‖x - S.starProjection x‖ * ‖y - S.starProjection y‖ ≤ ‖x‖ * ‖y‖ := by
    have hsq := sq_nonneg
      (‖S.starProjection x‖ * ‖y - S.starProjection y‖ -
        ‖x - S.starProjection x‖ * ‖S.starProjection y‖)
    have hxprod := congrArg (fun t : ℝ => t * ‖y‖ ^ 2) hx
    have hyprod := congrArg (fun t : ℝ => ‖S.starProjection x‖ ^ 2 * t) hy
    have hxyprod := congrArg (fun t : ℝ => ‖x - S.starProjection x‖ ^ 2 * t) hy
    apply (sq_le_sq₀
      (add_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
    nlinarith only [hsq, hxprod, hyprod, hxyprod]
  linarith
end RiemannResearch.Analysis.ProjectionPairingSplit
namespace RiemannResearch.Analysis.FiniteHilbertGram
open ProjectionPairingSplit
noncomputable section
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
theorem gram_pairing_split {v : ι → E} (hv : LinearIndependent ℝ v) (x y : E) :
    inner ℝ x y =
      dotProduct (cross v x) ((gramMatrix v)⁻¹.mulVec (cross v y)) +
      inner ℝ (x - (synthesisSpan v).starProjection x)
        (y - (synthesisSpan v).starProjection y) := by
  rw [← projection_inner_eq_inverseGram hv]
  exact pairing_split _ _ _
theorem gram_pairing_remainder_sq_le {v : ι → E} (hv : LinearIndependent ℝ v) (x y : E) :
    (inner ℝ x y - dotProduct (cross v x) ((gramMatrix v)⁻¹.mulVec (cross v y))) ^ 2 ≤
      (‖x‖ ^ 2 - dotProduct (cross v x) ((gramMatrix v)⁻¹.mulVec (cross v x))) *
      (‖y‖ ^ 2 - dotProduct (cross v y) ((gramMatrix v)⁻¹.mulVec (cross v y))) := by
  have h := residual_pairing_sq_le (synthesisSpan v) x y
  simpa only [← real_inner_self_eq_norm_sq, projection_inner_eq_inverseGram hv] using h
end
end RiemannResearch.Analysis.FiniteHilbertGram
