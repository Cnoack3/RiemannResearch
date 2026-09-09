import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.Tactic.Linarith

/-! # Recovering a positive operator norm bound from quadratic estimates -/

namespace RiemannResearch.Analysis.PositiveQuadraticNorm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private def operatorForm (P : E →ₗ[ℝ] E) : LinearMap.BilinForm ℝ E where
  toFun x :=
    { toFun := fun y => inner ℝ x (P y)
      map_add' := by intro y z; simp [map_add, inner_add_right]
      map_smul' := by intro c y; simp [map_smul, inner_smul_right] }
  map_add' := by intro x y; ext z; simp [inner_add_left]
  map_smul' := by intro c x; ext y; simp [inner_smul_left]

/-- Positive-form Cauchy--Schwarz needs the quadratic bound only at x and Px.
This avoids an assumption about a spectral decomposition or eigenvectors. -/
theorem norm_apply_le_of_quadratic_bounds (P : E →ₗ[ℝ] E)
    (hsym : ∀ x y, inner ℝ x (P y) = inner ℝ y (P x))
    (hpos : ∀ x, 0 ≤ inner ℝ x (P x)) (x : E) (q : ℝ) (hq : 0 ≤ q)
    (hx : inner ℝ x (P x) ≤ q * ‖x‖ ^ 2)
    (hPx : inner ℝ (P x) (P (P x)) ≤ q * ‖P x‖ ^ 2) :
    ‖P x‖ ≤ q * ‖x‖ := by
  let B := operatorForm P
  have hBpos : ∀ y, 0 ≤ B y y := hpos
  have hBsym : LinearMap.IsSymm B := by
    constructor
    intro y z
    exact hsym y z
  have hCS := LinearMap.BilinForm.apply_sq_le_of_symm B hBpos hBsym (P x) x
  change (inner ℝ (P x) (P x)) ^ 2 ≤
    inner ℝ (P x) (P (P x)) * inner ℝ x (P x) at hCS
  rw [real_inner_self_eq_norm_sq] at hCS
  have hprod := mul_le_mul hPx hx (hpos x) (mul_nonneg hq (sq_nonneg ‖P x‖))
  have hpower : ‖P x‖ ^ 2 * ‖P x‖ ^ 2 ≤ ‖P x‖ ^ 2 * (q * ‖x‖) ^ 2 := by
    nlinarith only [hCS, hprod]
  by_cases hz : P x = 0
  · simp only [hz, norm_zero]
    exact mul_nonneg hq (norm_nonneg x)
  · have hnorm : 0 < ‖P x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
    have hs := le_of_mul_le_mul_left hpower hnorm
    nlinarith [norm_nonneg (P x), mul_nonneg hq (norm_nonneg x)]

end RiemannResearch.Analysis.PositiveQuadraticNorm
