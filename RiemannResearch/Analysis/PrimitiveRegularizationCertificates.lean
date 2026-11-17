import RiemannResearch.Analysis.PrimitiveRegularization
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
/-!
# Approximate-source and trust-region certificates

Continuation of highest viability RH.pdf, equation (68) and agenda G1-G2:
https://drive.google.com/file/d/1smLPEbJDfOV2Z5mMSMMQvFEd3_qRYopL/view

Reuses PrimitiveRegularization's normal equations and existence theorem.
The centered identity retains the signed approximate-source correlation.
No exact target-range membership is assumed in the approximate bounds.
-/
noncomputable section
namespace RiemannResearch.Analysis.PrimitiveRegularization
variable {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

theorem trust_region_minimizes (T : E →ₗ[ℝ] Y) (S : Submodule ℝ E)
    (e : Y) (μ B : ℝ) (u v : E) (hu : u ∈ S) (hv : v ∈ S)
    (hμ : 0 ≤ μ) (hn : IsNormal T S e μ u)
    (hactive : μ * (‖u‖ ^ 2 - B) = 0) (hbudget : ‖v‖ ^ 2 ≤ B) :
    ‖T u - e‖ ^ 2 ≤ ‖T v - e‖ ^ 2 := by
  have hh := derivative_error_difference_exact T S e μ u v hu hv hn
  have hslack := mul_nonneg hμ (sub_nonneg.mpr hbudget)
  have hsq := mul_nonneg hμ (sq_nonneg ‖v - u‖)
  nlinarith [sq_nonneg ‖T (v - u)‖]

/-- The signed approximate-source correlation replaces exact range membership. -/
theorem approximate_source_centered_identity (T : E →ₗ[ℝ] Y) (S : Submodule ℝ E)
    (e : Y) (μ : ℝ) (u v : E) (hu : u ∈ S) (hv : v ∈ S)
    (hn : IsNormal T S e μ u) :
    4 * ‖T u - e‖ ^ 2 + μ * ‖v - (2 : ℝ) • u‖ ^ 2 =
      μ * ‖v‖ ^ 2 + 4 * inner ℝ (T u - e) (T v - e) := by
  have hh := hn (v - u) (S.sub_mem hv hu)
  have he : T (v - u) = (T v - e) - (T u - e) := by rw [map_sub]; abel
  rw [he, inner_sub_right (T u - e) (T v - e) (T u - e),
    real_inner_self_eq_norm_sq, inner_sub_right u v u,
    real_inner_self_eq_norm_sq] at hh
  rw [norm_sub_sq_real v ((2 : ℝ) • u), norm_smul, Real.norm_eq_abs, mul_pow,
    real_inner_smul_right, real_inner_comm u v]
  norm_num
  nlinarith only [hh]

theorem approximate_source_residual_bound (T : E →ₗ[ℝ] Y) (S : Submodule ℝ E)
    (e : Y) (μ : ℝ) (u v : E) (hu : u ∈ S) (hv : v ∈ S)
    (hμ : 0 ≤ μ) (hn : IsNormal T S e μ u) :
    ‖T u - e‖ ≤
      (‖T v - e‖ + Real.sqrt (‖T v - e‖ ^ 2 + μ * ‖v‖ ^ 2))/2 := by
  have hh := approximate_source_centered_identity T S e μ u v hu hv hn
  have hcs := real_inner_le_norm (T u - e) (T v - e)
  have hnrem := mul_nonneg hμ (sq_nonneg ‖v-(2 : ℝ) • u‖)
  have hd0 := Real.sqrt_nonneg (‖T v - e‖ ^ 2 + μ * ‖v‖ ^ 2)
  have hd := Real.sq_sqrt (show 0 ≤ ‖T v - e‖ ^ 2 + μ * ‖v‖ ^ 2 by positivity)
  nlinarith [sq_nonneg (2*‖T u - e‖ - ‖T v - e‖ -
    Real.sqrt (‖T v - e‖ ^ 2 + μ * ‖v‖ ^ 2))]

theorem exact_source_residual_le_quarter (T : E →ₗ[ℝ] Y) (S : Submodule ℝ E)
    (e : Y) (μ : ℝ) (u v : E) (hu : u ∈ S) (hv : v ∈ S)
    (hμ : 0 ≤ μ) (hn : IsNormal T S e μ u) (htarget : T v = e) :
    ‖T u - e‖ ^ 2 ≤ μ * ‖v‖ ^ 2 / 4 := by
  have hh := approximate_source_centered_identity T S e μ u v hu hv hn
  rw [htarget, sub_self, inner_zero_right, mul_zero, add_zero] at hh
  have hrem := mul_nonneg hμ (sq_nonneg ‖v-(2 : ℝ) • u‖)
  linarith

theorem approximate_source_budget (T : E →ₗ[ℝ] Y) (S : Submodule ℝ E)
    (e : Y) (μ : ℝ) (u v : E) (hu : u ∈ S) (hv : v ∈ S)
    (hμ : 0 ≤ μ) (hn : IsNormal T S e μ u)
    {δ B : ℝ} (herr : ‖T v - e‖ ^ 2 ≤ δ) (hbudget : ‖v‖ ^ 2 ≤ B) :
    ‖T u - e‖ ^ 2 + μ * ‖u‖ ^ 2 ≤ δ + μ * B :=
  (normal_minimizes T S e μ u v hu hv hμ hn).trans
    (add_le_add herr (mul_le_mul_of_nonneg_left hbudget hμ))

theorem exists_approximate_source_budget [CompleteSpace E] [CompleteSpace Y]
    (T : E →L[ℝ] Y) (e : Y) {μ : ℝ} (hμ : 0 < μ)
    (v : E) {δ B : ℝ} (herr : ‖T v - e‖ ^ 2 ≤ δ) (hbudget : ‖v‖ ^ 2 ≤ B) :
    ∃ u : E, IsNormal T.toLinearMap ⊤ e μ u ∧
      ‖T u - e‖ ^ 2 + μ * ‖u‖ ^ 2 ≤ δ + μ * B := by
  obtain ⟨u,hu⟩ := exists_normal T e hμ
  exact ⟨u,hu,approximate_source_budget T.toLinearMap ⊤ e μ u v
    (by simp) (by simp) hμ.le hu herr hbudget⟩

end RiemannResearch.Analysis.PrimitiveRegularization
