import Mathlib.MeasureTheory.Integral.Bochner.Basic
import RiemannResearch.LinearAlgebra.FiniteCumulativeCellEnergy

/-!
# Actual integral bridge for cumulative-cell energy

Source: user-provided `V_Zeta_Vector_Spaces_Research_2026-09-16.md`, §7.
The identities here connect the finite signed quadratic to actual Bochner
integrals. Taking `f x = x` and taking `μ` to be the weighted measure restricted
to one prime-power interval gives the moments used in the report.

All integrability conditions needed to split signed terms are explicit.
No arbitrary cancellation of nonintegrable integrals is used. These statements
establish the exact local geometry, not an estimate for the prescribed
von Mangoldt jumps, and not the global RH criterion.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace RiemannResearch.Analysis.CellEnergy

open RiemannResearch.LinearAlgebra.CumulativeCellEnergy

variable {α : Type*} [MeasurableSpace α]

/-- Expanding the square preserves integrability of all signed terms. -/
theorem integrable_constant_residual_square (μ : Measure α) (f : α → ℝ) (c : ℝ)
    (h1 : Integrable (fun _ : α => (1 : ℝ)) μ)
    (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ) :
    Integrable (fun x => (c - f x) ^ 2) μ := by
  have he : (fun x => (c - f x) ^ 2) =
      (fun x => c ^ 2 * (1 : ℝ) - (2 * c) * f x + f x ^ 2) := by
    funext x
    ring
  rw [he]
  exact ((h1.const_mul (c ^ 2)).sub (hf.const_mul (2 * c))).add hf2

/-- The exact signed quadratic expansion in the three actual moments. -/
theorem integral_constant_residual_square (μ : Measure α) (f : α → ℝ) (c : ℝ)
    (h1 : Integrable (fun _ : α => (1 : ℝ)) μ)
    (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ) :
    (∫ x, (c - f x) ^ 2 ∂μ) =
      (∫ _ : α, (1 : ℝ) ∂μ) * c ^ 2 -
        2 * (∫ x, f x ∂μ) * c + (∫ x, f x ^ 2 ∂μ) := by
  have he : (fun x => (c - f x) ^ 2) =
      (fun x => c ^ 2 * (1 : ℝ) - (2 * c) * f x + f x ^ 2) := by
    funext x
    ring
  have hsub : Integrable (fun x => c ^ 2 * (1 : ℝ) - (2 * c) * f x) μ :=
    (h1.const_mul (c ^ 2)).sub (hf.const_mul (2 * c))
  rw [he, integral_add hsub hf2,
    integral_sub (f := fun _ : α => c ^ 2 * (1 : ℝ))
      (g := fun x => (2 * c) * f x) (h1.const_mul (c ^ 2)) (hf.const_mul (2 * c))]
  simp only [integral_const_mul]
  ring

/-- Weighted variance decomposition with the mass and moments kept explicit. -/
theorem integral_constant_residual_square_completed
    (μ : Measure α) (f : α → ℝ) (c : ℝ)
    (h1 : Integrable (fun _ : α => (1 : ℝ)) μ)
    (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hw : (∫ _ : α, (1 : ℝ) ∂μ) ≠ 0) :
    (∫ x, (c - f x) ^ 2 ∂μ) =
      (∫ _ : α, (1 : ℝ) ∂μ) *
        (c - (∫ x, f x ∂μ) / (∫ _ : α, (1 : ℝ) ∂μ)) ^ 2 +
      ((∫ x, f x ^ 2 ∂μ) -
        (∫ x, f x ∂μ) ^ 2 / (∫ _ : α, (1 : ℝ) ∂μ)) := by
  rw [integral_constant_residual_square μ f c h1 hf hf2]
  exact one_cell_square_completion _ _ _ _ hw

theorem integral_mean_residual_square (μ : Measure α) (f : α → ℝ)
    (h1 : Integrable (fun _ : α => (1 : ℝ)) μ)
    (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hw : (∫ _ : α, (1 : ℝ) ∂μ) ≠ 0) :
    (∫ x, ((∫ y, f y ∂μ) / (∫ _ : α, (1 : ℝ) ∂μ) - f x) ^ 2 ∂μ) =
      (∫ x, f x ^ 2 ∂μ) -
        (∫ x, f x ∂μ) ^ 2 / (∫ _ : α, (1 : ℝ) ∂μ) := by
  simpa using integral_constant_residual_square_completed μ f
    ((∫ x, f x ∂μ) / (∫ _ : α, (1 : ℝ) ∂μ)) h1 hf hf2 hw

/-- The geometric minimum is itself an actual integral of a nonnegative square. -/
theorem integral_variance_remainder_nonneg (μ : Measure α) (f : α → ℝ)
    (h1 : Integrable (fun _ : α => (1 : ℝ)) μ)
    (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hw : (∫ _ : α, (1 : ℝ) ∂μ) ≠ 0) :
    0 ≤ (∫ x, f x ^ 2 ∂μ) -
      (∫ x, f x ∂μ) ^ 2 / (∫ _ : α, (1 : ℝ) ∂μ) := by
  rw [← integral_mean_residual_square μ f h1 hf hf2 hw]
  exact integral_nonneg (fun x => sq_nonneg _)

/-- The exact price of replacing a prescribed constant by the cell mean. -/
theorem integral_excess_energy (μ : Measure α) (f : α → ℝ) (c : ℝ)
    (h1 : Integrable (fun _ : α => (1 : ℝ)) μ)
    (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hw : (∫ _ : α, (1 : ℝ) ∂μ) ≠ 0) :
    (∫ x, (c - f x) ^ 2 ∂μ) -
      (∫ x, ((∫ y, f y ∂μ) / (∫ _ : α, (1 : ℝ) ∂μ) - f x) ^ 2 ∂μ) =
      (∫ _ : α, (1 : ℝ) ∂μ) *
        (c - (∫ x, f x ∂μ) / (∫ _ : α, (1 : ℝ) ∂μ)) ^ 2 := by
  rw [integral_constant_residual_square_completed μ f c h1 hf hf2 hw,
    integral_mean_residual_square μ f h1 hf hf2 hw]
  ring

theorem integral_mean_minimizes (μ : Measure α) (f : α → ℝ) (c : ℝ)
    (h1 : Integrable (fun _ : α => (1 : ℝ)) μ)
    (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hw : 0 < (∫ _ : α, (1 : ℝ) ∂μ)) :
    (∫ x, ((∫ y, f y ∂μ) / (∫ _ : α, (1 : ℝ) ∂μ) - f x) ^ 2 ∂μ) ≤
      (∫ x, (c - f x) ^ 2 ∂μ) := by
  have he := integral_excess_energy μ f c h1 hf hf2 (ne_of_gt hw)
  have hn := mul_nonneg (le_of_lt hw)
    (sq_nonneg (c - (∫ x, f x ∂μ) / (∫ _ : α, (1 : ℝ) ∂μ)))
  linarith

theorem integral_mean_unique (μ : Measure α) (f : α → ℝ) (c : ℝ)
    (h1 : Integrable (fun _ : α => (1 : ℝ)) μ)
    (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hw : 0 < (∫ _ : α, (1 : ℝ) ∂μ)) :
    ((∫ x, (c - f x) ^ 2 ∂μ) =
      (∫ x, ((∫ y, f y ∂μ) / (∫ _ : α, (1 : ℝ) ∂μ) - f x) ^ 2 ∂μ)) ↔
      c = (∫ x, f x ∂μ) / (∫ _ : α, (1 : ℝ) ∂μ) := by
  constructor
  · intro hc
    have he := integral_excess_energy μ f c h1 hf hf2 (ne_of_gt hw)
    rw [hc, sub_self] at he
    have hz := (mul_eq_zero.mp he.symm).resolve_left (ne_of_gt hw)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
  · rintro rfl
    rfl

/-- The correction norm equals the excess, without dropping a signed term. -/
theorem integral_mean_correction_cost (μ : Measure α) (f : α → ℝ) (c : ℝ)
    (h1 : Integrable (fun _ : α => (1 : ℝ)) μ)
    (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hw : (∫ _ : α, (1 : ℝ) ∂μ) ≠ 0) :
    (∫ _ : α, ((∫ x, f x ∂μ) / (∫ _ : α, (1 : ℝ) ∂μ) - c) ^ 2 ∂μ) =
      (∫ x, (c - f x) ^ 2 ∂μ) -
        (∫ x, ((∫ y, f y ∂μ) / (∫ _ : α, (1 : ℝ) ∂μ) - f x) ^ 2 ∂μ) := by
  rw [integral_excess_energy μ f c h1 hf hf2 hw]
  calc
    _ = ∫ _ : α,
        ((∫ x, f x ∂μ) / (∫ _ : α, (1 : ℝ) ∂μ) - c) ^ 2 * (1 : ℝ) ∂μ := by
      simp only [mul_one]
    _ = ((∫ x, f x ∂μ) / (∫ _ : α, (1 : ℝ) ∂μ) - c) ^ 2 *
        (∫ _ : α, (1 : ℝ) ∂μ) := integral_const_mul _ _
    _ = _ := by ring

/-- Actual cell integrals instantiate the finite cumulative signed-energy model. -/
theorem signedCellEnergy_eq_sum_integrals (n : ℕ) (μ : ℕ → Measure α)
    (f : α → ℝ) (a : ℕ → ℝ)
    (h1 : ∀ i ∈ Finset.range n, Integrable (fun _ : α => (1 : ℝ)) (μ i))
    (hf : ∀ i ∈ Finset.range n, Integrable f (μ i))
    (hf2 : ∀ i ∈ Finset.range n, Integrable (fun x => f x ^ 2) (μ i)) :
    signedCellEnergy n
      (fun i => ∫ _ : α, (1 : ℝ) ∂(μ i))
      (fun i => ∫ x, f x ∂(μ i))
      (fun i => ∫ x, f x ^ 2 ∂(μ i)) a =
      ∑ i ∈ Finset.range n, ∫ x, (cumulative a (i + 1) - f x) ^ 2 ∂(μ i) := by
  unfold signedCellEnergy
  apply Finset.sum_congr rfl
  intro i hi
  exact (integral_constant_residual_square (μ i) f (cumulative a (i + 1))
    (h1 i hi) (hf i hi) (hf2 i hi)).symm

end RiemannResearch.Analysis.CellEnergy
