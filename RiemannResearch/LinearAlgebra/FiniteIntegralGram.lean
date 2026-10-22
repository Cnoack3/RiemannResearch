import RiemannResearch.LinearAlgebra.FinitePrimePairResidual
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring

/-!
# Actual finite integral Gram identity

Prepared as a mathematical source continuation for coordinator checking.
Current checking evidence and remaining obligations are recorded in
`RiemannResearch/ANNULAR_FORMALIZATION_20261010.md`.
This historical preparation note is not a current verification claim.

Expected companion: `RiemannResearch.LinearAlgebra.FinitePrimePairResidual`.

This extends the finite discrete Gram identity to a genuine measure integral.
Integrability of every product is explicit and is used to interchange the
finite sums with the integral. No arithmetic or asymptotic provider is assumed.
The source APIs were checked at Mathlib 51e6992efd06126df61a496bebf8f49482a4e129.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators

namespace RiemannResearch.LinearAlgebra

variable {ι α : Type*} [DecidableEq ι] [MeasurableSpace α]

def integralWeightedGram (μ : Measure α) (w : α → ℝ)
    (W : ι → α → ℝ) (i j : ι) : ℝ :=
  ∫ x, W i x * W j x * w x ∂μ

theorem integralWeightedGram_symmetric (μ : Measure α) (w : α → ℝ)
    (W : ι → α → ℝ) (i j : ι) :
    integralWeightedGram μ w W i j = integralWeightedGram μ w W j i := by
  unfold integralWeightedGram
  apply integral_congr_ae
  exact Eventually.of_forall (fun _ => by ring)

/-- The coefficient identity is pointwise and retains every cross term. -/
theorem finite_square_mul_eq_double_sum (s : Finset ι)
    (c z : ι → ℝ) (w : ℝ) :
    (∑ i ∈ s, c i * z i) ^ 2 * w =
      ∑ i ∈ s, ∑ j ∈ s, c i * c j * (z i * z j * w) := by
  rw [pow_two, Finset.sum_mul_sum]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Genuine integrated Gram square, requiring only the local product
integrability needed for the two finite sum/integral interchanges. -/
theorem integral_finite_square_eq_gram (μ : Measure α) (s : Finset ι)
    (c : ι → ℝ) (w : α → ℝ) (W : ι → α → ℝ)
    (hpair : ∀ i ∈ s, ∀ j ∈ s,
      Integrable (fun x => W i x * W j x * w x) μ) :
    (∫ x, (∑ i ∈ s, c i * W i x) ^ 2 * w x ∂μ) =
      ∑ i ∈ s, ∑ j ∈ s, c i * c j * integralWeightedGram μ w W i j := by
  have hc : ∀ i ∈ s, ∀ j ∈ s,
      Integrable (fun x => c i * c j * (W i x * W j x * w x)) μ := by
    intro i hi j hj
    exact (hpair i hi j hj).const_mul (c i * c j)
  calc
    (∫ x, (∑ i ∈ s, c i * W i x) ^ 2 * w x ∂μ) =
        ∫ x, ∑ i ∈ s, ∑ j ∈ s,
          c i * c j * (W i x * W j x * w x) ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => finite_square_mul_eq_double_sum s c
        (fun i => W i x) (w x))
    _ = ∑ i ∈ s, ∫ x, ∑ j ∈ s,
          c i * c j * (W i x * W j x * w x) ∂μ := by
      exact integral_finsetSum s (fun i hi => integrable_finsetSum s (hc i hi))
    _ = ∑ i ∈ s, ∑ j ∈ s,
          ∫ x, c i * c j * (W i x * W j x * w x) ∂μ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_finsetSum s (hc i hi)
    _ = ∑ i ∈ s, ∑ j ∈ s,
          c i * c j * integralWeightedGram μ w W i j := by
      simp only [integral_const_mul, integralWeightedGram]

theorem centeredKernelEnergy_integralGram_eq (μ : Measure α) (s : Finset ι)
    (v b : ι → ℝ) (w : α → ℝ) (W : ι → α → ℝ)
    (hpair : ∀ i ∈ s, ∀ j ∈ s,
      Integrable (fun x => W i x * W j x * w x) μ) :
    centeredKernelEnergy s v b (integralWeightedGram μ w W) =
      ∫ x, (∑ i ∈ s, (v i - b i) * W i x) ^ 2 * w x ∂μ := by
  simpa only [centeredKernelEnergy] using
    (integral_finite_square_eq_gram μ s (fun i => v i - b i) w W hpair).symm

theorem centeredKernelEnergy_integralGram_nonnegative
    (μ : Measure α) (s : Finset ι) (v b : ι → ℝ)
    (w : α → ℝ) (W : ι → α → ℝ)
    (hpair : ∀ i ∈ s, ∀ j ∈ s,
      Integrable (fun x => W i x * W j x * w x) μ)
    (hw : 0 ≤ᵐ[μ] w) :
    0 ≤ centeredKernelEnergy s v b (integralWeightedGram μ w W) := by
  rw [centeredKernelEnergy_integralGram_eq μ s v b w W hpair]
  exact integral_nonneg_of_ae (hw.mono (fun x hx => mul_nonneg (sq_nonneg _) hx))

end RiemannResearch.LinearAlgebra
