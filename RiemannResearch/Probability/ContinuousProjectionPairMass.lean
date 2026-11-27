import RiemannResearch.Probability.ContinuousProjectionKernel

/-! # Total two-point mass of a finite projection DPP

Integration of the two-by-two principal determinant over its second argument
leaves the one-point intensity times rank minus one. The outer integral
therefore counts exactly the labeled ordered distinct pairs.
-/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators ComplexConjugate
namespace ProbabilityTheory.ContinuousProjectionDPP

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SigmaFinite μ] {n : ℕ}

theorem pair_det_integral_right (ψ : Fin n → X → ℂ) (hψ : ∀ i, MemLp (ψ i) 2 μ)
    (ho : ∀ i j, (∫ z, conj (ψ i z) * ψ j z ∂μ) = if i = j then 1 else 0) (x : X) :
    (∫ y, Matrix.det !![kernel ψ x x, kernel ψ x y; kernel ψ y x, kernel ψ y y] ∂μ)
      = kernel ψ x x * ((n : ℂ) - 1) := by
  simp_rw [Matrix.det_fin_two]
  change (∫ y, kernel ψ x x * kernel ψ y y - kernel ψ x y * kernel ψ y x ∂μ) = _
  rw [integral_sub ((kernel_diagonal_integrable ψ hψ).const_mul _) (kernel_product_integrable ψ hψ x x),
    integral_const_mul, kernel_trace ψ hψ ho, kernel_reproducing ψ hψ ho]
  ring

theorem total_pair_det_integral (ψ : Fin n → X → ℂ) (hψ : ∀ i, MemLp (ψ i) 2 μ)
    (ho : ∀ i j, (∫ z, conj (ψ i z) * ψ j z ∂μ) = if i = j then 1 else 0) :
    (∫ x, ∫ y, Matrix.det !![kernel ψ x x, kernel ψ x y; kernel ψ y x, kernel ψ y y] ∂μ ∂μ)
      = (n : ℂ) * ((n : ℂ) - 1) := by
  simp_rw [pair_det_integral_right ψ hψ ho]
  rw [integral_mul_const, kernel_trace ψ hψ ho]

end ProbabilityTheory.ContinuousProjectionDPP
