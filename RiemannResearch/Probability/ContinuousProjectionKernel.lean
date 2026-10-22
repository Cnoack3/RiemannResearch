import RiemannResearch.Probability.ContinuousProjectionDensity
import RiemannResearch.Probability.ContinuousProjectionSymmetry

/-!
# Reproducing and trace identities for a continuous finite projection kernel

Source: user-requested Mellin DPP construction, 20 September 2026.
The finite sums are expanded and integrated using the actual orthonormal
Gram identity; no projection or trace provider is assumed.
-/

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators ComplexConjugate

namespace ProbabilityTheory.ContinuousProjectionDPP
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SigmaFinite μ] {n : ℕ}

theorem kernel_hermitian (ψ : Fin n → X → ℂ) (x y : X) :
    star (kernel ψ y x) = kernel ψ x y := by
  simp only [kernel, star_sum, star_mul, star_star]

theorem kernel_diagonal (ψ : Fin n → X → ℂ) (x : X) :
    kernel ψ x x = ((∑ i, ‖ψ i x‖ ^ 2 : ℝ) : ℂ) := by
  simp only [kernel, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [Complex.star_def, Complex.normSq_eq_norm_sq] using Complex.mul_conj (ψ i x)

private theorem kernel_product_expansion (ψ : Fin n → X → ℂ) (x y z : X) :
    kernel ψ x z * kernel ψ z y =
      ∑ i, ∑ j, ψ i x * (conj (ψ i z) * ψ j z) * conj (ψ j y) := by
  simp only [kernel, Finset.sum_mul, Finset.mul_sum, Complex.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem kernel_product_integrable (ψ : Fin n → X → ℂ)
    (hψ : ∀ i, MemLp (ψ i) 2 μ) (x y : X) :
    Integrable (fun z => kernel ψ x z * kernel ψ z y) μ := by
  simp_rw [kernel_product_expansion]
  apply integrable_finsetSum
  intro i hi
  apply integrable_finsetSum
  intro j hj
  exact ((integrable_cross_of_memLp ψ hψ i j).const_mul _).mul_const _

/-- The kernel is the integral kernel of a genuine finite orthogonal projection. -/
theorem kernel_reproducing (ψ : Fin n → X → ℂ)
    (hψ : ∀ i, MemLp (ψ i) 2 μ)
    (ho : ∀ i j, (∫ z, conj (ψ i z) * ψ j z ∂μ) = if i = j then 1 else 0)
    (x y : X) :
    (∫ z, kernel ψ x z * kernel ψ z y ∂μ) = kernel ψ x y := by
  simp_rw [kernel_product_expansion]
  rw [integral_finsetSum]
  · have he (i : Fin n) :
        (∫ z, ∑ j, ψ i x * (conj (ψ i z) * ψ j z) * conj (ψ j y) ∂μ) =
          ψ i x * conj (ψ i y) := by
      rw [integral_finsetSum]
      · simp only [integral_mul_const, integral_const_mul, ho]
        simp
      · intro j hj
        exact ((integrable_cross_of_memLp ψ hψ i j).const_mul _).mul_const _
    simp only [he, kernel, Complex.star_def]
  · intro i hi
    apply integrable_finsetSum
    intro j hj
    exact ((integrable_cross_of_memLp ψ hψ i j).const_mul _).mul_const _

theorem kernel_diagonal_integrable (ψ : Fin n → X → ℂ)
    (hψ : ∀ i, MemLp (ψ i) 2 μ) : Integrable (fun x => kernel ψ x x) μ := by
  unfold kernel
  apply integrable_finsetSum
  intro i hi
  simpa only [Complex.star_def, mul_comm] using integrable_cross_of_memLp ψ hψ i i

theorem kernel_trace (ψ : Fin n → X → ℂ)
    (hψ : ∀ i, MemLp (ψ i) 2 μ)
    (ho : ∀ i j, (∫ z, conj (ψ i z) * ψ j z ∂μ) = if i = j then 1 else 0) :
    (∫ x, kernel ψ x x ∂μ) = n := by
  unfold kernel
  rw [integral_finsetSum]
  · have he (i : Fin n) : (∫ x, ψ i x * star (ψ i x) ∂μ) = 1 := by
      simpa [Complex.star_def, mul_comm] using ho i i
    simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one]
  · intro i hi
    simpa only [Complex.star_def, mul_comm] using integrable_cross_of_memLp ψ hψ i i

end ProbabilityTheory.ContinuousProjectionDPP
