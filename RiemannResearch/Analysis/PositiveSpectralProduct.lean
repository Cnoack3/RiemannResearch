import RiemannResearch.Analysis.PositiveSpectralPolynomial
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Infinite positive spectral products have only real zeros

Source: user-provided Hilbert--Polya determinant proposal, 2026-09-20.
The convergence and nonvanishing theorem for norm-summable perturbations of
one comes from Mathlib. This file constructs the actual scalar infinite
product from nonnegative summable spectral weights and proves all its zeros
real. Identifying it with an operator Fredholm determinant or the normalized
completed zeta function remains a separate research obligation.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.PositiveSpectralProduct

variable {ι : Type*}

def product (τ : ι → ℝ) (z : ℂ) : ℂ :=
  ∏' i, (1 - z ^ 2 * (τ i : ℂ))

theorem perturbation_norm_summable (τ : ι → ℝ)
    (hτ : ∀ i, 0 ≤ τ i) (hs : Summable τ) (z : ℂ) :
    Summable (fun i => ‖-(z ^ 2 * (τ i : ℂ))‖) := by
  have hn (i : ι) : ‖-(z ^ 2 * (τ i : ℂ))‖ = ‖z ^ 2‖ * τ i := by
    simp only [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hτ i)]
  simpa only [hn] using hs.mul_left ‖z ^ 2‖

theorem multipliable (τ : ι → ℝ) (hτ : ∀ i, 0 ≤ τ i)
    (hs : Summable τ) (z : ℂ) :
    Multipliable (fun i => (1 - z ^ 2 * (τ i : ℂ))) := by
  simpa only [sub_eq_add_neg] using
    multipliable_one_add_of_summable (perturbation_norm_summable τ hτ hs z)

theorem product_ne_zero_of_factors_ne_zero (τ : ι → ℝ)
    (hτ : ∀ i, 0 ≤ τ i) (hs : Summable τ) (z : ℂ)
    (hf : ∀ i, 1 - z ^ 2 * (τ i : ℂ) ≠ 0) : product τ z ≠ 0 := by
  simpa only [product, sub_eq_add_neg] using
    tprod_one_add_ne_zero_of_summable (f := fun i => -(z ^ 2 * (τ i : ℂ)))
      (by simpa only [sub_eq_add_neg] using hf)
      (perturbation_norm_summable τ hτ hs z)

/-- Norm summability rules out a vanishing product without any vanishing
factor. Every individual positive spectral factor has only real zeros. -/
theorem product_ne_zero_of_nonreal (τ : ι → ℝ)
    (hτ : ∀ i, 0 ≤ τ i) (hs : Summable τ) (z : ℂ) (hz : z.im ≠ 0) :
    product τ z ≠ 0 := by
  apply product_ne_zero_of_factors_ne_zero τ hτ hs z
  intro i hi
  exact hz (PositiveSpectralPolynomial.factor_zero_im_eq_zero (τ i) (hτ i) z hi)

theorem product_zero_im_eq_zero (τ : ι → ℝ)
    (hτ : ∀ i, 0 ≤ τ i) (hs : Summable τ) (z : ℂ)
    (hz : product τ z = 0) : z.im = 0 := by
  by_contra hnonreal
  exact product_ne_zero_of_nonreal τ hτ hs z hnonreal hz

end RiemannResearch.Analysis.PositiveSpectralProduct
