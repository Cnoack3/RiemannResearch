import RiemannResearch.Analysis.PositiveSpectralPolynomial
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

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


open Filter
open scoped Topology

/-- Ordered finite factors of a fixed nonnegative summable spectrum. -/
def partialProduct (τ : ℕ → ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  ∏ j ∈ Finset.range N, (1 - z ^ 2 * (τ j : ℂ))

theorem tendsto_partialProduct (τ : ℕ → ℝ)
    (hτ : ∀ j, 0 ≤ τ j) (hs : Summable τ) (z : ℂ) :
    Tendsto (fun N => partialProduct τ N z) atTop (𝓝 (product τ z)) := by
  simpa only [partialProduct, product] using
    (multipliable τ hτ hs z).tendsto_prod_tprod_nat

/-- Pointwise convergence identifies the limit; positivity alone does not
identify it with any independently specified entire function. -/
theorem partialProduct_limit_eq_product (τ : ℕ → ℝ)
    (hτ : ∀ j, 0 ≤ τ j) (hs : Summable τ) (z w : ℂ)
    (hw : Tendsto (fun N => partialProduct τ N z) atTop (𝓝 w)) :
    w = product τ z := by
  exact tendsto_nhds_unique hw (tendsto_partialProduct τ hτ hs z)

theorem partialProduct_limit_zero_im_eq_zero (τ : ℕ → ℝ)
    (hτ : ∀ j, 0 ≤ τ j) (hs : Summable τ) (z : ℂ)
    (hz : Tendsto (fun N => partialProduct τ N z) atTop (𝓝 0)) :
    z.im = 0 := by
  exact product_zero_im_eq_zero τ hτ hs z
    (partialProduct_limit_eq_product τ hτ hs z 0 hz).symm

/-- A locally uniform limit of these fixed-spectrum truncations is their
infinite product. This does not assert the general Hurwitz theorem for
arbitrary moving positive matrices. -/
theorem eq_product_of_locallyUniformLimit (τ : ℕ → ℝ)
    (hτ : ∀ j, 0 ≤ τ j) (hs : Summable τ)
    (F : ℂ → ℂ) (S : Set ℂ)
    (hF : TendstoLocallyUniformlyOn (partialProduct τ) F atTop S) :
    Set.EqOn F (product τ) S := by
  intro z hz
  exact partialProduct_limit_eq_product τ hτ hs z (F z) (hF.tendsto_at hz)

end RiemannResearch.Analysis.PositiveSpectralProduct
