import RiemannResearch.Analysis.GaussianPolynomialStrip
import RiemannResearch.Analysis.GaussianPolynomialFourier
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Gaussian envelopes for the actual polynomial Fourier transform

The recursively defined derivativePolynomial gives an exact finite polynomial
factor for every derivative of the normalized Gaussian. frequencyPolynomial
then represents the actual transform from GaussianPolynomialFourier exactly.
The resulting explicit envelope is uniform in the real center τ.

All complex inverse kernels and their fixed frequency moments have a common
integrable majorant on each fixed horizontal strip. This discharges their
absolute-integrability and domination requirements. The inverse identity,
holomorphy of the parameter integral, and zeta-specific contour and summation
results are not asserted in this module.

Source for normalization and the requested analytic obligations:
GaussianActualZetaExplicitFormula20261029.md, Sections 2--3, at
https://github.com/Cnoack3/RiemannResearch/blob/1905e5be21ec20d217b0f7c32905f09bd8720f92/RiemannResearch/RH/GaussianActualZetaExplicitFormula20261029.md.
The derivative recurrence is the direct product-rule proof of polynomial
Gaussian closure; it does not assume the memorandum's factorial expansion.
-/

open MeasureTheory
open scoped BigOperators
noncomputable section

namespace RiemannResearch.Analysis.GaussianPolynomialFourierGrowth
open GaussianPolynomialFourier GaussianPolynomialStrip

/-- The polynomial factor in the kth derivative of the normalized Gaussian. -/
def derivativePolynomial (R : ℝ) : ℕ → Polynomial ℂ
  | 0 => 1
  | k+1 => (derivativePolynomial R k).derivative -
      Polynomial.C ((2*(R : ℂ))⁻¹) * Polynomial.X * derivativePolynomial R k

theorem iteratedDeriv_density_eq_polynomial {R : ℝ} (hR : 0 < R) (k : ℕ) :
    iteratedDeriv k (density R) =
      fun u : ℝ => (derivativePolynomial R k).eval (u : ℂ) * density R u := by
  induction k with
  | zero => simp [derivativePolynomial]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext u
    have hd := (((derivativePolynomial R k).hasDerivAt (u : ℂ)).comp_ofReal).mul
      (hasDerivAt_density hR u)
    convert! hd.deriv using 1
    simp only [derivativePolynomial, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    ring

/-- Explicit finite polynomial in frequency; no Hermite estimate is assumed. -/
def frequencyPolynomial (R : ℝ) (B : Polynomial ℝ) : Polynomial ℂ :=
  ∑ k ∈ B.support,
    Polynomial.C ((B.coeff k : ℂ)*Complex.I^k) * derivativePolynomial R k

theorem transform_test_eq_frequencyPolynomial {R : ℝ} (hR : 0 < R)
    (τ u : ℝ) (B : Polynomial ℝ) :
    transform (GaussianPolynomialFourier.test R τ B) u =
      Complex.exp (-Complex.I*τ*u) *
        ((frequencyPolynomial R B).eval (u : ℂ) * density R u) := by
  rw [transform_test hR]
  simp only [iteratedDeriv_density_eq_polynomial hR, frequencyPolynomial,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Finset.sum_mul, mul_assoc]

def frequencyConstant (R : ℝ) (B : Polynomial ℝ) : ℝ :=
  (frequencyPolynomial R B).stripGrowthConstant 0 / Real.sqrt (4*Real.pi*R)

theorem frequencyConstant_nonneg (R : ℝ) (B : Polynomial ℝ) :
    0 ≤ frequencyConstant R B :=
  div_nonneg ((frequencyPolynomial R B).stripGrowthConstant_nonneg le_rfl)
    (Real.sqrt_nonneg _)

/-- A fully discharged Gaussian bound for the actual transform. -/
theorem norm_transform_test_le {R : ℝ} (hR : 0 < R) (τ u : ℝ) (B : Polynomial ℝ) :
    ‖transform (GaussianPolynomialFourier.test R τ B) u‖ ≤
      frequencyConstant R B * (1+|u|)^(frequencyPolynomial R B).natDegree *
        Real.exp (-(1/(4*R))*u^2) := by
  rw [transform_test_eq_frequencyPolynomial hR, norm_mul, norm_phase, one_mul,
    norm_mul, density_eq_real, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ Real.exp (-u^2/(4*R))/Real.sqrt (4*Real.pi*R))]
  have hp : ‖(frequencyPolynomial R B).eval (u : ℂ)‖ ≤
      (frequencyPolynomial R B).stripGrowthConstant 0 *
        (1+|u|)^(frequencyPolynomial R B).natDegree := by
    simpa using (frequencyPolynomial R B).norm_eval_le_stripGrowthConstant
      (t := u) (y := 0) le_rfl (by simp)
  calc
    _ ≤ ((frequencyPolynomial R B).stripGrowthConstant 0 *
        (1+|u|)^(frequencyPolynomial R B).natDegree) *
        (Real.exp (-u^2/(4*R))/Real.sqrt (4*Real.pi*R)) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = _ := by
      have he : -u^2/(4*R) = -(1/(4*R))*u^2 := by ring
      rw [he]
      dsimp [frequencyConstant]
      ring

theorem continuous_transform_test {R : ℝ} (hR : 0 < R) (τ : ℝ) (B : Polynomial ℝ) :
    Continuous (transform (GaussianPolynomialFourier.test R τ B)) := by
  have he := funext (fun u => transform_test_eq_frequencyPolynomial hR τ u B)
  rw [he]
  unfold density
  fun_prop

/-- All complex inverse Fourier kernels and all fixed frequency moments are integrable. -/
theorem integrable_inverse_transform_moment {R : ℝ} (hR : 0 < R)
    (τ : ℝ) (B : Polynomial ℝ) (N : ℕ) (z : ℂ) :
    Integrable (fun u : ℝ => (u : ℂ)^N * (Complex.exp (Complex.I*z*u) *
      transform (GaussianPolynomialFourier.test R τ B) u)) := by
  exact integrable_inverse_moment_of_bound
    (show 0 < 1/(4*R) by positivity) (frequencyConstant_nonneg R B)
    (frequencyPolynomial R B).natDegree N
    (continuous_transform_test hR τ B).aestronglyMeasurable
    (fun u => norm_transform_test_le hR τ u B) z (le_refl |z.im|)

/-- A single integrable envelope for the actual inverse kernels on any fixed strip. -/
def inverseMajorant (R b : ℝ) (B : Polynomial ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  frequencyConstant R B * Real.exp (2*R*b^2) *
    (1+|u|)^((frequencyPolynomial R B).natDegree+N) * Real.exp (-(1/(8*R))*u^2)

theorem integrable_inverseMajorant {R : ℝ} (hR : 0 < R)
    (b : ℝ) (B : Polynomial ℝ) (N : ℕ) :
    Integrable (inverseMajorant R b B N) := by
  have h := (integrable_one_add_abs_pow_gaussian
    (show 0 < 1/(8*R) by positivity) ((frequencyPolynomial R B).natDegree+N)).const_mul
      (frequencyConstant R B * Real.exp (2*R*b^2))
  convert h using 1
  funext u
  dsimp [inverseMajorant]
  ring

theorem norm_inverse_transform_moment_le {R b : ℝ} (hR : 0 < R)
    (τ : ℝ) (B : Polynomial ℝ) (N : ℕ) (z : ℂ) (hz : |z.im| ≤ b) (u : ℝ) :
    ‖(u : ℂ)^N * (Complex.exp (Complex.I*z*u) *
      transform (GaussianPolynomialFourier.test R τ B) u)‖ ≤ inverseMajorant R b B N u := by
  have h := norm_inverse_moment_le_of_bound
    (show 0 < 1/(4*R) by positivity) (frequencyConstant_nonneg R B)
    (frequencyPolynomial R B).natDegree N
    (transform (GaussianPolynomialFourier.test R τ B))
    (fun v => norm_transform_test_le hR τ v B) z hz u
  have h1 : b^2/(2*(1/(4*R))) = 2*R*b^2 := by field_simp; ring
  have h2 : (1/(4*R))/2 = 1/(8*R) := by ring
  simpa only [h1, h2, inverseMajorant] using h

theorem integrable_transform_test {R : ℝ} (hR : 0 < R)
    (τ : ℝ) (B : Polynomial ℝ) :
    Integrable (transform (GaussianPolynomialFourier.test R τ B)) := by
  simpa using integrable_inverse_transform_moment hR τ B 0 0

theorem continuous_real_test (R τ : ℝ) (B : Polynomial ℝ) :
    Continuous (GaussianPolynomialFourier.test R τ B) := by
  unfold GaussianPolynomialFourier.test polynomialFunction gaussian
  fun_prop

end RiemannResearch.Analysis.GaussianPolynomialFourierGrowth
