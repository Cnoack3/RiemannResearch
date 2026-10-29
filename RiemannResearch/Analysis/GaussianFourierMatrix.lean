import RiemannResearch.Analysis.GaussianPolynomialFourier
import RiemannResearch.Analysis.GaussianSignedMatrixAlgebra
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Module.LinearMap.Basic

/-!
# Gaussian Fourier integrals as finite Hankel functionals

The real part of the proved Gaussian polynomial Fourier transform is an actual
real linear functional. It instantiates `polynomialFunctional_square` and
`poleReduced_quadratic` from `GaussianSignedMatrixAlgebra`.

Source: GaussianActualZetaExplicitFormula20261029.md, Sections 2, 5, and 6,
for the intended Fourier contribution and finite matrix identities. This module
does not identify the Fourier functional with the complete arithmetic zeta
functional, and asserts no positivity or actual-zero formula.
-/

noncomputable section

namespace RiemannResearch.Analysis.GaussianFourierMatrix
open RiemannResearch.Analysis.GaussianPolynomialFourier
open RiemannResearch.Analysis.GaussianSignedMatrix

/-- Real part of the actual Fourier transform at one frequency. -/
def realFunctional (R : ℝ) (hR : 0 < R) (τ u : ℝ) :
    Polynomial ℝ →ₗ[ℝ] ℝ :=
  Complex.reCLM.toLinearMap.comp (polynomialTransform R hR τ u)

/-- Real Fourier moment in the shifted polynomial coordinate. -/
def realMoment (R τ u : ℝ) (k : ℕ) : ℝ :=
  (Complex.exp (-Complex.I * τ * u) *
    (Complex.I^k * iteratedDeriv k (density R) u)).re

theorem realFunctional_X_pow {R : ℝ} (hR : 0 < R) (τ u : ℝ) (k : ℕ) :
    realFunctional R hR τ u ((Polynomial.X : Polynomial ℝ)^k) =
      realMoment R τ u k := by
  exact congrArg Complex.re (polynomialTransform_X_pow hR τ u k)

/-- The finite Hankel identity for the actual Gaussian Fourier integral. -/
theorem fourier_quadratic {R : ℝ} (hR : 0 < R) (τ u : ℝ)
    (n : ℕ) (c : Fin n → ℝ) :
    (transform (test R τ (coefficientPolynomial n c ^ 2)) u).re =
      quadratic (hankel n (realMoment R τ u)) c := by
  change realFunctional R hR τ u (coefficientPolynomial n c ^ 2) = _
  simpa only [realFunctional_X_pow] using
    polynomialFunctional_square (realFunctional R hR τ u) n c

/-- Pole-factor multiplication gives the existing exact five-moment transform.
This statement does not assert a zero identity or a sign for the matrix. -/
theorem fourier_poleReduced_quadratic {R : ℝ} (hR : 0 < R) (τ u : ℝ)
    (n : ℕ) (c : Fin n → ℝ) :
    (transform (test R τ ((polePolynomial τ * coefficientPolynomial n c)^2)) u).re =
      quadratic (hankel n (poleReducedMoment (realMoment R τ u) τ)) c := by
  change realFunctional R hR τ u ((polePolynomial τ * coefficientPolynomial n c)^2) = _
  simpa only [realFunctional_X_pow] using
    poleReduced_quadratic (realFunctional R hR τ u) τ n c
end RiemannResearch.Analysis.GaussianFourierMatrix
