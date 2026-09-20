import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Zeros of positive spectral determinant factors

Source: user-provided Hilbert--Polya determinant proposal, 2026-09-20.
This proves the exact scalar implication and its finite determinant version.
The infinite trace-class determinant and its identification with Xi are
separate obligations; they are not assumptions hidden in these statements.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.PositiveSpectralPolynomial

theorem factor_zero_im_eq_zero (τ : ℝ) (hτ : 0 ≤ τ) (z : ℂ)
    (hz : 1 - z ^ 2 * (τ : ℂ) = 0) : z.im = 0 := by
  have hτ0 : τ ≠ 0 := by
    intro h
    simp [h] at hz
  have hr := congrArg Complex.re hz
  have hi := congrArg Complex.im hz
  simp only [Complex.sub_re, Complex.one_re, Complex.mul_re,
    Complex.sub_im, Complex.one_im, Complex.mul_im, pow_two,
    Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, Complex.zero_im,
    mul_zero, sub_zero] at hr hi
  by_contra hy
  have hfac : (2 : ℝ) * τ * z.im ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hτ0) hy
  have hm : ((2 : ℝ) * τ * z.im) * z.re = 0 := by nlinarith [hi]
  have hre : z.re = 0 := (mul_eq_zero.mp hm).resolve_left hfac
  have hp : 0 ≤ τ * z.im ^ 2 := mul_nonneg hτ (sq_nonneg _)
  rw [hre] at hr
  norm_num at hr
  nlinarith [hr]

def diagonalMatrix {ι : Type*} [DecidableEq ι]
    (τ : ι → ℝ) (z : ℂ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => 1 - z ^ 2 * (τ i : ℂ))

theorem det_eq_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (z : ℂ) :
    (diagonalMatrix τ z).det = ∏ i, (1 - z ^ 2 * (τ i : ℂ)) := by
  exact Matrix.det_diagonal

theorem det_zero_im_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (hτ : ∀ i, 0 ≤ τ i) (z : ℂ)
    (hz : (diagonalMatrix τ z).det = 0) : z.im = 0 := by
  rw [det_eq_product] at hz
  obtain ⟨i, hi, hzero⟩ := Finset.prod_eq_zero_iff.mp hz
  exact factor_zero_im_eq_zero (τ i) (hτ i) z hzero

end RiemannResearch.Analysis.PositiveSpectralPolynomial
