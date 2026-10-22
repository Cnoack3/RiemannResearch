import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Cancellation of a common complex factor in pair correlation

Source: user-provided Mellin DPP discussion, 2026-09-20. The two-point
expression is the algebraic expression in the determinantal correlation
formula (Hough--Krishnapur--Peres--Virag, arXiv:math/0503110). This module
does not construct a probability law. Its RH consumer is the exact Mellin
inverse-Gram kernel.
-/

noncomputable section
namespace RiemannResearch.Analysis.ComplexKernel

variable {X : Type*}

def envelopeKernel (Z : X → ℂ) (A : X → X → ℂ) (x y : X) : ℂ :=
  Z x * star (Z y) * A x y

def pairDensity (K : X → X → ℂ) (x y : X) : ℝ :=
  (K x x).re * (K y y).re - ‖K x y‖ ^ 2

theorem envelope_diagonal_re (Z : X → ℂ) (A : X → X → ℂ) (x : X) :
    (envelopeKernel Z A x x).re = ‖Z x‖ ^ 2 * (A x x).re := by
  simp only [envelopeKernel, Complex.mul_re, Complex.mul_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.sq_norm, Complex.normSq_apply]
  ring

theorem envelope_norm_sq (Z : X → ℂ) (A : X → X → ℂ) (x y : X) :
    ‖envelopeKernel Z A x y‖ ^ 2 =
      ‖Z x‖ ^ 2 * ‖Z y‖ ^ 2 * ‖A x y‖ ^ 2 := by
  simp only [envelopeKernel, norm_mul, norm_star, mul_pow]

theorem envelope_pairDensity (Z : X → ℂ) (A : X → X → ℂ) (x y : X) :
    pairDensity (envelopeKernel Z A) x y =
      (‖Z x‖ ^ 2 * ‖Z y‖ ^ 2) * pairDensity A x y := by
  rw [pairDensity, envelope_diagonal_re, envelope_diagonal_re, envelope_norm_sq]
  unfold pairDensity
  ring

/-- The common envelope disappears wherever the two marginal intensities
are nonzero. No limiting sine-kernel assertion is made. -/
theorem normalized_pairDensity_envelope
    (Z : X → ℂ) (A : X → X → ℂ) (x y : X)
    (hx : Z x ≠ 0) (hy : Z y ≠ 0)
    (hAx : (A x x).re ≠ 0) (hAy : (A y y).re ≠ 0) :
    pairDensity (envelopeKernel Z A) x y /
        ((envelopeKernel Z A x x).re * (envelopeKernel Z A y y).re) =
      1 - ‖A x y‖ ^ 2 / ((A x x).re * (A y y).re) := by
  have hnx : ‖Z x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hny : ‖Z y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  rw [envelope_pairDensity, envelope_diagonal_re, envelope_diagonal_re]
  unfold pairDensity
  field_simp [hnx, hny, hAx, hAy]

theorem envelope_row_zero_of_zero (Z : X → ℂ) (A : X → X → ℂ)
    {x : X} (hx : Z x = 0) (y : X) : envelopeKernel Z A x y = 0 := by
  simp [envelopeKernel, hx]

end RiemannResearch.Analysis.ComplexKernel
