/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.GapKernelPolynomial

/-!
# Positive quadratic deflation on a half-line

A monic quadratic with negative discriminant is positive everywhere.
Exact synthetic division witnesses positivity when every linear remainder
has nonnegative coefficients and the last quotient has positive constant
term and nonnegative coefficients. The certificate consists only of the
integer coefficient pairs for the monic quadratics.
-/

namespace RiemannResearch.Analysis.GapKernelPolynomial

theorem value_at_zero (p : List ℤ) : value p 0 = (p.headD 0 : ℝ) := by
  cases p <;> simp [value]

structure QuadraticDivision where
  quotient : List ℤ
  constant : ℤ
  linear : ℤ

/-- Synthetic division by x² + a x + b, in increasing monomial order. -/
def divideQuadratic (a b : ℤ) : List ℤ → QuadraticDivision
  | [] => ⟨[], 0, 0⟩
  | h :: p =>
    let d := divideQuadratic a b p
    ⟨d.linear :: d.quotient, h-b*d.linear, d.constant-a*d.linear⟩

theorem divideQuadratic_identity (a b : ℤ) (p : List ℤ) (x : ℝ) :
    value p x = (x^2 + a*x + b)*value (divideQuadratic a b p).quotient x +
      ((divideQuadratic a b p).constant + x*(divideQuadratic a b p).linear) := by
  induction p with
  | nil => simp [value, divideQuadratic]
  | cons h p ih =>
    simp only [divideQuadratic, value, Int.cast_sub, Int.cast_mul]
    rw [ih]
    ring

def checkQuadratics : List (ℤ × ℤ) → List ℤ → Bool
  | [], p => checkRay p
  | (a,b) :: rest, p =>
    let d := divideQuadratic a b p
    ((decide (a*a < 4*b) && decide (0 ≤ d.constant)) && decide (0 ≤ d.linear)) &&
      checkQuadratics rest d.quotient

theorem checkQuadratics_sound (factors : List (ℤ × ℤ)) (p : List ℤ) {x : ℝ}
    (hx : 0 ≤ x) (h : checkQuadratics factors p = true) : 0 < value p x := by
  induction factors generalizing p with
  | nil => exact checkRay_sound p hx h
  | cons factor rest ih =>
    obtain ⟨a,b⟩ := factor
    simp only [checkQuadratics, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hd,hc⟩,hl⟩,hq⟩ := h
    have hd' : (a : ℝ)*a < 4*b := by exact_mod_cast hd
    have hc' : (0 : ℝ) ≤ (divideQuadratic a b p).constant := by exact_mod_cast hc
    have hl' : (0 : ℝ) ≤ (divideQuadratic a b p).linear := by exact_mod_cast hl
    have hf : 0 < x^2 + a*x + b := by nlinarith [sq_nonneg (2*x+a)]
    rw [divideQuadratic_identity a b p x]
    exact add_pos_of_pos_of_nonneg (mul_pos hf (ih _ hq)) (add_nonneg hc' (mul_nonneg hx hl'))

/-- A common positive integer dilation changes neither sign nor the ray. -/
theorem positive_of_scaled_quadratics (D : ℤ) (hD : 0 < D)
    (p : List ℤ) (factors : List (ℤ × ℤ))
    (h : checkQuadratics factors (clearScale D p) = true)
    {x : ℝ} (hx : 0 ≤ x) : 0 < value p x := by
  have hD' : (0 : ℝ) < D := Int.cast_pos.mpr hD
  have hv := checkQuadratics_sound factors _ (mul_nonneg hD'.le hx) h
  rw [value_clearScale] at hv
  exact (mul_pos_iff_of_pos_left (pow_pos hD' _)).mp hv

end RiemannResearch.Analysis.GapKernelPolynomial
