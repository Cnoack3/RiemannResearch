/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.GapKernelPolynomial

/-! # Strict half-line positivity from integer square certificates

If D P(X) - A(X)^2 - X B(X)^2 has nonnegative coefficients and strictly
positive constant term, then P is strictly positive on the whole ray.
All four input polynomials use ascending integer coefficients.
-/

namespace RiemannResearch.Analysis.GapKernelPolynomial

def multiplyCoefficients : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: p, q => add (scale a q) (0 :: multiplyCoefficients p q)

theorem value_multiplyCoefficients (p q : List ℤ) (x : ℝ) :
    value (multiplyCoefficients p q) x = value p x * value q x := by
  induction p with
  | nil => simp [multiplyCoefficients, value]
  | cons a p ih =>
    simp only [multiplyCoefficients, value_add, value_scale, value, Int.cast_zero, zero_add, ih]
    ring

def squareRemainder (D : ℤ) (p a b : List ℤ) : List ℤ :=
  add (scale D p) (scale (-1) (add (multiplyCoefficients a a) (0 :: multiplyCoefficients b b)))

theorem positive_of_squareRemainder {D : ℤ} (hD : 0 < D) {p a b : List ℤ}
    (h : checkRay (squareRemainder D p a b) = true) (x : ℝ) (hx : 0 ≤ x) : 0 < value p x := by
  have H := checkRay_sound _ hx h
  simp only [squareRemainder, value_add, value_scale, value_multiplyCoefficients, value,
    Int.cast_zero, Int.cast_neg, Int.cast_one, zero_add, neg_one_mul] at H
  apply (mul_pos_iff_of_pos_left (Int.cast_pos.mpr hD : (0 : ℝ) < D)).mp
  nlinarith only [H, sq_nonneg (value a x), mul_nonneg hx (sq_nonneg (value b x))]

end RiemannResearch.Analysis.GapKernelPolynomial
