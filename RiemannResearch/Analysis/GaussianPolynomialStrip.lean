import RiemannResearch.Analysis.GaussianPolynomialFourier
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform Gaussian polynomial bounds on complex strips

For complex polynomial P, real center τ and nonnegative strip half-width b, the
explicit constant is the sum of ‖P.coeff k‖ * (1+b)^k over the support.
The exact Gaussian modulus identity precedes the uniform bound. Positive R gives
integrable majorants, including every polynomial weight. The real-polynomial
extension agrees exactly with GaussianPolynomialFourier.test.

The exponential-tilt estimate retains its exact completed-square remainder.
The inverse-kernel lemmas here take a Gaussian envelope as an explicit hypothesis;
GaussianPolynomialFourierGrowth supplies it for the actual transform.

Source for the strip statement and intended RH consumer:
GaussianActualZetaExplicitFormula20261029.md, Section 3 (equation 3.1), at
https://github.com/Cnoack3/RiemannResearch/blob/1905e5be21ec20d217b0f7c32905f09bd8720f92/RiemannResearch/RH/GaussianActualZetaExplicitFormula20261029.md.
Proof strategy: coefficientwise triangle inequality, Mathlib Complex.norm_exp,
and the existing GaussianPolynomialFourier.integrable_momentFunction.
See also Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral.
No zeta, contour, zero-sum or RH assertion is made here.
-/

open MeasureTheory
open scoped BigOperators
noncomputable section

namespace Polynomial
/-- Explicit coefficient constant for a strip of half-width b. -/
def stripGrowthConstant (P : Polynomial ℂ) (b : ℝ) : ℝ :=
  ∑ k ∈ P.support, ‖P.coeff k‖ * (1+b)^k

theorem stripGrowthConstant_nonneg (P : Polynomial ℂ) {b : ℝ} (hb : 0 ≤ b) :
    0 ≤ P.stripGrowthConstant b := by
  unfold stripGrowthConstant
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (norm_nonneg _) (by positivity))

theorem norm_eval_le_stripGrowthConstant (P : Polynomial ℂ)
    {b t y : ℝ} (hb : 0 ≤ b) (hy : |y| ≤ b) :
    ‖P.eval ((t : ℂ) + (y : ℂ)*Complex.I)‖ ≤
      P.stripGrowthConstant b * (1+|t|)^P.natDegree := by
  have hz : ‖(t : ℂ) + (y : ℂ)*Complex.I‖ ≤ (1+b)*(1+|t|) := by
    calc
      _ ≤ |t| + |y| := by
        simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
          mul_one] using norm_add_le (t : ℂ) ((y : ℂ)*Complex.I)
      _ ≤ (1+b)*(1+|t|) := by nlinarith [abs_nonneg t, mul_nonneg hb (abs_nonneg t)]
  calc
    _ ≤ ∑ k ∈ P.support, ‖P.coeff k‖ * ‖(t : ℂ)+(y : ℂ)*Complex.I‖^k := by
      rw [Polynomial.eval_eq_sum, Polynomial.sum]
      simpa only [norm_mul, norm_pow] using
        norm_sum_le P.support (fun k => P.coeff k * ((t : ℂ)+(y : ℂ)*Complex.I)^k)
    _ ≤ ∑ k ∈ P.support, ‖P.coeff k‖ * ((1+b)^k * (1+|t|)^P.natDegree) := by
      apply Finset.sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      calc
        _ ≤ ((1+b)*(1+|t|))^k := pow_le_pow_left₀ (norm_nonneg _) hz k
        _ = (1+b)^k * (1+|t|)^k := mul_pow _ _ _
        _ ≤ (1+b)^k * (1+|t|)^P.natDegree :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ (by linarith [abs_nonneg t])
              (Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hk)))
            (by positivity)
    _ = _ := by simp only [stripGrowthConstant, Finset.sum_mul, mul_assoc]
end Polynomial

namespace RiemannResearch.Analysis.GaussianPolynomialStrip
open GaussianPolynomialFourier

/-- Entire complex extension; complex coefficients are allowed. -/
def test (R τ : ℝ) (P : Polynomial ℂ) (z : ℂ) : ℂ :=
  P.eval (z-τ) * Complex.exp (-(R : ℂ)*(z-τ)^2)

theorem test_ofReal (R τ x : ℝ) (B : Polynomial ℝ) :
    test R τ (B.map Complex.ofRealHom) (x : ℂ) =
      GaussianPolynomialFourier.test R τ B x := by
  simp only [test, GaussianPolynomialFourier.test, polynomialFunction, gaussian,
    ← Complex.ofReal_sub, Polynomial.eval_map]
  congr 1
  exact Polynomial.eval₂_at_apply Complex.ofRealHom (x-τ)

theorem differentiable_test (R τ : ℝ) (P : Polynomial ℂ) :
    Differentiable ℂ (test R τ P) := by
  unfold test
  fun_prop

/-- Exact modulus identity, with no sign assumption on R. -/
theorem norm_gaussian (R t y : ℝ) :
    ‖Complex.exp (-(R : ℂ)*((t : ℂ)+(y : ℂ)*Complex.I)^2)‖ =
      Real.exp (-R*t^2 + R*y^2) := by
  rw [Complex.norm_exp]
  congr 1
  simp [pow_two, Complex.mul_re, Complex.mul_im]
  ring

theorem norm_test (R τ x y : ℝ) (P : Polynomial ℂ) :
    ‖test R τ P ((x : ℂ)+(y : ℂ)*Complex.I)‖ =
      ‖P.eval (((x-τ : ℝ) : ℂ)+(y : ℂ)*Complex.I)‖ *
        Real.exp (-R*(x-τ)^2+R*y^2) := by
  have hz : (x : ℂ)+(y : ℂ)*Complex.I-τ =
      ((x-τ : ℝ) : ℂ)+(y : ℂ)*Complex.I := by push_cast; ring
  simp only [test, hz, norm_mul, norm_gaussian]

/-- The requested degree-sharp strip estimate with an explicit coefficient constant. -/
theorem norm_test_le {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (τ x y : ℝ) (P : Polynomial ℂ) (hy : |y| ≤ b) :
    ‖test R τ P ((x : ℂ)+(y : ℂ)*Complex.I)‖ ≤
      P.stripGrowthConstant b * (1+|x-τ|)^P.natDegree *
        Real.exp (R*b^2) * Real.exp (-R*(x-τ)^2) := by
  rw [norm_test]
  have hs : y^2 ≤ b^2 := by nlinarith [sq_abs y, abs_nonneg y]
  have he : Real.exp (-R*(x-τ)^2+R*y^2) ≤
      Real.exp (R*b^2) * Real.exp (-R*(x-τ)^2) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    nlinarith [mul_le_mul_of_nonneg_left hs hR]
  calc
    _ ≤ (P.stripGrowthConstant b * (1+|x-τ|)^P.natDegree) *
        (Real.exp (R*b^2) * Real.exp (-R*(x-τ)^2)) :=
      mul_le_mul (P.norm_eval_le_stripGrowthConstant hb hy) he
        (Real.exp_nonneg _)
        (mul_nonneg (P.stripGrowthConstant_nonneg hb) (by positivity))
    _ = _ := by ring

/-- Absolute moments reuse the existing Gaussian Fourier integrability infrastructure. -/
theorem integrable_abs_pow_gaussian {R : ℝ} (hR : 0 < R) (k : ℕ) :
    Integrable (fun x : ℝ => |x|^k * Real.exp (-R*x^2)) := by
  have h := (integrable_momentFunction hR k).norm
  simpa [momentFunction, gaussian, norm_mul, norm_pow, Complex.norm_exp,
    Complex.norm_real, Real.norm_eq_abs, Complex.mul_re, pow_two] using h

theorem integrable_one_add_abs_pow_gaussian {R : ℝ} (hR : 0 < R) (M : ℕ) :
    Integrable (fun x : ℝ => (1+|x|)^M * Real.exp (-R*x^2)) := by
  have hsum : (fun x : ℝ => (1+|x|)^M * Real.exp (-R*x^2)) =
      fun x => ∑ k ∈ Finset.range (M+1),
        (M.choose k : ℝ) * (|x|^(M-k) * Real.exp (-R*x^2)) := by
    funext x
    rw [add_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [one_pow, one_mul]
    ring
  rw [hsum]
  exact integrable_finsetSum _ (fun k _ => (integrable_abs_pow_gaussian hR (M-k)).const_mul _)

/-- A common real, nonnegative majorant on a horizontal strip. -/
def majorant (R τ b : ℝ) (P : Polynomial ℂ) (x : ℝ) : ℝ :=
  P.stripGrowthConstant b * (1+|x-τ|)^P.natDegree *
    Real.exp (R*b^2) * Real.exp (-R*(x-τ)^2)

theorem integrable_majorant {R : ℝ} (hR : 0 < R)
    (τ b : ℝ) (P : Polynomial ℂ) :
    Integrable (majorant R τ b P) := by
  have h := ((integrable_one_add_abs_pow_gaussian hR P.natDegree).comp_sub_right τ).const_mul
    (P.stripGrowthConstant b * Real.exp (R*b^2))
  convert h using 1
  funext x
  dsimp [majorant]
  ring

theorem integrable_weighted_majorant {R : ℝ} (hR : 0 < R)
    (τ b : ℝ) (P : Polynomial ℂ) (N : ℕ) :
    Integrable (fun x => (1+|x-τ|)^N * majorant R τ b P x) := by
  have h := ((integrable_one_add_abs_pow_gaussian hR (N+P.natDegree)).comp_sub_right τ).const_mul
    (P.stripGrowthConstant b * Real.exp (R*b^2))
  convert h using 1
  funext x
  dsimp [majorant]
  rw [pow_add]
  ring

theorem integrable_horizontal {R : ℝ} (hR : 0 < R)
    (τ y : ℝ) (P : Polynomial ℂ) :
    Integrable (fun x : ℝ => test R τ P ((x : ℂ)+(y : ℂ)*Complex.I)) := by
  apply (integrable_majorant hR τ |y| P).mono'
  · exact ((differentiable_test R τ P).continuous.comp
      (by fun_prop : Continuous (fun x : ℝ => (x : ℂ)+(y : ℂ)*Complex.I))).aestronglyMeasurable
  · filter_upwards [] with x
    exact norm_test_le hR.le (abs_nonneg y) τ x y P le_rfl

/-- Exact completed square behind the exponential-tilt majorant. -/
theorem tilt_exponent_identity {R : ℝ} (hR : 0 < R) (b t : ℝ) :
    b*|t|-R*t^2 =
      b^2/(2*R) - (R/2)*t^2 - (R*|t|-b)^2/(2*R) := by
  field_simp
  nlinarith [sq_abs t]

theorem exp_tilt_gaussian_le {R : ℝ} (hR : 0 < R) (b t : ℝ) :
    Real.exp (b*|t|) * Real.exp (-R*t^2) ≤
      Real.exp (b^2/(2*R)) * Real.exp (-(R/2)*t^2) := by
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have hi := tilt_exponent_identity hR b t
  have hn : 0 ≤ (R*|t|-b)^2/(2*R) := by positivity
  linarith

theorem integrable_tilted_majorant {R : ℝ} (hR : 0 < R) (b : ℝ) (M : ℕ) :
    Integrable (fun u : ℝ => (1+|u|)^M * Real.exp (b*|u|) * Real.exp (-R*u^2)) := by
  apply ((integrable_one_add_abs_pow_gaussian (half_pos hR) M).const_mul
    (Real.exp (b^2/(2*R)))).mono'
  · exact (by fun_prop : Continuous
      (fun u : ℝ => (1+|u|)^M * Real.exp (b*|u|) * Real.exp (-R*u^2))).aestronglyMeasurable
  · filter_upwards [] with u
    rw [Real.norm_of_nonneg (by positivity)]
    calc
      _ = (1+|u|)^M * (Real.exp (b*|u|) * Real.exp (-R*u^2)) := by ring
      _ ≤ (1+|u|)^M * (Real.exp (b^2/(2*R)) * Real.exp (-(R/2)*u^2)) :=
        mul_le_mul_of_nonneg_left (exp_tilt_gaussian_le hR b u) (by positivity)
      _ = _ := by ring

/-- Uniform domination explicitly packaged for dominated-convergence applications. -/
theorem strip_domination {R b : ℝ} (hR : 0 < R) (hb : 0 ≤ b)
    (τ : ℝ) (P : Polynomial ℂ) :
    Integrable (majorant R τ b P) ∧
      ∀ x y : ℝ, |y| ≤ b →
        ‖test R τ P ((x : ℂ)+(y : ℂ)*Complex.I)‖ ≤ majorant R τ b P x :=
  ⟨integrable_majorant hR τ b P, fun x y hy => norm_test_le hR.le hb τ x y P hy⟩

/-- Exact norm of the inverse Fourier kernel for a complex argument. -/
theorem norm_inverse_phase (z : ℂ) (u : ℝ) :
    ‖Complex.exp (Complex.I*z*u)‖ = Real.exp (-z.im*u) := by
  simp [Complex.norm_exp, Complex.mul_re]

theorem norm_inverse_phase_le {b : ℝ} (z : ℂ) (u : ℝ) (hz : |z.im| ≤ b) :
    ‖Complex.exp (Complex.I*z*u)‖ ≤ Real.exp (b*|u|) := by
  rw [norm_inverse_phase, Real.exp_le_exp]
  calc
    -z.im*u ≤ |-z.im*u| := le_abs_self _
    _ = |z.im| * |u| := by rw [abs_mul, abs_neg]
    _ ≤ b*|u| := mul_le_mul_of_nonneg_right hz (abs_nonneg _)

/-- Common majorant for inverse kernels and all fixed frequency moments.
The caller must provide the Gaussian envelope for g; no inversion identity is asserted. -/
theorem norm_inverse_moment_le_of_bound {a b K : ℝ} (ha : 0 < a) (hK : 0 ≤ K)
    (M N : ℕ) (g : ℝ → ℂ)
    (hg : ∀ u, ‖g u‖ ≤ K * (1 + |u|) ^ M * Real.exp (-a * u ^ 2))
    (z : ℂ) (hz : |z.im| ≤ b) (u : ℝ) :
    ‖(u : ℂ)^N * (Complex.exp (Complex.I*z*u)*g u)‖ ≤
      K*Real.exp (b^2/(2*a)) * (1+|u|)^(M+N)*Real.exp (-(a/2)*u^2) := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_mul]
  have hu : |u|^N ≤ (1+|u|)^N :=
    pow_le_pow_left₀ (abs_nonneg u) (by linarith) N
  calc
    _ ≤ (1+|u|)^N * (Real.exp (b*|u|) *
          (K * (1 + |u|) ^ M * Real.exp (-a * u ^ 2))) :=
      mul_le_mul hu
        (mul_le_mul (norm_inverse_phase_le z u hz) (hg u) (norm_nonneg _) (by positivity))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
    _ = K*(1+|u|)^(M+N) *
        (Real.exp (b*|u|)*Real.exp (-a*u^2)) := by rw [pow_add]; ring
    _ ≤ K*(1+|u|)^(M+N) *
        (Real.exp (b^2/(2*a))*Real.exp (-(a/2)*u^2)) :=
      mul_le_mul_of_nonneg_left (exp_tilt_gaussian_le ha b u) (by positivity)
    _ = _ := by ring

theorem integrable_inverse_moment_of_bound {a b K : ℝ} (ha : 0 < a) (hK : 0 ≤ K)
    (M N : ℕ) {g : ℝ → ℂ} (hmeas : AEStronglyMeasurable g)
    (hg : ∀ u, ‖g u‖ ≤ K * (1 + |u|) ^ M * Real.exp (-a * u ^ 2))
    (z : ℂ) (hz : |z.im| ≤ b) :
    Integrable (fun u : ℝ => (u : ℂ)^N * (Complex.exp (Complex.I*z*u)*g u)) := by
  apply ((integrable_one_add_abs_pow_gaussian (half_pos ha) (M+N)).const_mul
    (K*Real.exp (b^2/(2*a)))).mono'
  · exact (by fun_prop : Continuous (fun u : ℝ => (u : ℂ)^N)).aestronglyMeasurable.mul
      ((by fun_prop : Continuous (fun u : ℝ =>
        Complex.exp (Complex.I*z*u))).aestronglyMeasurable.mul hmeas)
  · filter_upwards [] with u
    simpa only [mul_assoc] using norm_inverse_moment_le_of_bound ha hK M N g hg z hz u


theorem real_stripGrowthConstant (B : Polynomial ℝ) (b : ℝ) :
    (B.map Complex.ofRealHom).stripGrowthConstant b =
      ∑ k ∈ B.support, |B.coeff k| * (1+b)^k := by
  unfold Polynomial.stripGrowthConstant
  rw [Polynomial.support_map_of_injective B (f := Complex.ofRealHom) Complex.ofReal_injective]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Polynomial.coeff_map]
  change ‖(B.coeff k : ℂ)‖ * (1+b)^k = |B.coeff k| * (1+b)^k
  rw [Complex.norm_real, Real.norm_eq_abs]

/-- The original real-polynomial statement, with C written out and degree unchanged. -/
theorem norm_real_test_le {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (τ x y : ℝ) (B : Polynomial ℝ) (hy : |y| ≤ b) :
    ‖test R τ (B.map Complex.ofRealHom) ((x : ℂ)+(y : ℂ)*Complex.I)‖ ≤
      (∑ k ∈ B.support, |B.coeff k| * (1+b)^k) *
        (1+|x-τ|)^B.natDegree * Real.exp (R*b^2) * Real.exp (-R*(x-τ)^2) := by
  simpa only [real_stripGrowthConstant, Polynomial.natDegree_map] using
    norm_test_le hR hb τ x y (B.map Complex.ofRealHom) hy

end RiemannResearch.Analysis.GaussianPolynomialStrip
