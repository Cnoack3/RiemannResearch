import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
/-!
# Gaussian Fourier transforms and polynomial moments

The convention is `transform f u = (2*pi)^{-1} integral exp(-I*u*x) f(x) dx`.
For `R > 0`, `density R u` is the complexification of
`exp(-u^2/(4*R)) / sqrt(4*pi*R)`. Every polynomial moment is integrable,
and `moment_eq_iteratedDeriv` identifies its transform with `I^k D^k density`.
`transform_test` supplies the full shifted real-polynomial formula.

Source for the statements and normalization:
[GaussianActualZetaExplicitFormula20261029.md, Section 2]
(https://github.com/Cnoack3/RiemannResearch/blob/89c502e59dae3bb49b4dccfca9645b46b352c57f/RiemannResearch/RH/GaussianActualZetaExplicitFormula20261029.md).
The proofs reuse Mathlib's `integral_gaussian`, `fourierIntegral_gaussian`,
`integrable_rpow_mul_exp_neg_mul_sq`, and `Real.hasDerivAt_fourier`.

This module is independent of zeta, contour integration, infinite prime sums,
and zero sums. There are no domain-specific analytic hypotheses beyond `R > 0`.
The separate `GaussianFourierMatrix` module instantiates the finite matrix algebra.
-/

open MeasureTheory
open scoped Real FourierTransform BigOperators
noncomputable section
namespace RiemannResearch.Analysis.GaussianPolynomialFourier
def transform (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ * ∫ x : ℝ, Complex.exp (-Complex.I * u * x) * f x

def gaussian (R x : ℝ) : ℂ := Complex.exp (-(R : ℂ) * (x : ℂ)^2)
def momentFunction (R : ℝ) (k : ℕ) (x : ℝ) : ℂ :=
  (x : ℂ)^k * gaussian R x
def moment (R : ℝ) (k : ℕ) (u : ℝ) : ℂ := transform (momentFunction R k) u
def density (R u : ℝ) : ℂ :=
  Complex.exp (-(u : ℂ)^2 / (4 * R)) / (Real.sqrt (4 * Real.pi * R) : ℂ)

theorem integrable_momentFunction {R : ℝ} (hR : 0 < R) (k : ℕ) :
    Integrable (momentFunction R k) := by
  have h : Integrable (fun x : ℝ => x^k * Real.exp (-R * x^2)) := by
    simpa only [Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq hR (show (-1 : ℝ) < (k : ℝ) by
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith))
  have hc : Integrable (fun x : ℝ => ((x^k * Real.exp (-R * x^2) : ℝ) : ℂ)) := h.ofReal
  change Integrable (fun x : ℝ => (x : ℂ)^k * Complex.exp (-(R : ℂ) * (x : ℂ)^2))
  simpa [neg_mul] using hc

theorem transform_eq_fourier (f : ℝ → ℂ) (u : ℝ) :
    transform f u = (2 * Real.pi : ℂ)⁻¹ * 𝓕 f (u / (2 * Real.pi)) := by
  rw [transform, Real.fourier_real_eq_integral_exp_smul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [smul_eq_mul]
  congr 2
  push_cast
  field_simp

theorem gaussian_prefactor {R : ℝ} (hR : 0 < R) :
    (Real.pi / (R : ℂ)) ^ (1 / 2 : ℂ) = (Real.sqrt (Real.pi / R) : ℂ) := by
  rw [← integral_gaussian_complex (show 0 < (R : ℂ).re from hR)]
  rw [← integral_gaussian R]
  have hi : (∫ x : ℝ, (Real.exp (-R*x^2) : ℂ)) =
      ((∫ x : ℝ, Real.exp (-R*x^2) : ℝ) : ℂ) := integral_ofReal
  simpa [neg_mul] using hi

theorem real_normalization {R : ℝ} (hR : 0 < R) :
    Real.sqrt (Real.pi / R) / (2 * Real.pi) =
      1 / Real.sqrt (4 * Real.pi * R) := by
  rw [Real.sqrt_div Real.pi_pos.le,
    Real.sqrt_mul (show 0 ≤ 4 * Real.pi by positivity),
    Real.sqrt_mul (show (0:ℝ) ≤ 4 by positivity)]
  have h4 : Real.sqrt (4:ℝ) = 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 4 by norm_num), Real.sqrt_nonneg (4:ℝ)]
  rw [h4]
  have hp : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
  have hr : Real.sqrt R ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hR)
  field_simp
  nlinarith [Real.sq_sqrt Real.pi_pos.le]

theorem moment_zero {R : ℝ} (hR : 0 < R) (u : ℝ) :
    moment R 0 u = density R u := by
  simp only [moment, momentFunction, pow_zero, one_mul, transform, gaussian]
  have hx := fourierIntegral_gaussian (show 0 < (R : ℂ).re from hR) (-(u : ℂ))
  simp only [mul_neg, neg_mul, neg_sq] at hx ⊢
  rw [hx, gaussian_prefactor hR]
  have hn := congrArg (fun x : ℝ => (x : ℂ)) (real_normalization hR)
  push_cast at hn
  dsimp [density]
  rw [← mul_assoc, mul_comm ((2 * Real.pi : ℂ)⁻¹), ← div_eq_mul_inv, hn]
  ring

theorem hasDerivAt_density {R : ℝ} (hR : 0 < R) (u : ℝ) :
    HasDerivAt (density R) (-(u : ℂ) / (2 * R) * density R u) u := by
  have hr : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  convert! ((((hasDerivAt_id (u : ℂ)).pow 2).neg.div_const (4 * (R : ℂ))).cexp.div_const
    (Real.sqrt (4 * Real.pi * R) : ℂ)).comp_ofReal using 1
  dsimp [density]
  field_simp
  ring

theorem hasDerivAt_transform {f : ℝ → ℂ} (hf : Integrable f)
    (hfx : Integrable (fun x : ℝ => (x : ℂ) * f x)) (u : ℝ) :
    HasDerivAt (transform f) (-Complex.I * transform (fun x : ℝ => (x : ℂ) * f x) u) u := by
  have hfx' : Integrable (fun x : ℝ => x • f x) := by
    simpa only [Complex.real_smul] using hfx
  have hs : (𝓕 (fun x : ℝ => (-2 * Real.pi * Complex.I * x) • f x))
        (u / (2 * Real.pi)) =
      (-2 * (Real.pi : ℂ) * Complex.I) *
        (𝓕 (fun x : ℝ => (x : ℂ) * f x)) (u / (2 * Real.pi)) := by
    simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  have h := ((Real.hasDerivAt_fourier hf hfx' (u / (2 * Real.pi))).scomp u
      ((hasDerivAt_id u).div_const (2 * Real.pi))).const_mul
        ((2 * (Real.pi : ℂ))⁻¹)
  have heq : transform f = fun v => (2 * Real.pi : ℂ)⁻¹ * 𝓕 f (v / (2 * Real.pi)) :=
    funext (transform_eq_fourier f)
  rw [heq]
  convert! h using 1
  simp only [transform_eq_fourier, hs, Complex.real_smul, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_one]
  field_simp

theorem hasDerivAt_moment {R : ℝ} (hR : 0 < R) (k : ℕ) (u : ℝ) :
    HasDerivAt (moment R k) (-Complex.I * moment R (k+1) u) u := by
  have heq : (fun x : ℝ => (x : ℂ) * momentFunction R k x) = momentFunction R (k+1) := by
    funext x
    dsimp [momentFunction]
    rw [pow_succ]
    ring
  change HasDerivAt (transform (momentFunction R k))
    (-Complex.I * transform (momentFunction R (k+1)) u) u
  simpa only [heq] using
    (hasDerivAt_transform (integrable_momentFunction hR k)
      (heq.symm ▸ integrable_momentFunction hR (k+1)) u)

theorem iteratedDeriv_density {R : ℝ} (hR : 0 < R) (k : ℕ) :
    iteratedDeriv k (density R) = fun u => (-Complex.I)^k * moment R k u := by
  have hzero : density R = moment R 0 := (funext (moment_zero hR)).symm
  rw [hzero]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext u
    calc
      deriv (fun v => (-Complex.I)^k * moment R k v) u =
          (-Complex.I)^k * (-Complex.I * moment R (k+1) u) :=
        ((hasDerivAt_moment hR k u).const_mul ((-Complex.I)^k)).deriv
      _ = (-Complex.I)^(k+1) * moment R (k+1) u := by rw [pow_succ]; ring

theorem moment_eq_iteratedDeriv {R : ℝ} (hR : 0 < R) (k : ℕ) (u : ℝ) :
    moment R k u = Complex.I^k * iteratedDeriv k (density R) u := by
  rw [iteratedDeriv_density hR, ← mul_assoc, ← mul_pow]
  simp

theorem moment_one {R : ℝ} (hR : 0 < R) (u : ℝ) :
    moment R 1 u = (-Complex.I * u / (2 * R)) * density R u := by
  rw [moment_eq_iteratedDeriv hR, iteratedDeriv_one, (hasDerivAt_density hR u).deriv]
  ring

theorem moment_two {R : ℝ} (hR : 0 < R) (u : ℝ) :
    moment R 2 u = (1 / (2 * (R : ℂ)) - (u : ℂ)^2 / (4 * (R : ℂ)^2)) * density R u := by
  have hr : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hone : moment R 1 = fun v => (-Complex.I * v / (2 * R)) * density R v :=
    funext (moment_one hR)
  have hp : HasDerivAt (fun v : ℝ => -Complex.I * v / (2 * (R : ℂ)))
      (-Complex.I / (2 * R)) u := by
    convert! (((hasDerivAt_id (u : ℂ)).const_mul
      (-Complex.I)).div_const (2 * R)).comp_ofReal using 1
    simp
  have hh := hp.mul (hasDerivAt_density hR u)
  have hd := (hasDerivAt_moment hR 1 u).deriv
  rw [hone] at hd
  have hhd : deriv (fun v => (-Complex.I * v / (2 * R)) * density R v) u =
      (-Complex.I / (2 * R)) * density R u +
      (-Complex.I * u / (2 * R)) * (-(u : ℂ) / (2 * R) * density R u) := hh.deriv
  rw [hhd] at hd
  have hm := congrArg (fun z : ℂ => Complex.I * z) hd
  simp only [mul_add, ← mul_assoc, Complex.I_mul_I, mul_neg, neg_neg, one_mul] at hm
  calc
    moment R 2 u = Complex.I * ((-Complex.I / (2 * R)) * density R u +
      (-Complex.I * u / (2 * R)) * (-(u : ℂ) / (2 * R) * density R u)) := by
        simpa only [mul_add, ← mul_assoc, Complex.I_mul_I, mul_neg, neg_neg, one_mul] using hm.symm
    _ = _ := by
      field_simp
      simp only [Complex.I_sq]
      ring

theorem density_eq_real (R u : ℝ) :
    density R u = (Real.exp (-u^2 / (4*R)) / Real.sqrt (4*Real.pi*R) : ℝ) := by
  simp [density, neg_div]

theorem gaussian_integral {R : ℝ} (hR : 0 < R) :
    (∫ x : ℝ, gaussian R x) = (Real.sqrt (Real.pi / R) : ℂ) := by
  exact (integral_gaussian_complex (show 0 < (R : ℂ).re from hR)).trans
    (gaussian_prefactor hR)

theorem norm_phase (u x : ℝ) :
    ‖Complex.exp (-Complex.I * u * x)‖ = 1 := by
  simp [Complex.norm_exp]

theorem integrable_transformIntegrand {f : ℝ → ℂ} (hf : Integrable f) (u : ℝ) :
    Integrable (fun x : ℝ => Complex.exp (-Complex.I * u * x) * f x) := by
  apply hf.norm.mono'
  · exact (by fun_prop :
      Continuous (fun x : ℝ => Complex.exp (-Complex.I*u*x))).aestronglyMeasurable.mul
        hf.aestronglyMeasurable
  · filter_upwards [] with x
    simp only [norm_mul, norm_phase, one_mul, le_refl]

theorem transform_const_mul (c : ℂ) (f : ℝ → ℂ) (u : ℝ) :
    transform (fun x => c * f x) u = c * transform f u := by
  unfold transform
  simp_rw [mul_left_comm (Complex.exp _)]
  rw [integral_const_mul]
  ring

theorem transform_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ j ∈ s, Integrable (f j)) (u : ℝ) :
    transform (fun x => ∑ j ∈ s, f j x) u = ∑ j ∈ s, transform (f j) u := by
  unfold transform
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum s (fun j hj => integrable_transformIntegrand (hf j hj) u),
    Finset.mul_sum]

theorem transform_sub (f : ℝ → ℂ) (τ u : ℝ) :
    transform (fun t => f (t-τ)) u =
      Complex.exp (-Complex.I * τ * u) * transform f u := by
  unfold transform
  rw [← integral_add_right_eq_self (fun t : ℝ =>
    Complex.exp (-Complex.I * u * t) * f (t - τ)) τ]
  simp only [add_sub_cancel_right]
  have he (x : ℝ) : Complex.exp (-Complex.I * u * ((x+τ : ℝ) : ℂ)) =
      Complex.exp (-Complex.I * τ * u) * Complex.exp (-Complex.I * u * x) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [he, mul_assoc]
  rw [integral_const_mul]
  ring

def polynomialFunction (R : ℝ) (B : Polynomial ℝ) (x : ℝ) : ℂ :=
  ((B.eval x : ℝ) : ℂ) * gaussian R x

theorem polynomialFunction_eq_sum (R : ℝ) (B : Polynomial ℝ) (x : ℝ) :
    polynomialFunction R B x =
      ∑ k ∈ B.support, (B.coeff k : ℂ) * momentFunction R k x := by
  simp only [polynomialFunction, Polynomial.eval_eq_sum, Polynomial.sum,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow, Finset.sum_mul,
    momentFunction, mul_assoc]

theorem integrable_polynomialFunction {R : ℝ} (hR : 0 < R) (B : Polynomial ℝ) :
    Integrable (polynomialFunction R B) := by
  have he := funext (polynomialFunction_eq_sum R B)
  rw [he]
  exact integrable_finsetSum B.support (fun k _ => (integrable_momentFunction hR k).const_mul _)

theorem transform_polynomial {R : ℝ} (hR : 0 < R) (B : Polynomial ℝ) (u : ℝ) :
    transform (polynomialFunction R B) u =
      ∑ k ∈ B.support, (B.coeff k : ℂ) * (Complex.I^k * iteratedDeriv k (density R) u) := by
  rw [funext (polynomialFunction_eq_sum R B),
    transform_sum B.support _ (fun k _ => (integrable_momentFunction hR k).const_mul _)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [transform_const_mul]
  exact congrArg ((B.coeff k : ℂ) * ·) (moment_eq_iteratedDeriv hR k u)

/-- The shifted test used in the Gaussian explicit-formula memorandum. -/
def test (R τ : ℝ) (B : Polynomial ℝ) (t : ℝ) : ℂ :=
  polynomialFunction R B (t-τ)

theorem integrable_test {R : ℝ} (hR : 0 < R) (τ : ℝ) (B : Polynomial ℝ) :
    Integrable (test R τ B) :=
  (integrable_polynomialFunction hR B).comp_sub_right τ

theorem transform_test {R : ℝ} (hR : 0 < R) (τ : ℝ)
    (B : Polynomial ℝ) (u : ℝ) :
    transform (test R τ B) u = Complex.exp (-Complex.I * τ * u) *
      ∑ k ∈ B.support, (B.coeff k : ℂ) * (Complex.I^k * iteratedDeriv k (density R) u) := by
  change transform (fun t => polynomialFunction R B (t-τ)) u = _
  rw [transform_sub, transform_polynomial hR]

theorem transform_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (u : ℝ) :
    transform (fun x => f x + g x) u = transform f u + transform g u := by
  unfold transform
  simp_rw [mul_add]
  rw [integral_add (integrable_transformIntegrand hf u) (integrable_transformIntegrand hg u),
    mul_add]

/-- The actual Gaussian Fourier integral as a real linear map on polynomials. -/
def polynomialTransform (R : ℝ) (hR : 0 < R) (τ u : ℝ) :
    Polynomial ℝ →ₗ[ℝ] ℂ where
  toFun B := transform (test R τ B) u
  map_add' B C := by
    have ht : test R τ (B+C) = fun t => test R τ B t + test R τ C t := by
      funext t
      simp [test, polynomialFunction, add_mul]
    change transform (test R τ (B+C)) u = _
    rw [ht, transform_add (integrable_test hR τ B) (integrable_test hR τ C)]
  map_smul' r B := by
    have ht : test R τ (r • B) = fun t => (r : ℂ) * test R τ B t := by
      funext t
      simp [test, polynomialFunction, Polynomial.eval_smul, mul_assoc]
    change transform (test R τ (r • B)) u = r • transform (test R τ B) u
    rw [ht, transform_const_mul]
    simp [Complex.real_smul]

theorem polynomialTransform_X_pow {R : ℝ} (hR : 0 < R) (τ u : ℝ) (k : ℕ) :
    polynomialTransform R hR τ u ((Polynomial.X : Polynomial ℝ)^k) =
      Complex.exp (-Complex.I * τ * u) *
        (Complex.I^k * iteratedDeriv k (density R) u) := by
  have ht : test R τ ((Polynomial.X : Polynomial ℝ)^k) =
      fun t => momentFunction R k (t-τ) := by
    funext t
    simp [test, polynomialFunction, momentFunction]
  change transform (test R τ ((Polynomial.X : Polynomial ℝ)^k)) u = _
  rw [ht, transform_sub]
  exact congrArg (Complex.exp (-Complex.I * τ * u) * ·)
    (moment_eq_iteratedDeriv hR k u)

end RiemannResearch.Analysis.GaussianPolynomialFourier
