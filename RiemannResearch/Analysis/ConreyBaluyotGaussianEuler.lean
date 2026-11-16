/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotGaussianArithmetic
import RiemannResearch.Analysis.ConreyBaluyotGaussianMoment
import RiemannResearch.Analysis.ConreyBaluyotGaussianShift
import RiemannResearch.Analysis.ConreyBaluyotMollifiedBoundary
import RiemannResearch.Analysis.GaussianGammaTransform
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Exact Euler evaluation of the actual Gaussian arithmetic transform

Source for the arithmetic transform and the two-phase strategy:
S. A. C. Baluyot, *On the Zeros of Riemann's Zeta-function* (2017),
Lemma 3.1.7 and Section 3.3, pp. 104-105 and 116-117:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320

Using the proved product-space Fubini theorem in `GaussianGammaTransform`,
the actual `gaussianArithmeticTransform` is evaluated as two Euler integrals.
For `a = 1-2*l`, `s0 = l+I*u`, and `z_v = -log(2*pi)-log(omega)+I*v`,
the branch is

  exp(a*(-log(2*pi)+I*v)) * integral_{x>0}
    exp(-x) x^(a-1) exp(s0*(z_v+log x)-Delta^2*(z_v+log x)^2/4) dx.

The two phases are `v = pi/2` and `v = -pi/2`. Their sum times
`Delta*sqrt(pi)` equals the scalar transform for every `c > 2*l-1`,
with arbitrary real `l,u` and positive `Delta,omega`. There is no upper
restriction on `c`. Consequently the transform is independent of `c` in
that half-plane. The final actual-moment identity removes `c` entirely,
proves absolute convergence of the paired Euler series, and retains the
signed residue with coefficient `-2*sqrt(pi)/Delta`.

These are damped Euler integrals on the positive axis. Rotation to the
oscillatory/rational-phase Estermann representation still requires a proof;
the complete long-mollifier estimate and Ingham density provider are not
asserted here. The logarithms below are principal complex logarithms; their
arguments on the Euler axis and at positive frequency are positive real.
-/

noncomputable section
open Complex MeasureTheory Set
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- One exact Euler branch, with the phase and Gamma normalization explicit. -/
def gaussianArithmeticEulerBranch (l Δ u ω v : ℝ) : ℂ :=
  Complex.exp ((1 - ((2 * l : ℝ) : ℂ)) * (-Complex.log (2 * Real.pi : ℂ) + I * v)) *
    (∫ x : ℝ in Ioi 0,
      ((Real.exp (-x) : ℂ) * (x : ℂ) ^ ((1 - ((2 * l : ℝ) : ℂ)) - 1)) *
        Complex.exp (((l : ℂ) + I * u) *
          (-Complex.log (2 * Real.pi : ℂ) - Complex.log (ω : ℂ) + I * v +
            Complex.log (x : ℂ)) -
          (Δ : ℂ)^2 * (-Complex.log (2 * Real.pi : ℂ) - Complex.log (ω : ℂ) +
            I * v + Complex.log (x : ℂ))^2 / 4))

private theorem phase_factor (a s G : ℂ) (v : ℝ) {r ω : ℝ}
    (hr : 0 < r) (hω : 0 < ω) :
    G * (r : ℂ) ^ (-(a + s)) * Gamma (a + s) *
      Complex.exp (I * v * (a + s)) * (ω : ℂ) ^ (-s) =
    Complex.exp (a * (-Complex.log (r : ℂ) + I * v)) *
      (G * Gamma (a + s) *
        Complex.exp (s * (-Complex.log (r : ℂ) - Complex.log (ω : ℂ) + I * v))) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hω.ne')]
  calc
    _ = G * Gamma (a + s) * Complex.exp
        (Complex.log (r : ℂ) * (-(a + s)) + I * v * (a + s) +
          Complex.log (ω : ℂ) * (-s)) := by
      rw [Complex.exp_add, Complex.exp_add]
      ring
    _ = _ := by
      rw [show Complex.log (r : ℂ) * (-(a + s)) + I * v * (a + s) +
          Complex.log (ω : ℂ) * (-s) =
          a * (-Complex.log (r : ℂ) + I * v) +
            s * (-Complex.log (r : ℂ) - Complex.log (ω : ℂ) + I * v) by ring,
        Complex.exp_add]
      ring

private theorem arithmetic_phase_split (l Δ u : ℝ) (s : ℂ) {ω : ℝ}
    (hω : 0 < ω) :
    gaussianArithmeticKernel l Δ u s * (ω : ℂ) ^ (-s) =
      Complex.exp ((1 - ((2 * l : ℝ) : ℂ)) * (-Complex.log (2 * Real.pi : ℂ) + I * (Real.pi / 2:ℝ))) *
        (Complex.exp ((s - (l : ℂ) - I * u)^2 / (Δ : ℂ)^2) *
          Gamma (1 - ((2 * l : ℝ) : ℂ) + s) *
          Complex.exp (s * (-Complex.log (2 * Real.pi : ℂ) - Complex.log (ω : ℂ) + I * (Real.pi / 2:ℝ)))) +
      Complex.exp ((1 - ((2 * l : ℝ) : ℂ)) * (-Complex.log (2 * Real.pi : ℂ) + I * (-(Real.pi / 2):ℝ))) *
        (Complex.exp ((s - (l : ℂ) - I * u)^2 / (Δ : ℂ)^2) *
          Gamma (1 - ((2 * l : ℝ) : ℂ) + s) *
          Complex.exp (s * (-Complex.log (2 * Real.pi : ℂ) - Complex.log (ω : ℂ) + I * (-(Real.pi / 2):ℝ)))) := by
  let a : ℂ := 1 - ((2 * l : ℝ) : ℂ)
  let G := Complex.exp ((s - (l : ℂ) - I * u)^2 / (Δ : ℂ)^2)
  have hp : 0 < 2 * Real.pi := by positivity
  have he : Complex.exp (I * (Real.pi / 2:ℝ) * (a + s)) +
      Complex.exp (I * (-(Real.pi / 2):ℝ) * (a + s)) =
      2 * Complex.cos ((Real.pi : ℂ) * (a + s) / 2) := by
    rw [Complex.two_cos]
    congr 1 <;> congr 1 <;> push_cast <;> ring
  change G * (2 * (2 * Real.pi : ℂ) ^ (-(a + s)) * Gamma (a + s) * _) * _ = _
  calc
    _ = (G * (2 * Real.pi : ℂ) ^ (-(a + s)) * Gamma (a + s) *
          Complex.exp (I * (Real.pi / 2:ℝ) * (a + s)) * (ω : ℂ) ^ (-s)) +
        (G * (2 * Real.pi : ℂ) ^ (-(a + s)) * Gamma (a + s) *
          Complex.exp (I * (-(Real.pi / 2):ℝ) * (a + s)) * (ω : ℂ) ^ (-s)) := by
      rw [← add_mul, ← mul_add, he]
      ring
    _ = _ := by
      simpa only [a, G, Complex.ofReal_mul, Complex.ofReal_ofNat] using
        congrArg₂ (· + ·) (phase_factor a s G (Real.pi / 2) hp hω)
          (phase_factor a s G (-(Real.pi / 2)) hp hω)

/-- Evaluation of the actual scalar transform for every `c > 2*l-1`. -/
theorem gaussianArithmeticTransform_eq_euler (l u : ℝ) {c Δ ω : ℝ}
    (hc : 0 < 1 - 2 * l + c) (hΔ : 0 < Δ) (hω : 0 < ω) :
    gaussianArithmeticTransform l Δ u c ω =
      ((Δ * Real.sqrt Real.pi : ℝ) : ℂ) *
        (gaussianArithmeticEulerBranch l Δ u ω (Real.pi / 2) +
          gaussianArithmeticEulerBranch l Δ u ω (-(Real.pi / 2))) := by
  let a : ℂ := 1 - ((2 * l : ℝ) : ℂ)
  let z (v : ℝ) : ℂ := -Complex.log (2 * Real.pi : ℂ) - Complex.log (ω : ℂ) + I * v
  let G (t : ℝ) := Complex.exp ((((c : ℂ) + I * t) - (l : ℂ) - I * u)^2 / (Δ : ℂ)^2)
  have ha : 0 < a.re + c := by simpa [a] using hc
  have hi (v : ℝ) : Integrable (fun t : ℝ =>
      Complex.exp (a * (-Complex.log (2 * Real.pi : ℂ) + I * v)) *
        (G t * Gamma (a + ((c : ℂ) + I * t)) * Complex.exp (((c : ℂ) + I * t) * z v))) := by
    simpa [G, add_assoc] using
      (Complex.gaussian_gamma_vertical_laplace_integrable a (z v) c l u hΔ ha).const_mul
        (Complex.exp (a * (-Complex.log (2 * Real.pi : ℂ) + I * v)))
  unfold gaussianArithmeticTransform
  simp_rw [arithmetic_phase_split l Δ u _ hω]
  rw [integral_add (hi _) (hi _), integral_const_mul, integral_const_mul]
  have he (v : ℝ) := Complex.gaussian_gamma_vertical_laplace_integral a (z v) c l u hΔ ha
  simp only [add_assoc] at he
  rw [he (Real.pi / 2), he (-(Real.pi / 2))]
  dsimp [gaussianArithmeticEulerBranch, a, z]
  ring

/-- The exact Euler expression is independent of the scalar abscissa. -/
theorem gaussianArithmeticTransform_abscissa_independent (l u : ℝ) {c d Δ ω : ℝ}
    (hc : 0 < 1 - 2 * l + c) (hd : 0 < 1 - 2 * l + d)
    (hΔ : 0 < Δ) (hω : 0 < ω) :
    gaussianArithmeticTransform l Δ u c ω = gaussianArithmeticTransform l Δ u d ω := by
  rw [gaussianArithmeticTransform_eq_euler l u hc hΔ hω,
    gaussianArithmeticTransform_eq_euler l u hd hΔ hω]

/-- The normalized Euler value, with the natural-index zero convention. -/
def gaussianArithmeticEulerValue (l Δ u ω : ℝ) : ℂ :=
  if 0 < ω then
    gaussianArithmeticEulerBranch l Δ u ω (Real.pi / 2) +
      gaussianArithmeticEulerBranch l Δ u ω (-(Real.pi / 2))
  else 0

/-- Evaluation including zero frequency, with the existing natural-index convention. -/
theorem gaussianArithmeticTransform_eq_eulerValue (l u : ℝ) {c Δ ω : ℝ}
    (hc0 : 0 < c) (hc : 0 < 1 - 2 * l + c) (hΔ : 0 < Δ) (hω : 0 ≤ ω) :
    gaussianArithmeticTransform l Δ u c ω =
      ((Δ * Real.sqrt Real.pi : ℝ) : ℂ) * gaussianArithmeticEulerValue l Δ u ω := by
  rcases hω.eq_or_lt with hz | hp
  · subst ω
    have hs (t : ℝ) : -((c : ℂ) + I * t) ≠ 0 := by
      intro he
      have hr := congrArg Complex.re he
      simp at hr
      linarith
    simp only [gaussianArithmeticTransform, Complex.ofReal_zero,
      Complex.zero_cpow (hs _), mul_zero, integral_zero, gaussianArithmeticEulerValue,
      lt_self_iff_false, if_false]
  · simpa [gaussianArithmeticEulerValue, hp] using
      gaussianArithmeticTransform_eq_euler l u hc hΔ hp

/-- The exact paired Euler term with the original finite mollifier coefficients. -/
def mollifiedGaussianEulerTerm (σ y ε l Δ u : ℝ) (p : ℕ × ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ⌊y ^ (1 + ε)⌋₊,
  ∑ k ∈ Finset.Icc 1 ⌊y ^ (1 + ε)⌋₊,
    ((mollifierCoefficient σ y h * mollifierCoefficient σ y k) *
      (p.2 : ℂ) ^ (((2 * l : ℝ) : ℂ) - 1) / (k : ℂ) ^ ((2 * l : ℝ) : ℂ)) *
      gaussianArithmeticEulerValue l Δ u (((p.1 * p.2 * h : ℕ) : ℝ) / (k : ℝ))

/-- Every integrated arithmetic term equals its normalized paired Euler term. -/
theorem integral_mollifiedGaussianArithmeticTerm_eq_eulerTerm
    (σ y ε l u : ℝ) {c Δ : ℝ} (hc0 : 0 < c)
    (hc : 0 < 1 - 2 * l + c) (hΔ : 0 < Δ) (p : ℕ × ℕ) :
    (∫ t : ℝ, mollifiedGaussianArithmeticTerm σ y ε l Δ u ((c : ℂ) + I * t) p) =
      ((Δ * Real.sqrt Real.pi : ℝ) : ℂ) * mollifiedGaussianEulerTerm σ y ε l Δ u p := by
  rw [integral_mollifiedGaussianArithmeticTerm_eq_finite_sum σ y ε l u hc0 hc hΔ p.1 p.2]
  have he (h k : ℕ) := gaussianArithmeticTransform_eq_eulerValue l u hc0 hc hΔ
    (show 0 ≤ (((p.1 * p.2 * h : ℕ) : ℝ) / (k : ℝ)) by positivity)
  simp_rw [he]
  unfold mollifiedGaussianEulerTerm
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Absolute convergence for all fixed real parameters; no density or moment input. -/
theorem summable_norm_mollifiedGaussianEulerTerm (σ y ε l u : ℝ) {Δ : ℝ}
    (hΔ : 0 < Δ) :
    Summable (fun p : ℕ × ℕ => ‖mollifiedGaussianEulerTerm σ y ε l Δ u p‖) := by
  let c : ℝ := 2 * |l| + 2
  have hc1 : 1 < c := by dsimp [c]; linarith [abs_nonneg l]
  have hlc : 2 * l < c := by dsimp [c]; linarith [le_abs_self l]
  have hc0 : 0 < c := by linarith
  have hc : 0 < 1 - 2 * l + c := by linarith
  let C : ℂ := ((Δ * Real.sqrt Real.pi : ℝ) : ℂ)
  have hC : C ≠ 0 := by
    dsimp [C]
    exact_mod_cast (mul_ne_zero hΔ.ne' (Real.sqrt_pos.mpr Real.pi_pos).ne')
  have he (p : ℕ × ℕ) : mollifiedGaussianEulerTerm σ y ε l Δ u p =
      C⁻¹ * (∫ t : ℝ, mollifiedGaussianArithmeticTerm σ y ε l Δ u ((c : ℂ) + I * t) p) := by
    rw [integral_mollifiedGaussianArithmeticTerm_eq_eulerTerm σ y ε l u hc0 hc hΔ p]
    change _ = C⁻¹ * (C * _)
    rw [← mul_assoc, inv_mul_cancel₀ hC, one_mul]
  simp_rw [he, norm_mul]
  exact (summable_norm_integral_mollifiedGaussianArithmeticTerm σ y ε l Δ u hc1 hlc).mul_left _

/-- Exact contour-free Euler series for the actual moment, with its signed residue. -/
theorem mollifiedGaussianMoment_eq_euler_series (σ ε u : ℝ) {y l Δ : ℝ}
    (hy : 0 < y) (hl : 0 < l) (hl' : l < 1) (hΔ : 0 < Δ) :
    (mollifiedGaussianMoment σ y ε l Δ u : ℂ) =
      (∑' p : ℕ × ℕ, mollifiedGaussianEulerTerm σ y ε l Δ u p) -
        ((2 * Real.sqrt Real.pi / Δ : ℝ) : ℂ) * mollifiedGaussianPoleCoeff σ y ε l Δ u := by
  let c : ℝ := 2 * l + 2
  have hc1 : 1 < c := by dsimp [c]; linarith
  have hlc : 2 * l < c := by dsimp [c]; linarith
  have hc0 : 0 < c := by linarith
  have hc : 0 < 1 - 2 * l + c := by linarith
  have hS := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hC : Δ * Real.sqrt Real.pi ≠ 0 := mul_ne_zero hΔ.ne' hS
  have hcancel : ((1 / (Δ * Real.sqrt Real.pi) : ℝ) : ℂ) *
      ((Δ * Real.sqrt Real.pi : ℝ) : ℂ) = 1 := by
    exact_mod_cast (one_div_mul_cancel hC)
  have hres : (1 / (Δ * Real.sqrt Real.pi) : ℝ) * (2 * Real.pi) =
      2 * Real.sqrt Real.pi / Δ := by
    field_simp
    nlinarith [Real.sq_sqrt Real.pi_pos.le]
  have hresC : ((1 / (Δ * Real.sqrt Real.pi) : ℝ) : ℂ) * (2 * Real.pi : ℂ) =
      ((2 * Real.sqrt Real.pi / Δ : ℝ) : ℂ) := by exact_mod_cast hres
  rw [mollifiedGaussianMoment_eq_arithmetic_series σ ε u hy hl hl' hc1 hlc hΔ]
  simp_rw [integral_mollifiedGaussianArithmeticTerm_eq_eulerTerm σ y ε l u hc0 hc hΔ]
  rw [tsum_mul_left, mul_sub, ← mul_assoc, hcancel, one_mul, ← mul_assoc, hresC]

end RiemannResearch.Analysis.ConreyBaluyot
