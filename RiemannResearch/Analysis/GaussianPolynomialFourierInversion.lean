/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.GaussianFourierInversion
import RiemannResearch.Analysis.GaussianPolynomialFourierGrowth
import RiemannResearch.Analysis.GaussianPolynomialStrip
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Complex Gaussian-polynomial Fourier inversion

For R > 0 and the actual integral-defined transform g_B, the inverse integral
equals the entire extension of the real Gaussian-polynomial test for every z.
The first frequency-moment majorant on a neighborhood supplies the derivative
bound required by Mathlib's parameter-integral theorem. Real inversion and the
identity theorem complete the proof. The bilateral Laplace corollary records the
coordinate s used by the actual-zeta explicit formula.

Source for the requested statement and intended consumer:
[GaussianActualZetaExplicitFormula20261029.md, Sections 1--4]
(https://github.com/Cnoack3/RiemannResearch/blob/933fb43028951dd503c7ec2a14808f365bad7e72/RiemannResearch/RH/GaussianActualZetaExplicitFormula20261029.md).
Proof strategy: Mathlib's ParametricIntegral and Analytic.IsolatedZeros.
The previously checked GaussianPolynomialFourierGrowth supplies domination.
No zeta-zero, zero-counting, contour, arithmetic summation, or RH assertion is used.
-/

open MeasureTheory Filter
open scoped FourierTransform Topology
noncomputable section

namespace RiemannResearch.Analysis.GaussianPolynomialFourierInversion
open GaussianPolynomialFourier GaussianPolynomialFourierGrowth

/-- The absolutely convergent complex inverse integral of the actual transform. -/
def inverse (R τ : ℝ) (B : Polynomial ℝ) (z : ℂ) : ℂ :=
  ∫ u : ℝ, Complex.exp (Complex.I*z*u) * transform (test R τ B) u
/-- Differentiation under the integral, using the first frequency-moment majorant. -/
theorem hasDerivAt_inverse {R : ℝ} (hR : 0 < R) (τ : ℝ) (B : Polynomial ℝ) (z₀ : ℂ) :
    HasDerivAt (inverse R τ B)
      (∫ u : ℝ, Complex.I * ((u : ℂ) * (Complex.exp (Complex.I*z₀*u) *
        transform (test R τ B) u))) z₀ := by
  let F : ℂ → ℝ → ℂ := fun z u =>
    Complex.exp (Complex.I*z*u) * transform (test R τ B) u
  let F' : ℂ → ℝ → ℂ := fun z u => Complex.I * ((u : ℂ) * F z u)
  have hdiff (u : ℝ) (z : ℂ) : HasDerivAt (fun z => F z u) (F' z u) z := by
    simpa [F, F', mul_assoc, mul_comm, mul_left_comm] using
      ((((hasDerivAt_id z).const_mul Complex.I).mul_const (u : ℂ)).cexp.mul_const
        (transform (test R τ B) u))
  have hbound : ∀ᵐ u : ℝ, ∀ z ∈ Metric.ball z₀ 1,
      ‖F' z u‖ ≤ inverseMajorant R (|z₀.im|+1) B 1 u := by
    filter_upwards [] with u
    intro z hz
    have hnorm : ‖z-z₀‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
    have him : |z.im| ≤ |z₀.im|+1 := by
      have habs := abs_add_le (z-z₀).im z₀.im
      have hle := Complex.abs_im_le_norm (z-z₀)
      simp only [Complex.sub_im] at habs hle
      have hh : |z.im| ≤ |z.im-z₀.im|+|z₀.im| := by simpa using habs
      linarith
    simpa [F', F, norm_mul, Complex.norm_I, pow_one] using
      norm_inverse_transform_moment_le hR τ B 1 z him u
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F')
    (Metric.ball_mem_nhds z₀ (by norm_num : (0:ℝ)<1))
    (Filter.Eventually.of_forall fun z => by
      simpa only [F, pow_zero, one_mul] using
        (integrable_inverse_transform_moment hR τ B 0 z).aestronglyMeasurable)
    (by simpa [F] using integrable_inverse_transform_moment hR τ B 0 z₀)
    (by
      have h := (integrable_inverse_transform_moment hR τ B 1 z₀).const_mul Complex.I
      simpa [F', F] using h.aestronglyMeasurable)
    hbound (integrable_inverseMajorant hR (|z₀.im|+1) B 1)
    (Filter.Eventually.of_forall fun u z _ => hdiff u z)).2

/-- Real Fourier inversion for the actual Gaussian-polynomial transform. -/
theorem inverse_ofReal {R : ℝ} (hR : 0 < R) (τ x : ℝ) (B : Polynomial ℝ) :
    inverse R τ B (x : ℂ) = test R τ B x := by
  exact inverse_integral_eq (integrable_test hR τ B)
    (integrable_transform_test hR τ B) ((continuous_real_test R τ B).continuousAt)

/-- The inverse parameter integral is entire. -/
theorem differentiable_inverse {R : ℝ} (hR : 0 < R) (τ : ℝ) (B : Polynomial ℝ) :
    Differentiable ℂ (inverse R τ B) :=
  fun z => (hasDerivAt_inverse hR τ B z).differentiableAt

/-- Real inversion extends to every complex argument by the identity theorem. -/
theorem inverse_eq_test {R : ℝ} (hR : 0 < R) (τ : ℝ) (B : Polynomial ℝ) (z : ℂ) :
    inverse R τ B z = GaussianPolynomialStrip.test R τ (B.map Complex.ofRealHom) z := by
  have hf : AnalyticOnNhd ℂ (inverse R τ B) Set.univ :=
    fun w _ => (differentiable_inverse hR τ B).analyticAt w
  have hg : AnalyticOnNhd ℂ
      (GaussianPolynomialStrip.test R τ (B.map Complex.ofRealHom)) Set.univ :=
    fun w _ => (GaussianPolynomialStrip.differentiable_test R τ _).analyticAt w
  have ht : Tendsto (fun n : ℕ => ((1/((n : ℝ)+1) : ℝ) : ℂ))
      atTop (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [Complex.ofReal_zero, Function.comp_def] using
        Complex.continuous_ofReal.continuousAt.tendsto.comp
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · exact Eventually.of_forall fun n => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
        positivity
  have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ),
      inverse R τ B w = GaussianPolynomialStrip.test R τ (B.map Complex.ofRealHom) w := by
    apply ht.frequently
    apply Filter.Eventually.frequently
    exact Eventually.of_forall fun n => by
      rw [GaussianPolynomialStrip.test_ofReal, inverse_ofReal hR]
  exact (hf.eqOn_of_preconnected_of_frequently_eq hg isPreconnected_univ
    (Set.mem_univ (0:ℂ)) hfreq) (Set.mem_univ z)


/-- Complex Gaussian-polynomial inversion with the normalization requested by the zeta program. -/
theorem test_eq_inverse_integral {R : ℝ} (hR : 0 < R) (τ : ℝ) (B : Polynomial ℝ) (z : ℂ) :
    GaussianPolynomialStrip.test R τ (B.map Complex.ofRealHom) z =
      ∫ u : ℝ, Complex.exp (Complex.I*z*u) * transform (test R τ B) u :=
  (inverse_eq_test hR τ B z).symm

/-- The bilateral Laplace form at the zeta coordinate, for every complex s. -/
theorem test_eq_laplace_integral {R : ℝ} (hR : 0 < R)
    (τ : ℝ) (B : Polynomial ℝ) (s : ℂ) :
    GaussianPolynomialStrip.test R τ (B.map Complex.ofRealHom) ((s-1/2)/Complex.I) =
      ∫ u : ℝ, Complex.exp ((s-1/2)*u) * transform (test R τ B) u := by
  rw [test_eq_inverse_integral hR]
  apply integral_congr_ae
  filter_upwards [] with u
  congr 2
  field_simp

/-- Absolute integrability of that Laplace kernel, including both completed-zeta pole points. -/
theorem integrable_laplace_kernel {R : ℝ} (hR : 0 < R)
    (τ : ℝ) (B : Polynomial ℝ) (s : ℂ) :
    Integrable (fun u : ℝ => Complex.exp ((s-1/2)*u) * transform (test R τ B) u) := by
  have hphase : ∀ u : ℝ, Complex.I*((s-1/2)/Complex.I)*u = (s-1/2)*u := by
    intro u
    field_simp
  simpa only [pow_zero, one_mul, hphase] using
    integrable_inverse_transform_moment hR τ B 0 ((s-1/2)/Complex.I)

end RiemannResearch.Analysis.GaussianPolynomialFourierInversion
