/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Bilateral Laplace transform of the hyperbolic secant

The sigmoid substitution converts the complete real-line integral into Euler's
Beta integral. Euler reflection then evaluates it in the sharp convergence strip.
Sources for the Beta and reflection identities used in this proof:
https://dlmf.nist.gov/5.12.E1 and https://dlmf.nist.gov/5.5.E3.
The substitution is formalized here directly using Mathlib's Jacobian theorem.

Consumer: the positive complex-shifted sech smoothing kernel for Montgomery
pair correlation. This module proves an analytic transform; it makes no
zero-sampling or pair-correlation asymptotic assumption.
-/

noncomputable section
open MeasureTheory Set
namespace RiemannResearch.Analysis.SechLaplace

theorem sigmoid_two_eq (x : ℝ) :
    Real.sigmoid (2*x) = Real.exp x / (2*Real.cosh x) := by
  rw [Real.sigmoid_def, Real.cosh_eq, Real.exp_neg,
    show 2*x = x+x by ring, Real.exp_add, Real.exp_neg]
  have he := Real.exp_pos x
  field_simp

theorem log_sigmoid_two (x : ℝ) :
    Real.log (Real.sigmoid (2*x)) = x - Real.log (2*Real.cosh x) := by
  rw [sigmoid_two_eq, Real.log_div (Real.exp_ne_zero _) (by positivity), Real.log_exp]

theorem log_one_sub_sigmoid_two (x : ℝ) :
    Real.log (1 - Real.sigmoid (2*x)) = -x - Real.log (2*Real.cosh x) := by
  rw [← Real.sigmoid_neg, show -(2*x) = 2*(-x) by ring,
    log_sigmoid_two, Real.cosh_neg]

theorem beta_jacobian (s : ℂ) (x : ℝ) :
    ((2*Real.sigmoid (2*x)*(1-Real.sigmoid (2*x)) : ℝ) : ℂ) *
        ((Real.sigmoid (2*x) : ℂ)^(s-1) *
          (1-(Real.sigmoid (2*x) : ℂ))^(-s)) =
      Complex.exp ((2*s-1)*(x : ℂ)) / (Real.cosh x : ℂ) := by
  let t := Real.sigmoid (2*x)
  let q := 1 - t
  have ht : 0 < t := Real.sigmoid_pos _
  have hq : 0 < q := sub_pos.mpr (Real.sigmoid_lt_one _)
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  have hq0 : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hq)
  rw [show (1 : ℂ) - (Real.sigmoid (2*x) : ℂ) = (q : ℂ) by simp [q,t]]
  change ((2*t*q : ℝ) : ℂ) * ((t : ℂ)^(s-1) * (q : ℂ)^(-s)) = _
  rw [Complex.cpow_def_of_ne_zero ht0, Complex.cpow_def_of_ne_zero hq0,
    ← Complex.ofReal_log ht.le, ← Complex.ofReal_log hq.le]
  have et : Complex.exp (Real.log t : ℂ) = (t : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log ht]
  have eq : Complex.exp (Real.log q : ℂ) = (q : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hq]
  calc
    _ = 2 * Complex.exp ((Real.log t : ℂ) + Real.log q +
        (Real.log t : ℂ)*(s-1) + (Real.log q : ℂ)*(-s)) := by
      simp only [Complex.exp_add, et, eq]
      push_cast
      ring
    _ = 2 * Complex.exp ((2*s-1)*(x : ℂ) -
        (Real.log (2*Real.cosh x) : ℂ)) := by
      congr 2
      dsimp [t,q]
      rw [log_sigmoid_two, log_one_sub_sigmoid_two]
      push_cast
      ring
    _ = _ := by
      rw [Complex.exp_sub, ← Complex.ofReal_exp,
        Real.exp_log (by positivity : 0 < 2*Real.cosh x)]
      push_cast
      field_simp

theorem sigmoid_two_image :
    (fun x : ℝ => Real.sigmoid (2*x)) '' univ = Ioo 0 1 := by
  rw [image_univ]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Real.sigmoid_pos _, Real.sigmoid_lt_one _⟩
  · intro hy
    obtain ⟨x, hx⟩ := Real.range_sigmoid.symm ▸ hy
    exact ⟨x/2, by dsimp only; rw [show 2*(x/2) = x by ring]; exact hx⟩

theorem betaIntegral_eq_laplace (s : ℂ) :
    Complex.betaIntegral s (1-s) =
      ∫ x : ℝ, Complex.exp ((2*s-1)*(x : ℂ)) / (Real.cosh x : ℂ) := by
  have hd (x : ℝ) :
      HasDerivAt (fun x : ℝ => Real.sigmoid (2*x))
        (2*Real.sigmoid (2*x)*(1-Real.sigmoid (2*x))) x := by
    simpa only [Function.comp_def, id_eq, mul_one, one_mul, mul_assoc, mul_comm, mul_left_comm]
      using (Real.hasDerivAt_sigmoid (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  have hi : InjOn (fun x : ℝ => Real.sigmoid (2*x)) univ := by
    intro x hx y hy hxy
    have := Real.sigmoid_injective hxy
    linarith
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (hd x).hasDerivWithinAt) hi
    (fun t : ℝ => (t : ℂ)^(s-1) * (1-(t : ℂ))^((1-s)-1))
  rw [sigmoid_two_image, setIntegral_univ] at h
  rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num),
    integral_Ioc_eq_integral_Ioo]
  calc
    _ = _ := h
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      have ht := Real.sigmoid_pos (2*x)
      have hq := sub_pos.mpr (Real.sigmoid_lt_one (2*x))
      rw [abs_of_pos (by positivity : 0 < 2*Real.sigmoid (2*x)*(1-Real.sigmoid (2*x)))]
      simp only [Complex.real_smul, show (1-s)-1 = -s by ring]
      exact beta_jacobian s x

theorem integral_exp_div_cosh (z : ℂ) (hz : |z.re| < 1) :
    (∫ x : ℝ, Complex.exp (z*(x : ℂ)) / (Real.cosh x : ℂ)) =
      (Real.pi : ℂ) / Complex.cos ((Real.pi : ℂ)*z/2) := by
  let s : ℂ := (z+1)/2
  have hs : 0 < s.re := by
    dsimp [s]
    simp only [Complex.div_ofNat_re, Complex.add_re, Complex.one_re]
    linarith [(abs_lt.mp hz).1]
  have ht : 0 < (1-s).re := by
    simp only [Complex.sub_re, Complex.one_re]
    dsimp [s]
    simp only [Complex.div_ofNat_re, Complex.add_re, Complex.one_re]
    linarith [(abs_lt.mp hz).2]
  have he : 2*s-1 = z := by dsimp [s]; ring
  calc
    _ = Complex.betaIntegral s (1-s) := by
      rw [betaIntegral_eq_laplace, he]
    _ = _ := by
      rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ hs ht,
        Complex.Gamma_mul_Gamma_one_sub]
      simp only [add_sub_cancel, Complex.Gamma_one, div_one]
      congr 1
      have hsine : (Real.pi : ℂ)*s = Real.pi/2 + Real.pi*z/2 := by dsimp [s]; ring
      rw [hsine, Complex.sin_add]
      simp


theorem integrable_exp_div_cosh (z : ℂ) (hz : |z.re| < 1) :
    Integrable (fun x : ℝ => Complex.exp (z*(x : ℂ)) / (Real.cosh x : ℂ)) := by
  let s : ℂ := (z+1)/2
  have hs : 0 < s.re := by
    dsimp [s]
    simp only [Complex.div_ofNat_re, Complex.add_re, Complex.one_re]
    linarith [(abs_lt.mp hz).1]
  have ht : 0 < (1-s).re := by
    simp only [Complex.sub_re, Complex.one_re]
    dsimp [s]
    simp only [Complex.div_ofNat_re, Complex.add_re, Complex.one_re]
    linarith [(abs_lt.mp hz).2]
  have he : 2*s-1 = z := by dsimp [s]; ring
  have hd (x : ℝ) :
      HasDerivAt (fun x : ℝ => Real.sigmoid (2*x))
        (2*Real.sigmoid (2*x)*(1-Real.sigmoid (2*x))) x := by
    simpa only [Function.comp_def, id_eq, mul_one, one_mul, mul_assoc, mul_comm, mul_left_comm]
      using (Real.hasDerivAt_sigmoid (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  have hi : InjOn (fun x : ℝ => Real.sigmoid (2*x)) univ := by
    intro x hx y hy hxy
    have := Real.sigmoid_injective hxy
    linarith
  have hb : IntegrableOn (fun t : ℝ =>
      (t : ℂ)^(s-1) * (1-(t : ℂ))^((1-s)-1)) (Ioo 0 1) :=
    (Complex.betaIntegral_convergent hs ht).1.mono_set
      (by intro t ht; exact ⟨ht.1, ht.2.le⟩)
  have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (hd x).hasDerivWithinAt) hi
    (fun t : ℝ => (t : ℂ)^(s-1) * (1-(t : ℂ))^((1-s)-1))).mp
    (by rw [sigmoid_two_image]; exact hb)
  rw [integrableOn_univ] at h
  apply h.congr
  filter_upwards [] with x
  have ht := Real.sigmoid_pos (2*x)
  have hq := sub_pos.mpr (Real.sigmoid_lt_one (2*x))
  rw [abs_of_pos (by positivity : 0 < 2*Real.sigmoid (2*x)*(1-Real.sigmoid (2*x)))]
  simp only [Complex.real_smul, show (1-s)-1 = -s by ring]
  rw [beta_jacobian, he]

end RiemannResearch.Analysis.SechLaplace
