/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import RiemannResearch.Analysis.ComplexLaplaceGamma

/-!
# Complex exponential Mellin inversion

The RH consumer is the initial Mellin formula in Baluyot, *On the Zeros of
Riemann's Zeta-function* (2017), equation (3.1.8) and the proof of Lemma 3.1.3,
pp. 96–97:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320
The reference supplies the identity. The proof here uses the complex Laplace–Gamma
integral, an exact two-step recurrence, and Mathlib's Mellin inversion theorem.

For every damping parameter with positive real part and every positive abscissa,
the kernel has an explicit integrable Cauchy majorant. No asymptotic Gamma estimate
or unresolved analytic provider is assumed. All complex powers are principal powers.
-/

noncomputable section
open Complex MeasureTheory Set Filter
open scoped Topology

namespace Complex

/-- The complex Laplace integral bounds the damped Gamma kernel. -/
theorem gamma_mul_cpow_neg_norm_le {lam s : ℂ} (hs : 0 < s.re) (hlam : 0 < lam.re) :
    ‖Gamma s * lam ^ (-s)‖ ≤ (1 / lam.re) ^ s.re * Real.Gamma s.re := by
  rw [mul_comm, ← integral_cpow_mul_exp_neg_complex hs hlam]
  calc
    _ ≤ ∫ x : ℝ in Ioi 0, ‖(x : ℂ) ^ (s - 1) * exp (-lam * x)‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ x : ℝ in Ioi 0, x ^ (s.re - 1) * Real.exp (-(lam.re * x)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx, norm_exp]
      simp [mul_re]
    _ = _ := Real.integral_rpow_mul_exp_neg_mul_Ioi hs hlam

/-- Exact recurrence of the complete damped kernel, retaining the complex power. -/
theorem gamma_mul_cpow_neg_add_two {lam s : ℂ} (hlam : lam ≠ 0)
    (hs : 0 < s.re) :
    lam ^ 2 * (Gamma (s + 2) * lam ^ (-(s + 2))) =
      (s + 1) * s * (Gamma s * lam ^ (-s)) := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hg : Gamma (s + 2) = (s + 1) * s * Gamma s := by
    calc
      _ = (s + 1) * Gamma (s + 1) := by
        convert Gamma_add_one (s + 1) hs1 using 1
        congr 1
        ring
      _ = _ := by rw [Gamma_add_one s hs0]; ring
  have hp : lam ^ 2 * lam ^ (-(s + 2)) = lam ^ (-s) := by
    rw [← cpow_natCast lam 2, ← cpow_add _ _ hlam]
    congr 1
    push_cast
    ring
  rw [hg]
  calc
    _ = (s + 1) * s * Gamma s * (lam ^ 2 * lam ^ (-(s + 2))) := by ring
    _ = _ := by rw [hp]; ring

/-- An explicit inverse-quadratic majorant for complex damping. -/
theorem gamma_mul_cpow_neg_vertical_bound {lam : ℂ} (hlam : 0 < lam.re)
    {c : ℝ} (hc : 0 < c)
    (t : ℝ) :
    ‖Gamma ((c : ℂ) + I * t) * lam ^ (-((c : ℂ) + I * t))‖ ≤
      (‖lam‖ ^ 2 * ((1 / lam.re) ^ (c + 2) * Real.Gamma (c + 2))) /
        (c ^ 2 + t ^ 2) := by
  let s : ℂ := (c : ℂ) + I * t
  have hs : 0 < s.re := by simpa [s] using hc
  have hlam0 : lam ≠ 0 := by intro h; simp [h] at hlam
  have he := congrArg norm (gamma_mul_cpow_neg_add_two (s := s) hlam0 hs)
  simp only [norm_mul, norm_pow] at he
  have hs2 : ‖s‖ ^ 2 = c ^ 2 + t ^ 2 := by
    rw [← normSq_eq_norm_sq, normSq_apply]
    simp [s, pow_two]
  have hs12 : ‖s + 1‖ ^ 2 = (c + 1) ^ 2 + t ^ 2 := by
    rw [← normSq_eq_norm_sq, normSq_apply]
    simp [s, pow_two]
  have hle : ‖s‖ ≤ ‖s + 1‖ := by
    nlinarith [norm_nonneg s, norm_nonneg (s + 1)]
  have hden : c ^ 2 + t ^ 2 ≤ ‖s + 1‖ * ‖s‖ := by
    nlinarith [mul_le_mul_of_nonneg_right hle (norm_nonneg s)]
  have hb := gamma_mul_cpow_neg_norm_le (s := s + 2) (by simp [s]; linarith) hlam
  have hb' : ‖Gamma (s + 2)‖ * ‖lam ^ (-(s + 2))‖ ≤
      (1 / lam.re) ^ (c + 2) * Real.Gamma (c + 2) := by
    simpa [s, norm_mul] using hb
  apply (le_div_iff₀ (by positivity : 0 < c ^ 2 + t ^ 2)).mpr
  change ‖Gamma s * lam ^ (-s)‖ * (c ^ 2 + t ^ 2) ≤ _
  calc
    _ ≤ ‖Gamma s * lam ^ (-s)‖ * (‖s + 1‖ * ‖s‖) :=
      mul_le_mul_of_nonneg_left hden (norm_nonneg _)
    _ = ‖lam‖ ^ 2 * (‖Gamma (s + 2)‖ * ‖lam ^ (-(s + 2))‖) := by
      rw [norm_mul]
      nlinarith [he]
    _ ≤ _ := mul_le_mul_of_nonneg_left hb' (sq_nonneg _)

/-- A common vertical majorant when the damping has bounded modulus and real part at least δ. -/
theorem gamma_mul_cpow_neg_vertical_bound_uniform {delta M c : ℝ}
    (hdelta : 0 < delta) (hc : 0 < c) {lam : ℂ}
    (hlam : delta ≤ lam.re) (hM : ‖lam‖ ≤ M)
    (t : ℝ) :
    ‖Gamma ((c : ℂ) + I * t) * lam ^ (-((c : ℂ) + I * t))‖ ≤
      (M ^ 2 * ((1 / delta) ^ (c + 2) * Real.Gamma (c + 2))) /
        (c ^ 2 + t ^ 2) := by
  have hlam0 : 0 < lam.re := hdelta.trans_le hlam
  refine (gamma_mul_cpow_neg_vertical_bound hlam0 hc t).trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul
  · nlinarith [norm_nonneg lam]
  · exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (by positivity) (one_div_le_one_div_of_le hdelta hlam)
        (by linarith)) (Real.Gamma_pos_of_pos (by linarith)).le
  · positivity
  · positivity

private theorem integrable_cauchy_scale {c : ℝ} (hc : 0 < c) (C : ℝ) :
    Integrable (fun t : ℝ => C / (c ^ 2 + t ^ 2)) := by
  have h := (integrable_inv_one_add_sq.comp_div hc.ne').const_mul (C / c ^ 2)
  convert h using 1
  funext t
  field_simp

/-- Absolute vertical integrability throughout the right damping half-plane. -/
theorem integrable_gamma_mul_cpow_neg {lam : ℂ} (hlam : 0 < lam.re)
    {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ => Gamma ((c : ℂ) + I * t) *
      lam ^ (-((c : ℂ) + I * t))) := by
  have hlam0 : lam ≠ 0 := by intro h; simp [h] at hlam
  have hg : Continuous (fun t : ℝ => Gamma ((c : ℂ) + I * t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (continuousAt_Gamma _ ?_).comp (by fun_prop)
    intro n hn
    have he := congrArg Complex.re hn
    simp at he
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hp : Continuous (fun t : ℝ => lam ^ (-((c : ℂ) + I * t))) := by
    simp only [cpow_def_of_ne_zero hlam0]
    fun_prop
  refine (integrable_cauchy_scale hc
    (‖lam‖ ^ 2 * ((1 / lam.re) ^ (c + 2) * Real.Gamma (c + 2)))).mono'
      (hg.mul hp).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (gamma_mul_cpow_neg_vertical_bound hlam hc)

/-- Complex exponential inversion with the exact real-line factor `1 / (2π)`. -/
theorem exponential_eq_mellin_integral {lam : ℂ} (hlam : 0 < lam.re)
    {c : ℝ} (hc : 0 < c)
    {x : ℝ} (hx : 0 < x) :
    exp (-lam * x) = (1 / (2 * (Real.pi : ℂ))) *
      ∫ t : ℝ, Gamma ((c : ℂ) + I * t) * lam ^ (-((c : ℂ) + I * t)) *
        (x : ℂ) ^ (-((c : ℂ) + I * t)) := by
  let f : ℝ → ℂ := fun x => exp (-lam * x)
  have hf : MellinConvergent f (c : ℂ) := by
    simpa [MellinConvergent, f, smul_eq_mul] using
      integrableOn_cpow_mul_exp_neg_complex (a := (c : ℂ)) (by simpa using hc) hlam
  have hF : VerticalIntegrable (mellin f) c := by
    refine (integrable_gamma_mul_cpow_neg hlam hc).congr ?_
    filter_upwards with t
    simp only [mellin, f, smul_eq_mul]
    rw [integral_cpow_mul_exp_neg_complex (by simpa using hc) hlam]
    simp only [mul_comm (t : ℂ) I, mul_comm]
  have h := mellinInv_mellin_eq c f hx hf hF (by dsimp [f]; fun_prop)
  calc
    _ = mellinInv c (mellin f) x := h.symm
    _ = _ := by
      simp only [mellinInv, smul_eq_mul, real_smul]
      push_cast
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      simp only [mellin, f, smul_eq_mul]
      rw [integral_cpow_mul_exp_neg_complex (by simpa using hc) hlam]
      simp only [mul_comm (t : ℂ) I]
      ring

end Complex
