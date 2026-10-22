/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.WeilExplicitFormula.GammaFacts.StirlingVert
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact logarithm integrals and oscillatory bounds

Support for the fixed-c=2 actual Landau left side.
The generic lemmas retain their exact finite integral and endpoint identities.
Only ordinary sign and nonzero hypotheses occur.
The digamma comparison uses the already proved actual StirlingVert provider;
the finite FTC and integration-by-parts formulas below retain their endpoints.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Complex Set MeasureTheory

namespace Complex

theorem hasDerivAt_log_real_add_of_im_ne_zero {w : ℂ} (hw : w.im ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.log ((y : ℂ) + w)) (((x : ℂ) + w)⁻¹) x := by
  have hs : (x : ℂ) + w ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inr (by simpa using hw))
  have h := (Complex.hasDerivAt_log hs).comp (x : ℂ)
    ((hasDerivAt_id (x : ℂ)).add_const w)
  have h' : HasDerivAt (fun z : ℂ => Complex.log (z + w)) (((x : ℂ) + w)⁻¹) (x : ℂ) := by
    simpa only [Function.comp_def, id_eq, mul_one] using h
  exact h'.comp_ofReal

/-- Exact finite horizontal complex-log difference, valid on either half-plane. -/
theorem integral_inv_real_add_of_im_ne_zero {w : ℂ} (hw : w.im ≠ 0) (a b : ℝ) :
    (∫ x in a..b, ((x : ℂ) + w)⁻¹) =
      Complex.log ((b : ℂ) + w) - Complex.log ((a : ℂ) + w) := by
  have hc : Continuous (fun x : ℝ => ((x : ℂ) + w)⁻¹) := by
    apply Continuous.inv₀ (by fun_prop)
    intro x hx
    apply hw
    have h := congrArg Complex.im hx
    simpa using h
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_log_real_add_of_im_ne_zero hw x) (hc.intervalIntegrable _ _)

/-- The log shift is bounded by its exact inverse integral. -/
theorem norm_log_real_add_sub_le_of_im_ne_zero {w : ℂ} (hw : w.im ≠ 0)
    (a : ℝ) (ha : 0 ≤ a) :
    ‖Complex.log ((a : ℂ) + w) - Complex.log w‖ ≤ a / |w.im| := by
  have he := integral_inv_real_add_of_im_ne_zero hw 0 a
  simp only [Complex.ofReal_zero, zero_add] at he
  rw [← he]
  calc
    _ ≤ (1 / |w.im|) * |a - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [norm_inv, inv_eq_one_div]
      apply one_div_le_one_div_of_le (abs_pos.mpr hw)
      have h := Complex.abs_im_le_norm ((x : ℂ) + w)
      simpa using h
    _ = _ := by rw [sub_zero, abs_of_nonneg ha]; ring

/-- Digamma compared with the imaginary-axis logarithm, using the established
complete complex Stirling remainder and the exact horizontal log shift. -/
theorem norm_digamma_sub_log_axis_le (a t : ℝ) (ha : 0 < a) (ht : 1 / 2 ≤ |t|) :
    ‖Complex.digamma ((a : ℂ) + t * I) - Complex.log ((t : ℂ) * I)‖ ≤
      a / |t| + 1 / (2 * |t|) + 3 / t ^ 2 := by
  let w : ℂ := (a : ℂ) + t * I
  have ht0 : t ≠ 0 := by intro h; rw [h] at ht; norm_num at ht
  have hw : 0 < w.re := by simpa only [w, add_re, ofReal_re, mul_re,
    ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero] using ha
  have hst := Zeta23.StirlingVert.digamma_stirling hw
    (by simpa only [w, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
      mul_one, mul_zero, add_zero, zero_add] using ht)
  have hlog := norm_log_real_add_sub_le_of_im_ne_zero
    (w := (t : ℂ) * I) (by simpa using ht0) a ha.le
  have hinv : ‖(1 / 2 : ℂ) / w‖ ≤ 1 / (2 * |t|) := by
    rw [norm_div, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num]
    have htpos : 0 < |t| := abs_pos.mpr ht0
    have hn : |t| ≤ ‖w‖ := by
      have h := Complex.abs_im_le_norm w
      simpa [w] using h
    calc
      _ ≤ (1 / 2 : ℝ) / |t| :=
        div_le_div_of_nonneg_left (by norm_num) htpos hn
      _ = _ := by ring
  have he : Complex.digamma w - Complex.log ((t : ℂ) * I) =
      (Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w) +
      (Complex.log w - Complex.log ((t : ℂ) * I)) - (1 / 2 : ℂ) / w := by ring
  change ‖Complex.digamma w - Complex.log ((t : ℂ) * I)‖ ≤ _
  rw [he]
  have h1 := norm_sub_le
    ((Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w) +
      (Complex.log w - Complex.log ((t : ℂ) * I))) ((1 / 2 : ℂ) / w)
  have h2 := norm_add_le (Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w)
    (Complex.log w - Complex.log ((t : ℂ) * I))
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero] at hlog
  change ‖Complex.log w - Complex.log ((t : ℂ) * I)‖ ≤ a / |t| at hlog
  simp only [w, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
    mul_one, mul_zero, add_zero, zero_add] at hst
  linarith only [h1, h2, hst, hlog, hinv]

theorem log_imaginary_axis_pair (t : ℝ) (ht : 0 < t) :
    Complex.log ((t : ℂ) * I) + Complex.log ((t : ℂ) * (-I)) =
      (2 : ℂ) * (Real.log t : ℂ) := by
  rw [Complex.log_ofReal_mul ht Complex.I_ne_zero,
    Complex.log_ofReal_mul ht (neg_ne_zero.mpr Complex.I_ne_zero),
    Complex.log_I, Complex.log_neg_I]
  ring

/-- Exact integration by parts for the log model, with both endpoints and the
entire inverse-weight remainder retained. -/
theorem integral_exp_mul_log_sub_eq (A B u q : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hu : u ≠ 0) :
    (∫ t in A..B, Complex.exp (((u : ℂ) * I) * (t : ℂ)) *
      ((Real.log t - Real.log q : ℝ) : ℂ)) =
      (Complex.exp (((u : ℂ) * I) * (B : ℂ)) *
          ((Real.log B - Real.log q : ℝ) : ℂ) -
        Complex.exp (((u : ℂ) * I) * (A : ℂ)) *
          ((Real.log A - Real.log q : ℝ) : ℂ) -
        ∫ t in A..B, Complex.exp (((u : ℂ) * I) * (t : ℂ)) / (t : ℂ)) /
        ((u : ℂ) * I) := by
  let c : ℂ := (u : ℂ) * I
  let P : ℝ → ℂ := fun t => Complex.exp (c * (t : ℂ))
  let G : ℝ → ℂ := fun t => ((Real.log t - Real.log q : ℝ) : ℂ)
  have hc : c ≠ 0 := mul_ne_zero (by exact_mod_cast hu) Complex.I_ne_zero
  have hpos : ∀ t ∈ Set.uIcc A B, 0 < t := fun t ht =>
    lt_of_lt_of_le (lt_min hA hB) ht.1
  have hdP : ∀ t : ℝ, HasDerivAt P (c * P t) t := by
    intro t
    have h := ((hasDerivAt_id' t).ofReal_comp.const_mul c).cexp
    simpa only [P, Complex.ofReal_one, mul_one, mul_comm] using h
  have hdG : ∀ t ∈ Set.uIcc A B, HasDerivAt G ((t : ℂ)⁻¹) t := by
    intro t ht
    have h := ((Real.hasDerivAt_log (hpos t ht).ne').sub_const (Real.log q)).ofReal_comp
    simpa only [G, one_div, Complex.ofReal_inv] using h
  have hPG : ContinuousOn (fun t => c * P t * G t) (Set.uIcc A B) := by
    apply ContinuousOn.mul (by dsimp [P]; fun_prop)
    intro t ht
    exact (hdG t ht).continuousAt.continuousWithinAt
  have hPI : ContinuousOn (fun t => P t / (t : ℂ)) (Set.uIcc A B) := by
    apply ContinuousOn.div (by dsimp [P]; fun_prop) (by fun_prop)
    intro t ht
    exact Complex.ofReal_ne_zero.mpr (hpos t ht).ne'
  have hid := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t => P t * G t) (f' := fun t => c * P t * G t + P t / (t : ℂ))
    (fun t ht => by
      have h := (hdP t).mul (hdG t ht)
      simpa only [div_eq_mul_inv] using! h)
    (hPG.intervalIntegrable.add hPI.intervalIntegrable)
  rw [intervalIntegral.integral_add hPG.intervalIntegrable hPI.intervalIntegrable,
    show (fun t => c * P t * G t) = (fun t => c * (P t * G t)) by
      funext t; ring, intervalIntegral.integral_const_mul] at hid
  change (∫ t in A..B, P t * G t) =
    (P B * G B - P A * G A - ∫ t in A..B, P t / (t : ℂ)) / c
  apply (eq_div_iff hc).2
  linear_combination hid

/-- Quantitative oscillation of the real log model. The bound is uniform in q
when 1<=q<=A; no derivative or integral estimate is assumed. -/
theorem norm_integral_exp_mul_log_sub_le (A B u q : ℝ)
    (hAB : A ≤ B) (hq : 1 ≤ q) (hqa : q ≤ A) (hu : 0 < u) :
    ‖∫ t in A..B, Complex.exp (((u : ℂ) * I) * (t : ℂ)) *
      ((Real.log t - Real.log q : ℝ) : ℂ)‖ ≤ 3 * Real.log B / u := by
  have hA : 0 < A := lt_of_lt_of_le (by linarith : 0 < q) hqa
  have hB : 0 < B := lt_of_lt_of_le hA hAB
  have hLB : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
  have hp : ∀ t : ℝ, ‖Complex.exp (((u : ℂ) * I) * (t : ℂ))‖ = 1 := by
    intro t
    rw [Complex.norm_exp]
    simp
  have hendpoint : ∀ t, q ≤ t → t ≤ B →
      ‖((Real.log t - Real.log q : ℝ) : ℂ)‖ ≤ Real.log B := by
    intro t hqt htB
    have ht : 0 < t := lt_of_lt_of_le (by linarith : 0 < q) hqt
    have h1 := Real.log_le_log (by linarith : 0 < q) hqt
    have h2 := Real.log_le_log ht htB
    have h3 := Real.log_nonneg hq
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h1)]
    linarith
  have hJ : ‖∫ t in A..B, Complex.exp (((u : ℂ) * I) * (t : ℂ)) / (t : ℂ)‖ ≤
      Real.log B := by
    calc
      _ ≤ ∫ t in A..B, ‖Complex.exp (((u : ℂ) * I) * (t : ℂ)) / (t : ℂ)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hAB
      _ = ∫ t in A..B, 1 / t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hAB] at ht
        have ht0 : 0 < t := lt_of_lt_of_le hA ht.1
        change ‖Complex.exp (((u : ℂ) * I) * (t : ℂ)) / (t : ℂ)‖ = 1 / t
        rw [norm_div, hp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
      _ = Real.log B - Real.log A := by
        rw [integral_one_div_of_pos hA hB, Real.log_div hB.ne' hA.ne']
      _ ≤ _ := by linarith [Real.log_nonneg (show 1 ≤ A by linarith)]
  rw [integral_exp_mul_log_sub_eq A B u q hA hB hu.ne', norm_div]
  have hden : ‖(u : ℂ) * I‖ = u := by simp [abs_of_pos hu]
  rw [hden]
  apply div_le_div_of_nonneg_right _ hu.le
  have h1 := norm_sub_le
    (Complex.exp (((u : ℂ) * I) * (B : ℂ)) * ((Real.log B - Real.log q : ℝ) : ℂ) -
      Complex.exp (((u : ℂ) * I) * (A : ℂ)) * ((Real.log A - Real.log q : ℝ) : ℂ))
    (∫ t in A..B, Complex.exp (((u : ℂ) * I) * (t : ℂ)) / (t : ℂ))
  have h2 := norm_sub_le
    (Complex.exp (((u : ℂ) * I) * (B : ℂ)) * ((Real.log B - Real.log q : ℝ) : ℂ))
    (Complex.exp (((u : ℂ) * I) * (A : ℂ)) * ((Real.log A - Real.log q : ℝ) : ℂ))
  simp only [norm_mul, hp, one_mul] at h2
  have hAend := hendpoint A hqa hAB
  have hBend := hendpoint B (hqa.trans hAB) le_rfl
  linarith only [h1, h2, hJ, hAend, hBend]

end Complex
