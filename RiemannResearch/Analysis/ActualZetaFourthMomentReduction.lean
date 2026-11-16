/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.DivisorPolynomialMoment
import RiemannResearch.Analysis.IntervalL2Triangle
import RiemannResearch.Analysis.ActualInghamMollifierMoment
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Exact residual and fourth-moment transfer for the actual zeta function

The unconditional results here are finite identities and transfer inequalities.
The bound on the actual residual is an explicit, unresolved analytic input.
No actual-zeta fourth-moment provider or approximate functional equation is
asserted. The existing Ingham I2 provider is used without modification.

Source for the representation agenda: Chourasiya--Simonic,
https://arxiv.org/html/2507.15184v2, Section 5.1, equations (51)--(56).
Those contour identities and their uniform remainder bounds are external
classical results, not premises silently supplied to these proofs.
-/
noncomputable section
open MeasureTheory Complex Set
open scoped BigOperators

namespace RiemannResearch.Analysis

def zetaSquareResidual (P Q : ℝ → ℂ) (t : ℝ) : ℂ :=
  riemannZeta ((1 / 2 : ℂ) + Complex.I * t) ^ 2 - P t - Q t

theorem zetaSquareResidual_identity (P Q : ℝ → ℂ) (t : ℝ) :
    riemannZeta ((1 / 2 : ℂ) + Complex.I * t) ^ 2 =
      P t + Q t + zetaSquareResidual P Q t := by
  unfold zetaSquareResidual
  ring

theorem continuous_zetaSquareResidual {P Q : ℝ → ℂ}
    (hP : Continuous P) (hQ : Continuous Q) : Continuous (zetaSquareResidual P Q) :=
  ((InghamMollifier.continuous_critical_zeta.pow 2).sub hP).sub hQ

/-- Every signed cross term and the norm-square residual is retained. -/
theorem zeta_fourth_power_residual_identity (P Q : ℝ → ℂ) (t : ℝ) :
    ‖riemannZeta ((1 / 2 : ℂ) + Complex.I * t)‖ ^ 4 =
      ‖P t‖ ^ 2 + ‖Q t‖ ^ 2 + ‖zetaSquareResidual P Q t‖ ^ 2 +
      2 * (P t * star (Q t)).re +
      2 * (P t * star (zetaSquareResidual P Q t)).re +
      2 * (Q t * star (zetaSquareResidual P Q t)).re := by
  calc
    _ = ‖riemannZeta ((1 / 2 : ℂ) + Complex.I * t) ^ 2‖ ^ 2 := by
      rw [norm_pow]; ring
    _ = _ := by
      rw [zetaSquareResidual_identity P Q t]
      simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
        Complex.add_re, Complex.add_im, Complex.mul_re, Complex.star_def,
        Complex.conj_re, Complex.conj_im]
      ring

/-- A transfer inequality; the residual moment on the right is not estimated here. -/
theorem zeta_fourth_moment_le_residual {P Q : ℝ → ℂ}
    (hP : Continuous P) (hQ : Continuous Q) {H T : ℝ} (hHT : H ≤ T) :
    (∫ t in H..T, ‖riemannZeta ((1 / 2 : ℂ) + Complex.I * t)‖ ^ 4) ≤
      3 * ((∫ t in H..T, ‖P t‖ ^ 2) + (∫ t in H..T, ‖Q t‖ ^ 2) +
        (∫ t in H..T, ‖zetaSquareResidual P Q t‖ ^ 2)) := by
  have hR := continuous_zetaSquareResidual hP hQ
  have hiP : IntervalIntegrable (fun t => ‖P t‖ ^ 2) volume H T :=
    (hP.norm.pow 2).intervalIntegrable H T
  have hiQ : IntervalIntegrable (fun t => ‖Q t‖ ^ 2) volume H T :=
    (hQ.norm.pow 2).intervalIntegrable H T
  have hiR : IntervalIntegrable (fun t => ‖zetaSquareResidual P Q t‖ ^ 2) volume H T :=
    (hR.norm.pow 2).intervalIntegrable H T
  have hb := intervalIntegral.integral_mono_on (μ := volume) hHT
    (InghamMollifier.continuous_critical_zeta.norm.pow 4 |>.intervalIntegrable H T)
    (((hP.norm.pow 2).add (hQ.norm.pow 2)).add (hR.norm.pow 2) |>.const_mul 3
      |>.intervalIntegrable H T) (fun t _ => show
        ‖riemannZeta ((1 / 2 : ℂ) + Complex.I * t)‖ ^ 4 ≤
          3 * (‖P t‖ ^ 2 + ‖Q t‖ ^ 2 + ‖zetaSquareResidual P Q t‖ ^ 2) from by
      have hn := (norm_add_le (P t + Q t) (zetaSquareResidual P Q t)).trans
        (add_le_add (norm_add_le (P t) (Q t)) le_rfl)
      rw [← zetaSquareResidual_identity P Q t, norm_pow] at hn
      have hs := pow_le_pow_left₀ (sq_nonneg _) hn 2
      nlinarith [sq_nonneg (‖P t‖ - ‖Q t‖),
        sq_nonneg (‖P t‖ - ‖zetaSquareResidual P Q t‖),
        sq_nonneg (‖Q t‖ - ‖zetaSquareResidual P Q t‖)])
  change (∫ t in H..T, ‖riemannZeta ((1 / 2 : ℂ) + Complex.I * t)‖ ^ 4) ≤
    ∫ t in H..T, 3 * (‖P t‖ ^ 2 + ‖Q t‖ ^ 2 + ‖zetaSquareResidual P Q t‖ ^ 2) at hb
  simpa only [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hiP.add hiQ) hiR,
    intervalIntegral.integral_add hiP hiQ] using hb

/-- Multiplication by a bounded phase and complex conjugation preserve the upper mean value. -/
theorem reflected_divisorPolynomial_second_moment_le {N : ℕ} (hN : 0 < N)
    (w : ℕ → ℂ) (hw : ∀ n ∈ Finset.Icc 1 N, ‖w n‖ ≤ 1)
    {φ : ℝ → ℂ} (hφ : Continuous φ) {H T : ℝ} (hHT : H ≤ T)
    (hφnorm : ∀ t ∈ Set.Icc H T, ‖φ t‖ ≤ 1) :
    (∫ t in H..T, ‖φ t * star (divisorPolynomial N w t)‖ ^ 2) ≤
      (12 * Real.sqrt (2 * Real.pi) * Real.exp (1 / 2 : ℝ)) *
        (T - H + N) * (1 + Real.log N) ^ 4 := by
  apply le_trans _ (divisorPolynomial_second_moment_le hN w hw hHT)
  have hc : Continuous (fun t => φ t * star (divisorPolynomial N w t)) :=
    hφ.mul (continuous_divisorPolynomial N w).star
  apply intervalIntegral.integral_mono_on hHT
    (hc.norm.pow 2 |>.intervalIntegrable H T)
    ((continuous_divisorPolynomial N w).norm.pow 2 |>.intervalIntegrable H T)
  intro t ht
  change ‖φ t * star (divisorPolynomial N w t)‖ ^ 2 ≤ ‖divisorPolynomial N w t‖ ^ 2
  rw [norm_mul, norm_star]
  apply pow_le_pow_left₀ (by positivity)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hφnorm t ht) (norm_nonneg _)

/-- Two actual divisor polynomials, plus the explicit actual-zeta residual. -/
theorem zeta_fourth_moment_le_two_divisor_polynomials {N : ℕ} (hN : 0 < N)
    (u v : ℕ → ℂ) (hu : ∀ n ∈ Finset.Icc 1 N, ‖u n‖ ≤ 1)
    (hv : ∀ n ∈ Finset.Icc 1 N, ‖v n‖ ≤ 1)
    {φ : ℝ → ℂ} (hφ : Continuous φ) {H T : ℝ} (hHT : H ≤ T)
    (hφnorm : ∀ t ∈ Set.Icc H T, ‖φ t‖ ≤ 1) :
    (∫ t in H..T, ‖riemannZeta ((1 / 2 : ℂ) + Complex.I * t)‖ ^ 4) ≤
      3 * (2 * ((12 * Real.sqrt (2 * Real.pi) * Real.exp (1 / 2 : ℝ)) *
        (T - H + N) * (1 + Real.log N) ^ 4) +
        ∫ t in H..T, ‖zetaSquareResidual (divisorPolynomial N u)
          (fun t => φ t * star (divisorPolynomial N v t)) t‖ ^ 2) := by
  have hp := divisorPolynomial_second_moment_le hN u hu hHT
  have hq := reflected_divisorPolynomial_second_moment_le hN v hv hφ hHT hφnorm
  have hc := zeta_fourth_moment_le_residual (P := divisorPolynomial N u)
    (Q := fun t => φ t * star (divisorPolynomial N v t)) (continuous_divisorPolynomial N u)
    (hφ.mul (continuous_divisorPolynomial N v).star) hHT
  linarith

/-- Explicit logarithmic bookkeeping for a cutoff no larger than the height. -/
theorem cutoff_log_four_cost_le {N : ℕ} (hN : 0 < N) {T A : ℝ}
    (hT : 2 ≤ T) (hNT : (N : ℝ) ≤ T) (hA : 0 ≤ A) :
    A * (T + N) * (1 + Real.log N) ^ 4 ≤ 162 * A * T * (Real.log T) ^ 4 := by
  have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hlN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlT : (1 / 2 : ℝ) ≤ Real.log T :=
    hl2.trans (Real.log_le_log (by norm_num) hT)
  have hlNT := Real.log_le_log hN0 hNT
  have hlog : 1 + Real.log N ≤ 3 * Real.log T := by linarith
  calc
    _ ≤ A * (2 * T) * (3 * Real.log T) ^ 4 :=
      mul_le_mul (mul_le_mul_of_nonneg_left (by linarith : T + N ≤ 2 * T) hA)
        (pow_le_pow_left₀ (by linarith) hlog 4) (by positivity) (by positivity)
    _ = _ := by ring

/-- Conditional I1 estimate with the unresolved residual bound displayed explicitly. -/
theorem zeta_fourth_moment_le_of_residual_bound {N : ℕ} (hN : 0 < N)
    (u v : ℕ → ℂ) (hu : ∀ n ∈ Finset.Icc 1 N, ‖u n‖ ≤ 1)
    (hv : ∀ n ∈ Finset.Icc 1 N, ‖v n‖ ≤ 1)
    {φ : ℝ → ℂ} (hφ : Continuous φ) {T C_R : ℝ} (hT : 2 ≤ T)
    (hNT : (N : ℝ) ≤ T) (hφnorm : ∀ t ∈ Set.Icc 0 T, ‖φ t‖ ≤ 1)
    (hR : (∫ t in (0 : ℝ)..T, ‖zetaSquareResidual (divisorPolynomial N u)
      (fun t => φ t * star (divisorPolynomial N v t)) t‖ ^ 2) ≤
        C_R * T * (Real.log T) ^ 4) :
    (∫ t in (0 : ℝ)..T, ‖riemannZeta ((1 / 2 : ℂ) + Complex.I * t)‖ ^ 4) ≤
      (3 * (324 * (12 * Real.sqrt (2 * Real.pi) * Real.exp (1 / 2 : ℝ)) + C_R)) *
        T * (Real.log T) ^ 4 := by
  have hb := zeta_fourth_moment_le_two_divisor_polynomials hN u v hu hv hφ
    (H := 0) (T := T) (by linarith) hφnorm
  simp only [sub_zero] at hb
  have hk := cutoff_log_four_cost_le hN hT hNT
    (A := 12 * Real.sqrt (2 * Real.pi) * Real.exp (1 / 2 : ℝ)) (by positivity)
  nlinarith

/-- A uniform actual-residual provider would discharge I1 with one height-independent constant.
This theorem is a conditional research reduction, not a provider for its premise. -/
theorem exists_fourth_moment_bound_of_uniform_residual
    {H₀ C_R : ℝ} (hH : 2 ≤ H₀) (hC : 0 ≤ C_R)
    (u v : ℝ → ℕ → ℂ) (hu : ∀ T ≥ H₀, ∀ n, ‖u T n‖ ≤ 1)
    (hv : ∀ T ≥ H₀, ∀ n, ‖v T n‖ ≤ 1)
    {φ : ℝ → ℂ} (hφ : Continuous φ) (hφnorm : ∀ t, ‖φ t‖ ≤ 1)
    (hR : ∀ T ≥ H₀, ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ T ∧
      (∫ t in (0 : ℝ)..T, ‖zetaSquareResidual (divisorPolynomial N (u T))
        (fun t => φ t * star (divisorPolynomial N (v T) t)) t‖ ^ 2) ≤
          C_R * T * (Real.log T) ^ 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ T ≥ H₀,
      (∫ t in (0 : ℝ)..T, ‖riemannZeta ((1 / 2 : ℂ) + Complex.I * t)‖ ^ 4) ≤
        C * T * (Real.log T) ^ 4 := by
  refine ⟨3 * (324 * (12 * Real.sqrt (2 * Real.pi) * Real.exp (1 / 2 : ℝ)) + C_R),
    by positivity, ?_⟩
  intro T hT
  obtain ⟨N, hN, hNT, hres⟩ := hR T hT
  exact zeta_fourth_moment_le_of_residual_bound hN (u T) (v T)
    (fun n _ => hu T hT n) (fun n _ => hv T hT n) hφ (hH.trans hT) hNT
    (fun t _ => hφnorm t) hres

/-- Sharp L2 transfer: the three square-root moments are added before squaring. -/
theorem zeta_fourth_moment_le_residual_l2 {P Q : ℝ → ℂ}
    (hP : Continuous P) (hQ : Continuous Q) {H T : ℝ} (hHT : H ≤ T) :
    (∫ t in H..T, ‖riemannZeta ((1 / 2 : ℂ) + Complex.I * t)‖ ^ 4) ≤
      (Real.sqrt (∫ t in H..T, ‖P t‖ ^ 2) +
        Real.sqrt (∫ t in H..T, ‖Q t‖ ^ 2) +
        Real.sqrt (∫ t in H..T, ‖zetaSquareResidual P Q t‖ ^ 2)) ^ 2 := by
  have he : (∫ t in H..T, ‖riemannZeta ((1 / 2 : ℂ) + Complex.I * t)‖ ^ 4) =
      ∫ t in H..T, ‖P t + Q t + zetaSquareResidual P Q t‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    change ‖riemannZeta ((1 / 2 : ℂ) + Complex.I * t)‖ ^ 4 =
      ‖P t + Q t + zetaSquareResidual P Q t‖ ^ 2
    rw [← zetaSquareResidual_identity P Q t, norm_pow]
    ring
  have h := intervalIntegral.sqrt_integral_norm_sq_add_le (hP.add hQ)
    (continuous_zetaSquareResidual hP hQ) hHT
  have h' := intervalIntegral.sqrt_integral_norm_sq_add_le hP hQ hHT
  have hh := h.trans (add_le_add h' le_rfl)
  rw [he]
  exact (Real.sqrt_le_iff.mp hh).2

/-- Separate cutoffs and independent square-root bounds for the two polynomials. -/
theorem zeta_fourth_moment_le_two_cutoffs_residual
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (u v : ℕ → ℂ) (hu : ∀ n ∈ Finset.Icc 1 N, ‖u n‖ ≤ 1)
    (hv : ∀ n ∈ Finset.Icc 1 M, ‖v n‖ ≤ 1)
    {φ : ℝ → ℂ} (hφ : Continuous φ) {H T : ℝ} (hHT : H ≤ T)
    (hφnorm : ∀ t ∈ Set.Icc H T, ‖φ t‖ ≤ 1) :
    (∫ t in H..T, ‖riemannZeta ((1 / 2 : ℂ) + Complex.I * t)‖ ^ 4) ≤
      (Real.sqrt ((12 * Real.sqrt (2 * Real.pi) * Real.exp (1 / 2 : ℝ)) *
          (T - H + N) * (1 + Real.log N) ^ 4) +
       Real.sqrt ((12 * Real.sqrt (2 * Real.pi) * Real.exp (1 / 2 : ℝ)) *
          (T - H + M) * (1 + Real.log M) ^ 4) +
       Real.sqrt (∫ t in H..T, ‖zetaSquareResidual (divisorPolynomial N u)
          (fun t => φ t * star (divisorPolynomial M v t)) t‖ ^ 2)) ^ 2 := by
  apply (zeta_fourth_moment_le_residual_l2 (continuous_divisorPolynomial N u)
    (hφ.mul (continuous_divisorPolynomial M v).star) hHT).trans
  apply pow_le_pow_left₀ (by positivity)
  exact add_le_add
    (add_le_add (Real.sqrt_le_sqrt (divisorPolynomial_second_moment_le hN u hu hHT))
      (Real.sqrt_le_sqrt
        (reflected_divisorPolynomial_second_moment_le hM v hv hφ hHT hφnorm))) le_rfl

namespace InghamMollifier

/-- A bound on `[0,T]` discharges the actual fourth-moment integral on every `[H,T]`. -/
theorem critical_error_moment_le_of_fourth_moment_bound {X : ℕ} (hX : 1 ≤ X)
    {H T C : ℝ} (hH : 0 ≤ H) (hHT : H ≤ T)
    (hfourth : (∫ t in (0 : ℝ)..T,
      ‖riemannZeta ((1 / 2 : ℂ) + Complex.I * t)‖ ^ 4) ≤ C * T * (Real.log T) ^ 4) :
    (∫ t in H..T, ‖riemannZeta ((1 / 2 : ℂ) + Complex.I * t) *
      mollifier X ((1 / 2 : ℂ) + Complex.I * t) - 1‖ ^ (4 / 3 : ℝ)) ≤
      (2 : ℝ) ^ (1 / 3 : ℝ) *
        ((C * T * (Real.log T) ^ 4) ^ (1 / 3 : ℝ) *
          ((12 * Real.sqrt (2 * Real.pi) * Real.exp (1 / 2 : ℝ)) *
            (T - H + X) * (1 + Real.log X)) ^ (2 / 3 : ℝ) + (T - H)) := by
  apply (critical_error_moment_le_fourth_moment hX hHT).trans
  have hw : (∫ t in H..T, ‖riemannZeta ((1 / 2 : ℂ) + Complex.I * t)‖ ^ 4) ≤
      C * T * (Real.log T) ^ 4 := by
    apply le_trans _ hfourth
    exact intervalIntegral.integral_mono_interval hH hHT le_rfl
      (Filter.Eventually.of_forall (fun _ => by positivity))
      (continuous_critical_zeta.norm.pow 4 |>.intervalIntegrable 0 T)
  have hz0 : 0 ≤ ∫ t in H..T, ‖riemannZeta ((1 / 2 : ℂ) + Complex.I * t)‖ ^ 4 :=
    intervalIntegral.integral_nonneg hHT (fun _ _ => by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hz0 hw (by norm_num))
  exact Real.rpow_nonneg (by
    have := sub_nonneg.mpr hHT
    have : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX)
    positivity) _

end InghamMollifier
end RiemannResearch.Analysis
