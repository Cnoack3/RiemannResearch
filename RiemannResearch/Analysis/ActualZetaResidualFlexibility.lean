/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZetaFourthMomentReduction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform actual residual bounds with independent cutoffs

The exact signed residual identity is retained first. A global actual fourth
moment then controls the residual for any two independent positive cutoffs no
larger than the height, any unit-bounded complex coefficients on their finite
supports, and any continuous phase bounded by one on the interval.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Complex Set
open scoped BigOperators

namespace RiemannResearch.Analysis

/-- The exact norm-square residual, with all signed cross terms retained. -/
theorem zetaSquareResidual_norm_sq_identity (P Q : ℝ → ℂ) (t : ℝ) :
    ‖zetaSquareResidual P Q t‖ ^ 2 =
      ‖riemannZeta ((1 / 2 : ℂ) + I * t)‖ ^ 4 + ‖P t‖ ^ 2 + ‖Q t‖ ^ 2 -
      2 * (riemannZeta ((1 / 2 : ℂ) + I * t) ^ 2 * star (P t)).re -
      2 * (riemannZeta ((1 / 2 : ℂ) + I * t) ^ 2 * star (Q t)).re +
      2 * (P t * star (Q t)).re := by
  have hz : ‖riemannZeta ((1 / 2 : ℂ) + I * t)‖ ^ 4 =
      ‖riemannZeta ((1 / 2 : ℂ) + I * t) ^ 2‖ ^ 2 := by
    rw [norm_pow]
    ring
  rw [hz]
  unfold zetaSquareResidual
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring

/-- The actual residual is assembled in L2 before squaring. -/
theorem zetaSquareResidual_second_moment_le_l2 {P Q : ℝ → ℂ}
    (hP : Continuous P) (hQ : Continuous Q) {H T : ℝ} (hHT : H ≤ T) :
    (∫ t in H..T, ‖zetaSquareResidual P Q t‖ ^ 2) ≤
      (Real.sqrt (∫ t in H..T, ‖riemannZeta ((1 / 2 : ℂ) + I * t)‖ ^ 4) +
        Real.sqrt (∫ t in H..T, ‖P t‖ ^ 2) +
        Real.sqrt (∫ t in H..T, ‖Q t‖ ^ 2)) ^ 2 := by
  have hz := InghamMollifier.continuous_critical_zeta.pow 2
  have h₁ := intervalIntegral.sqrt_integral_norm_sq_add_le
    (f := fun t => riemannZeta ((1 / 2 : ℂ) + I * t) ^ 2 + -P t)
    (g := fun t => -Q t) (hz.add hP.neg) hQ.neg hHT
  have h₂ := intervalIntegral.sqrt_integral_norm_sq_add_le
    (f := fun t => riemannZeta ((1 / 2 : ℂ) + I * t) ^ 2)
    (g := fun t => -P t) hz hP.neg hHT
  have hh := h₁.trans (add_le_add h₂ le_rfl)
  have hn (t : ℝ) : ‖riemannZeta ((1 / 2 : ℂ) + I * t) ^ 2‖ ^ 2 =
      ‖riemannZeta ((1 / 2 : ℂ) + I * t)‖ ^ 4 := by rw [norm_pow]; ring
  simp only [Pi.add_apply, Pi.neg_apply, Pi.pow_apply, norm_neg, hn] at hh
  simpa only [zetaSquareResidual, sub_eq_add_neg] using (Real.sqrt_le_iff.mp hh).2

/-- A convenient linear-cost consequence of the sharp L2 triangle bound. -/
theorem zetaSquareResidual_second_moment_le_three {P Q : ℝ → ℂ}
    (hP : Continuous P) (hQ : Continuous Q) {H T : ℝ} (hHT : H ≤ T) :
    (∫ t in H..T, ‖zetaSquareResidual P Q t‖ ^ 2) ≤
      3 * ((∫ t in H..T, ‖riemannZeta ((1 / 2 : ℂ) + I * t)‖ ^ 4) +
        (∫ t in H..T, ‖P t‖ ^ 2) + (∫ t in H..T, ‖Q t‖ ^ 2)) := by
  have hz0 : 0 ≤ ∫ t in H..T, ‖riemannZeta ((1 / 2 : ℂ) + I * t)‖ ^ 4 :=
    intervalIntegral.integral_nonneg hHT (fun _ _ => by positivity)
  have hp0 : 0 ≤ ∫ t in H..T, ‖P t‖ ^ 2 :=
    intervalIntegral.integral_nonneg hHT (fun _ _ => sq_nonneg _)
  have hq0 : 0 ≤ ∫ t in H..T, ‖Q t‖ ^ 2 :=
    intervalIntegral.integral_nonneg hHT (fun _ _ => sq_nonneg _)
  apply (zetaSquareResidual_second_moment_le_l2 hP hQ hHT).trans
  nlinarith [Real.sq_sqrt hz0, Real.sq_sqrt hp0, Real.sq_sqrt hq0,
    sq_nonneg (Real.sqrt (∫ t in H..T, ‖riemannZeta ((1 / 2 : ℂ) + I * t)‖ ^ 4) -
      Real.sqrt (∫ t in H..T, ‖P t‖ ^ 2)),
    sq_nonneg (Real.sqrt (∫ t in H..T, ‖riemannZeta ((1 / 2 : ℂ) + I * t)‖ ^ 4) -
      Real.sqrt (∫ t in H..T, ‖Q t‖ ^ 2)),
    sq_nonneg (Real.sqrt (∫ t in H..T, ‖P t‖ ^ 2) -
      Real.sqrt (∫ t in H..T, ‖Q t‖ ^ 2))]

/-- A fourth-moment provider implies a residual bound for arbitrary independent
cutoffs. There is no lower-cutoff condition such as `U ≤ 2*N`. -/
theorem exists_uniform_two_cutoff_residual_bound_of_fourth_moment
    (hfourth : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (∫ t in (0 : ℝ)..T, ‖riemannZeta ((1 / 2 : ℂ) + I * t)‖ ^ 4) ≤
        C * T * (Real.log T) ^ 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 2 ≤ U → ∀ N M : ℕ,
      0 < N → 0 < M → (N : ℝ) ≤ U → (M : ℝ) ≤ U →
      ∀ u v : ℕ → ℂ, (∀ n ∈ Finset.Icc 1 N, ‖u n‖ ≤ 1) →
        (∀ n ∈ Finset.Icc 1 M, ‖v n‖ ≤ 1) →
      ∀ φ : ℝ → ℂ, Continuous φ → (∀ t ∈ Set.Icc U (2 * U), ‖φ t‖ ≤ 1) →
      (∫ t in U..(2 * U),
        ‖zetaSquareResidual (divisorPolynomial N u)
          (fun t => φ t * star (divisorPolynomial M v t)) t‖ ^ 2) ≤
            C * U * (Real.log U) ^ 4 := by
  obtain ⟨C₄, hC₄, hfourth⟩ := hfourth
  let K : ℝ := 12 * Real.sqrt (2 * Real.pi) * Real.exp (1 / 2 : ℝ)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨3 * (32 * C₄ + 324 * K), by positivity, ?_⟩
  intro U hU N M hN hM hNU hMU u v hu hv φ hφ hφnorm
  have hU0 : 0 < U := by linarith
  have hUU : U ≤ 2 * U := by linarith
  have hlog2U : 0 ≤ Real.log (2 * U) := Real.log_nonneg (by linarith)
  have hlog : Real.log (2 * U) ≤ 2 * Real.log U := by
    rw [Real.log_mul (by norm_num) hU0.ne']
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hU
    linarith
  have hz : (∫ t in U..(2 * U), ‖riemannZeta ((1 / 2 : ℂ) + I * t)‖ ^ 4) ≤
      32 * C₄ * U * (Real.log U) ^ 4 := by
    calc
      _ ≤ ∫ t in (0 : ℝ)..(2 * U), ‖riemannZeta ((1 / 2 : ℂ) + I * t)‖ ^ 4 :=
        intervalIntegral.integral_mono_interval hU0.le hUU le_rfl
          (Filter.Eventually.of_forall (fun _ => by positivity))
          (InghamMollifier.continuous_critical_zeta.norm.pow 4 |>.intervalIntegrable 0 (2 * U))
      _ ≤ C₄ * (2 * U) * (Real.log (2 * U)) ^ 4 := hfourth (2 * U) (by linarith)
      _ ≤ C₄ * (2 * U) * (2 * Real.log U) ^ 4 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog2U hlog 4) (by positivity)
      _ = _ := by ring
  have hp : (∫ t in U..(2 * U), ‖divisorPolynomial N u t‖ ^ 2) ≤
      162 * K * U * (Real.log U) ^ 4 := by
    calc
      _ ≤ K * (U + N) * (1 + Real.log N) ^ 4 := by
        simpa only [show 2 * U - U = U by ring] using
          divisorPolynomial_second_moment_le hN u hu (H := U) (T := 2 * U) hUU
      _ ≤ _ := cutoff_log_four_cost_le hN hU hNU hK.le
  have hq : (∫ t in U..(2 * U), ‖φ t * star (divisorPolynomial M v t)‖ ^ 2) ≤
      162 * K * U * (Real.log U) ^ 4 := by
    calc
      _ ≤ K * (U + M) * (1 + Real.log M) ^ 4 := by
        simpa only [show 2 * U - U = U by ring] using
          reflected_divisorPolynomial_second_moment_le hM v hv hφ
            (H := U) (T := 2 * U) hUU hφnorm
      _ ≤ _ := cutoff_log_four_cost_le hM hU hMU hK.le
  have hr := zetaSquareResidual_second_moment_le_three
    (P := divisorPolynomial N u) (Q := fun t => φ t * star (divisorPolynomial M v t))
    (continuous_divisorPolynomial N u)
    (hφ.mul (continuous_divisorPolynomial M v).star) hUU
  nlinarith

end RiemannResearch.Analysis
