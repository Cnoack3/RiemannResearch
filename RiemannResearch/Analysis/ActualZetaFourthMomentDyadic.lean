/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZetaFourthMomentReduction
import RiemannResearch.Analysis.DyadicIntegralBound
import RiemannResearch.RH.WeilExplicitFormula.XiPrime.Hardy.ZFunction
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Dyadic residual criterion for the actual zeta fourth moment

This closes the dyadic-to-global assembly in the uploaded Ingham
continuation. The actual-residual bound on each window remains a
hypothesis. The two cutoffs, coefficients, and phase can be chosen
independently on every window. The square-root residual transfer keeps
the L2 constant instead of replacing it by three times the squared costs.

The phase of the actual functional equation is connected to the vendored
Hardy API. Its continuity and unit modulus are proved, including at zero.
Source: Chourasiya--Simonic, arXiv:2507.15184v2, Section 5.1, supports the
analytic representation agenda. The uniform contour remainder is not
proved here. Dyadic induction is an elementary assembly step.
-/
noncomputable section
open MeasureTheory Complex Set
open scoped BigOperators

namespace RiemannResearch.Analysis

/-- The actual squared functional-equation phase on the critical line. -/
def zetaSquareCriticalPhase (t : ℝ) : ℂ :=
  Zeta23.XiPrime.chiFE ((1 / 2 : ℂ) + Complex.I * t) ^ 2

theorem zetaSquareCriticalPhase_eq_gamma_ratio (t : ℝ) :
    zetaSquareCriticalPhase t =
      (star (Zeta23.XiPrime.Gfun t) / Zeta23.XiPrime.Gfun t) ^ 2 := by
  have hs : (1 / 2 : ℂ) + Complex.I * t = Zeta23.XiPrime.sline t := by
    unfold Zeta23.XiPrime.sline
    ring
  rw [zetaSquareCriticalPhase, hs, Zeta23.XiPrime.chiFE_sline]
  rfl

theorem continuous_zetaSquareCriticalPhase : Continuous zetaSquareCriticalPhase := by
  have hG : Continuous Zeta23.XiPrime.Gfun :=
    continuous_iff_continuousAt.mpr
      (fun t => (Zeta23.XiPrime.hasDerivAt_Gfun t).continuousAt)
  have he : zetaSquareCriticalPhase = fun t =>
      (star (Zeta23.XiPrime.Gfun t) / Zeta23.XiPrime.Gfun t) ^ 2 :=
    funext zetaSquareCriticalPhase_eq_gamma_ratio
  rw [he]
  exact (hG.star.div hG Zeta23.XiPrime.Gfun_ne_zero).pow 2

@[simp] theorem norm_zetaSquareCriticalPhase (t : ℝ) :
    ‖zetaSquareCriticalPhase t‖ = 1 := by
  rw [zetaSquareCriticalPhase_eq_gamma_ratio, norm_pow, norm_div, norm_star,
    div_self (norm_ne_zero_iff.mpr (Zeta23.XiPrime.Gfun_ne_zero t)), one_pow]

/-- The actual phase preserves every reflected divisor-polynomial moment exactly. -/
theorem zeta_phase_reflected_divisor_moment (N : ℕ) (w : ℕ → ℂ) (H T : ℝ) :
    (∫ t in H..T, ‖zetaSquareCriticalPhase t * star (divisorPolynomial N w t)‖ ^ 2) =
      ∫ t in H..T, ‖divisorPolynomial N w t‖ ^ 2 := by
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [norm_mul, norm_star, norm_zetaSquareCriticalPhase, one_mul]

/-- One window, with independent cutoffs and the L2 constant retained. -/
theorem zeta_fourth_moment_dyadic_le_of_residual
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (u v : ℕ → ℂ) (hu : ∀ n ∈ Finset.Icc 1 N, ‖u n‖ ≤ 1)
    (hv : ∀ n ∈ Finset.Icc 1 M, ‖v n‖ ≤ 1)
    {φ : ℝ → ℂ} (hφ : Continuous φ) {U C_R : ℝ} (hU : 2 ≤ U)
    (hNU : (N : ℝ) ≤ U) (hMU : (M : ℝ) ≤ U) (hC : 0 ≤ C_R)
    (hφnorm : ∀ t ∈ Set.Icc U (2 * U), ‖φ t‖ ≤ 1)
    (hR : (∫ t in U..2 * U, ‖zetaSquareResidual (divisorPolynomial N u)
      (fun t => φ t * star (divisorPolynomial M v t)) t‖ ^ 2) ≤
        C_R * U * (Real.log U) ^ 4) :
    (∫ t in U..2 * U, ‖riemannZeta ((1 / 2 : ℂ) + Complex.I * t)‖ ^ 4) ≤
      (2 * Real.sqrt (162 * (12 * Real.sqrt (2 * Real.pi) *
        Real.exp (1 / 2 : ℝ))) + Real.sqrt C_R) ^ 2 * U * (Real.log U) ^ 4 := by
  let A : ℝ := 162 * (12 * Real.sqrt (2 * Real.pi) * Real.exp (1 / 2 : ℝ))
  let W : ℝ := U * (Real.log U) ^ 4
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hW : 0 ≤ W := by
    have hU0 : 0 ≤ U := by linarith
    exact mul_nonneg hU0 (pow_nonneg (Real.log_nonneg (by linarith)) 4)
  have hp := divisorPolynomial_second_moment_le hN u hu
    (H := U) (T := 2 * U) (by linarith)
  have hq := reflected_divisorPolynomial_second_moment_le hM v hv hφ
    (H := U) (T := 2 * U) (by linarith) hφnorm
  rw [show 2 * U - U = U by ring] at hp hq
  have hcostN := cutoff_log_four_cost_le hN hU hNU
    (A := 12 * Real.sqrt (2 * Real.pi) * Real.exp (1 / 2 : ℝ)) (by positivity)
  have hcostM := cutoff_log_four_cost_le hM hU hMU
    (A := 12 * Real.sqrt (2 * Real.pi) * Real.exp (1 / 2 : ℝ)) (by positivity)
  have hp' : (∫ t in U..2 * U, ‖divisorPolynomial N u t‖ ^ 2) ≤ A * W := by
    simpa only [A, W, mul_assoc] using hp.trans hcostN
  have hq' : (∫ t in U..2 * U, ‖φ t * star (divisorPolynomial M v t)‖ ^ 2) ≤ A * W := by
    simpa only [A, W, mul_assoc] using hq.trans hcostM
  have hres : (∫ t in U..2 * U, ‖zetaSquareResidual (divisorPolynomial N u)
      (fun t => φ t * star (divisorPolynomial M v t)) t‖ ^ 2) ≤ C_R * W := by
    simpa only [W, mul_assoc] using hR
  have hs := add_le_add (add_le_add (Real.sqrt_le_sqrt hp') (Real.sqrt_le_sqrt hq'))
    (Real.sqrt_le_sqrt hres)
  rw [Real.sqrt_mul hA, Real.sqrt_mul hC] at hs
  have hz := zeta_fourth_moment_le_residual_l2 (continuous_divisorPolynomial N u)
    (hφ.mul (continuous_divisorPolynomial M v).star) (H := U) (T := 2 * U) (by linarith)
  have hh := hz.trans (pow_le_pow_left₀ (by positivity) hs 2)
  have he : (Real.sqrt A * Real.sqrt W + Real.sqrt A * Real.sqrt W +
      Real.sqrt C_R * Real.sqrt W) ^ 2 =
      (2 * Real.sqrt A + Real.sqrt C_R) ^ 2 * W := by
    calc
      _ = (2 * Real.sqrt A + Real.sqrt C_R) ^ 2 * (Real.sqrt W) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hW]
  rw [he] at hh
  simpa only [A, W, mul_assoc] using hh

/-- A dyadic fourth-moment bound gives I1, with the finite initial interval absorbed. -/
theorem exists_fourth_moment_bound_of_dyadic
    {H D : ℝ} (hH : 2 ≤ H) (hD : 0 ≤ D)
    (hwindow : ∀ U ≥ H, (∫ t in U..2 * U,
      ‖riemannZeta ((1 / 2 : ℂ) + Complex.I * t)‖ ^ 4) ≤
        D * U * (Real.log U) ^ 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ T ≥ H,
      (∫ t in (0 : ℝ)..T, ‖riemannZeta ((1 / 2 : ℂ) + Complex.I * t)‖ ^ 4) ≤
        C * T * (Real.log T) ^ 4 := by
  let f : ℝ → ℝ := fun t => ‖riemannZeta ((1 / 2 : ℂ) + Complex.I * t)‖ ^ 4
  let A : ℝ := ∫ t in (0 : ℝ)..2 * H, f t
  let C : ℝ := D + A / (H * (Real.log H) ^ 4) + 1
  have hH0 : 0 < H := by linarith
  have hlog : 0 < Real.log H := Real.log_pos (by linarith)
  have hden : 0 < H * (Real.log H) ^ 4 := by positivity
  have hA : 0 ≤ A := intervalIntegral.integral_nonneg (by linarith)
    (fun _ _ => by dsimp [f]; positivity)
  have hC : 0 < C := by dsimp [C]; positivity
  have hDC : D ≤ C := by
    have := div_nonneg hA hden.le
    dsimp [C]
    linarith
  have hhead : A ≤ C * H * (Real.log H) ^ 4 := by
    have hc : A / (H * (Real.log H) ^ 4) ≤ C := by dsimp [C]; linarith
    have := (div_le_iff₀ hden).mp hc
    nlinarith
  refine ⟨C, hC, ?_⟩
  apply integral_bound_of_dyadic_linear_weight f (fun T => (Real.log T) ^ 4)
    (InghamMollifier.continuous_critical_zeta.norm.pow 4)
    (fun _ => by dsimp [f]; positivity) hH0 hC.le hDC ?_ ?_ hhead hwindow
  · intro a ha b hb hab
    have ha1 : 1 ≤ a := by change H ≤ a at ha; linarith
    exact pow_le_pow_left₀ (Real.log_nonneg ha1)
      (Real.log_le_log (by linarith) hab) 4
  · intro T hT
    positivity

/-- A conditional research reduction: only dyadic residual moments are requested.
All fitting data may be selected afresh for each window; no uniform regularity
or coherence across windows is assumed. -/
theorem exists_fourth_moment_bound_of_dyadic_residual
    {H C_R : ℝ} (hH : 2 ≤ H) (hC : 0 ≤ C_R)
    (hfit : ∀ U ≥ H, ∃ (N M : ℕ) (u v : ℕ → ℂ) (φ : ℝ → ℂ),
      0 < N ∧ 0 < M ∧ (N : ℝ) ≤ U ∧ (M : ℝ) ≤ U ∧
      (∀ n ∈ Finset.Icc 1 N, ‖u n‖ ≤ 1) ∧
      (∀ n ∈ Finset.Icc 1 M, ‖v n‖ ≤ 1) ∧ Continuous φ ∧
      (∀ t ∈ Set.Icc U (2 * U), ‖φ t‖ ≤ 1) ∧
      (∫ t in U..2 * U, ‖zetaSquareResidual (divisorPolynomial N u)
        (fun t => φ t * star (divisorPolynomial M v t)) t‖ ^ 2) ≤
          C_R * U * (Real.log U) ^ 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ T ≥ H,
      (∫ t in (0 : ℝ)..T, ‖riemannZeta ((1 / 2 : ℂ) + Complex.I * t)‖ ^ 4) ≤
        C * T * (Real.log T) ^ 4 := by
  apply exists_fourth_moment_bound_of_dyadic hH
    (D := (2 * Real.sqrt (162 * (12 * Real.sqrt (2 * Real.pi) *
      Real.exp (1 / 2 : ℝ))) + Real.sqrt C_R) ^ 2) (sq_nonneg _)
  intro U hU
  obtain ⟨N, M, u, v, φ, hN, hM, hNU, hMU, hu, hv, hφ, hφnorm, hR⟩ := hfit U hU
  exact zeta_fourth_moment_dyadic_le_of_residual hN hM u v hu hv hφ
    (hH.trans hU) hNU hMU hC hφnorm hR

/-- The canonical choice `N=floor U`, unit weights, and the actual functional
equation phase. Its only domain-specific premise is the dyadic residual bound. -/
theorem exists_fourth_moment_bound_of_actual_dyadic_residual
    {H C_R : ℝ} (hH : 2 ≤ H) (hC : 0 ≤ C_R)
    (hR : ∀ U ≥ H,
      (∫ t in U..2 * U, ‖zetaSquareResidual
        (divisorPolynomial ⌊U⌋₊ (fun _ => 1))
        (fun t => zetaSquareCriticalPhase t *
          star (divisorPolynomial ⌊U⌋₊ (fun _ => 1) t)) t‖ ^ 2) ≤
            C_R * U * (Real.log U) ^ 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ T ≥ H,
      (∫ t in (0 : ℝ)..T, ‖riemannZeta ((1 / 2 : ℂ) + Complex.I * t)‖ ^ 4) ≤
        C * T * (Real.log T) ^ 4 := by
  apply exists_fourth_moment_bound_of_dyadic_residual hH hC
  intro U hU
  have hN : 0 < ⌊U⌋₊ := Nat.floor_pos.mpr (by linarith)
  have hNU : (⌊U⌋₊ : ℝ) ≤ U := Nat.floor_le (by linarith)
  refine ⟨⌊U⌋₊, ⌊U⌋₊, (fun _ => 1), (fun _ => 1),
    zetaSquareCriticalPhase, hN, hN, hNU, hNU, ?_, ?_,
    continuous_zetaSquareCriticalPhase, ?_, hR U hU⟩
  · intro n hn
    simp
  · intro n hn
    simp
  · intro t ht
    simp

/-- The L2 constant is never worse than the earlier three-square estimate. -/
theorem dyadic_residual_l2_constant_le {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) :
    (2 * Real.sqrt A + Real.sqrt C) ^ 2 ≤ 3 * (2 * A + C) := by
  nlinarith [Real.sq_sqrt hA, Real.sq_sqrt hC,
    sq_nonneg (Real.sqrt A - Real.sqrt C)]

end RiemannResearch.Analysis
