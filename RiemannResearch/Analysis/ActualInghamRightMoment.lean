/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.DirichletTailMeanSquare
import RiemannResearch.Analysis.ActualMobiusZeroDetector
import RiemannResearch.Analysis.ActualMollifierRightBoundary
import RiemannResearch.Analysis.ZetaAbsoluteConvergenceBounds
import RiemannResearch.Analysis.ZeroOrdinateEquidistribution
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega

/-!
# An unconditional actual moving right-line Ingham moment

The exact identity f_X = -zeta * mobiusTail precedes the estimates. For every
eta > 0, X >= 1 and H <= T, the moment at sigma = 1 + eta is at most

  (1 + 1/eta)^2 * X^(-2*eta) *
    ((T-H)/(X*(1+2*eta)) + 26/eta).

On sigma = 1 + delta/log X this gives one explicit constant times
(1 + (T-H)/X) * (1+log X)^3, for every delta > 0 and X >= 2.
The constant does not depend on X, H or T. No supplied analytic provider,
critical-line moment, zero-density estimate or RH premise occurs.

Source for the moving-line target and its interpolation role:
Chourasiya--Simonic, arXiv:2507.15184v2, Section 4, Lemma 6 and Corollary 6,
https://arxiv.org/html/2507.15184v2.
That paper's sharper one-logarithm endpoint needs an additional arithmetic
coefficient-energy estimate; it is not proved here. The present proof instead
combines the checked mean square of the actual Mobius tail with the elementary
absolute-convergence bound for zeta. Gabriel interpolation, its damped
whole-line integrals, and the final boundary/counting assembly remain separate.
-/

noncomputable section
open MeasureTheory Complex Filter Set
open scoped BigOperators
namespace RiemannResearch.Analysis.InghamMollifier
open DirichletMeanSquare

private theorem moebius_norm_le_one (n : ℕ) (_hn : 1 ≤ n) :
    ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))

theorem mobiusTail_eq_dirichletTail (X : ℕ) (σ t : ℝ) :
    mobiusTail X ((σ : ℂ) + I * t) =
      dirichletTail (fun n => (ArithmeticFunction.moebius n : ℂ)) σ X t := by
  unfold mobiusTail dirichletTail
  apply tsum_congr
  intro k
  have hn : k + X + 1 ≠ 0 := by omega
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg,
    Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn), ← Complex.natCast_log]
  unfold tailTerm tailCoefficient ZeroOrdinate.phase
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem continuous_mobiusTail_right (X : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    Continuous (fun t : ℝ => mobiusTail X ((σ : ℂ) + I * t)) := by
  simp_rw [mobiusTail_eq_dirichletTail]
  exact continuous_dirichletTail moebius_norm_le_one hσ X

/-- The full actual error identity, before either factor is bounded. -/
theorem right_error_moment_identity (X : ℕ) {σ : ℝ} (hσ : 1 < σ) (H T : ℝ) :
    (∫ t in H..T, ‖riemannZeta ((σ : ℂ) + I * t) *
      mollifier X ((σ : ℂ) + I * t) - 1‖ ^ 2) =
    ∫ t in H..T, ‖riemannZeta ((σ : ℂ) + I * t)‖ ^ 2 *
      ‖mobiusTail X ((σ : ℂ) + I * t)‖ ^ 2 := by
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [mollifier_error_exact (by simpa using hσ) X, norm_mul, norm_neg, mul_pow]

theorem mobiusTail_second_moment_le {σ : ℝ} (hσ : 1 < σ)
    {X : ℕ} (hX : 1 ≤ X) {H T : ℝ} (hHT : H ≤ T) :
    (∫ t in H..T, ‖mobiusTail X ((σ : ℂ) + I * t)‖ ^ 2) ≤
      (T - H) * ((X : ℝ) ^ (1 - 2 * σ) / (2 * σ - 1)) +
        52 * ((X : ℝ) ^ (2 - 2 * σ) / (2 * σ - 2)) := by
  simp_rw [mobiusTail_eq_dirichletTail]
  exact dirichletTail_mean_square_le moebius_norm_le_one hσ hX hHT

/-- Unconditional actual error moment on every translated interval and every
right line. The constant is independent of the line, cutoff, and endpoints. -/
theorem actual_right_error_moment_le {σ : ℝ} (hσ : 1 < σ)
    {X : ℕ} (hX : 1 ≤ X) {H T : ℝ} (hHT : H ≤ T) :
    (∫ t in H..T, ‖riemannZeta ((σ : ℂ) + I * t) *
      mollifier X ((σ : ℂ) + I * t) - 1‖ ^ 2) ≤
      (1 + 1 / (σ - 1)) ^ 2 *
        ((T - H) * ((X : ℝ) ^ (1 - 2 * σ) / (2 * σ - 1)) +
          52 * ((X : ℝ) ^ (2 - 2 * σ) / (2 * σ - 2))) := by
  have hz : Continuous (fun t : ℝ => riemannZeta ((σ : ℂ) + I * t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (analyticAt_riemannZeta ?_).continuousAt.comp
      (by fun_prop : Continuous (fun t : ℝ => (σ : ℂ) + I * t)).continuousAt
    intro he
    have hr := congrArg Complex.re he
    simp at hr
    linarith
  have hm := continuous_mobiusTail_right X hσ
  have hζ (t : ℝ) : ‖riemannZeta ((σ : ℂ) + I * t)‖ ≤ 1 + 1 / (σ - 1) := by
    simpa using (norm_riemannZeta_le_integral_test
      (show 1 < ((σ : ℂ) + I * t).re by simpa using hσ))
  rw [right_error_moment_identity X hσ]
  calc
    _ ≤ ∫ t in H..T, (1 + 1 / (σ - 1)) ^ 2 *
        ‖mobiusTail X ((σ : ℂ) + I * t)‖ ^ 2 :=
      intervalIntegral.integral_mono hHT
        (((hz.norm.pow 2).mul (hm.norm.pow 2)).intervalIntegrable H T)
        (((continuous_const).mul (hm.norm.pow 2)).intervalIntegrable H T)
        (fun t => mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) (hζ t) 2) (sq_nonneg _))
    _ = (1 + 1 / (σ - 1)) ^ 2 *
        (∫ t in H..T, ‖mobiusTail X ((σ : ℂ) + I * t)‖ ^ 2) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (mobiusTail_second_moment_le hσ hX hHT)
      (sq_nonneg _)

/-- Explicit distance-to-one dependence, retaining the sharper diagonal denominator. -/
theorem actual_right_error_moment_gap_le {η : ℝ} (hη : 0 < η)
    {X : ℕ} (hX : 1 ≤ X) {H T : ℝ} (hHT : H ≤ T) :
    (∫ t in H..T, ‖riemannZeta (((1 + η : ℝ) : ℂ) + I * t) *
      mollifier X (((1 + η : ℝ) : ℂ) + I * t) - 1‖ ^ 2) ≤
      (1 + 1 / η) ^ 2 * (X : ℝ) ^ (-(2 * η)) *
        ((T - H) / ((X : ℝ) * (1 + 2 * η)) + 26 / η) := by
  have hh := actual_right_error_moment_le (by linarith : 1 < 1 + η) hX hHT
  have hx : 0 < (X : ℝ) := by exact_mod_cast hX
  have he : (X : ℝ) ^ (1 - 2 * (1 + η)) = (X : ℝ) ^ (-(2 * η)) / X := by
    rw [show 1 - 2 * (1 + η) = -(2 * η) - 1 by ring,
      Real.rpow_sub hx, Real.rpow_one]
  rw [he, show 2 - 2 * (1 + η) = -(2 * η) by ring,
    show 1 + η - 1 = η by ring, show 2 * (1 + η) - 1 = 1 + 2 * η by ring,
    show 2 * (1 + η) - 2 = 2 * η by ring] at hh
  convert hh using 1
  field_simp
  ring

/-- A moving line with no implicit dependence on X or on either interval endpoint. -/
theorem actual_moving_right_error_moment_le {δ : ℝ} (hδ : 0 < δ)
    {X : ℕ} (hX : 2 ≤ X) {H T : ℝ} (hHT : H ≤ T) :
    (∫ t in H..T,
      ‖riemannZeta (((1 + δ / Real.log X : ℝ) : ℂ) + I * t) *
        mollifier X (((1 + δ / Real.log X : ℝ) : ℂ) + I * t) - 1‖ ^ 2) ≤
      Real.exp (-2 * δ) * (1 + Real.log X / δ) ^ 2 *
        ((T - H) / ((X : ℝ) * (1 + 2 * δ / Real.log X)) +
          26 * Real.log X / δ) := by
  have hx : (1 : ℝ) < X := by exact_mod_cast hX
  have hl : 0 < Real.log (X : ℝ) := Real.log_pos hx
  have hh := actual_right_error_moment_gap_le (div_pos hδ hl) (by omega : 1 ≤ X) hHT
  have he : (X : ℝ) ^ (-(2 * (δ / Real.log X))) = Real.exp (-2 * δ) := by
    rw [Real.rpow_def_of_pos (by linarith : (0 : ℝ) < X)]
    congr 1
    field_simp
  rw [he] at hh
  convert hh using 1
  field_simp

def movingRightMomentConstant (δ : ℝ) : ℝ :=
  Real.exp (-2 * δ) * (1 + 1 / δ) ^ 2 * (1 + 26 / δ)

theorem movingRightMomentConstant_pos {δ : ℝ} (hδ : 0 < δ) :
    0 < movingRightMomentConstant δ := by
  unfold movingRightMomentConstant
  positivity

/-- One explicit constant for every cutoff and every translated interval,
including intervals shorter than the mollifier cutoff. -/
theorem actual_moving_right_error_moment_log_cube_le {δ : ℝ} (hδ : 0 < δ)
    {X : ℕ} (hX : 2 ≤ X) {H T : ℝ} (hHT : H ≤ T) :
    (∫ t in H..T,
      ‖riemannZeta (((1 + δ / Real.log X : ℝ) : ℂ) + I * t) *
        mollifier X (((1 + δ / Real.log X : ℝ) : ℂ) + I * t) - 1‖ ^ 2) ≤
      movingRightMomentConstant δ * (1 + (T - H) / X) * (1 + Real.log X) ^ 3 := by
  have hx : (1 : ℝ) < X := by exact_mod_cast hX
  have hx0 : (0 : ℝ) < X := by linarith
  have hl : 0 < Real.log (X : ℝ) := Real.log_pos hx
  have hv : 0 ≤ (T - H) / (X : ℝ) := div_nonneg (sub_nonneg.mpr hHT) hx0.le
  have hu : 0 ≤ 1 / δ := by positivity
  have hden : (X : ℝ) ≤ X * (1 + 2 * δ / Real.log X) := by
    have hh : 0 ≤ 2 * δ / Real.log X := by positivity
    nlinarith [mul_nonneg (Nat.cast_nonneg X) hh]
  have hfrac := div_le_div_of_nonneg_left (sub_nonneg.mpr hHT) hx0 hden
  have hlinear : 1 + Real.log X / δ ≤ (1 + 1 / δ) * (1 + Real.log X) := by
    rw [div_eq_mul_inv, one_div] at *
    nlinarith
  let B : ℝ := (1 + (T - H) / X) * (1 + Real.log X)
  have hvB : (T - H) / (X : ℝ) ≤ B := by
    dsimp [B]
    nlinarith [mul_nonneg hv hl.le]
  have hlB : Real.log X ≤ B := by
    dsimp [B]
    nlinarith [mul_nonneg hv hl.le]
  have hsecond : (T - H) / (X : ℝ) + 26 * Real.log X / δ ≤
      (1 + 26 / δ) * B := by
    have hh := mul_le_mul_of_nonneg_left hlB (by positivity : (0 : ℝ) ≤ 26 / δ)
    calc
      _ = (T - H) / (X : ℝ) + (26 / δ) * Real.log X := by ring
      _ ≤ B + (26 / δ) * B := add_le_add hvB hh
      _ = _ := by ring
  calc
    _ ≤ Real.exp (-2 * δ) * (1 + Real.log X / δ) ^ 2 *
        ((T - H) / ((X : ℝ) * (1 + 2 * δ / Real.log X)) + 26 * Real.log X / δ) :=
      actual_moving_right_error_moment_le hδ hX hHT
    _ ≤ Real.exp (-2 * δ) * (1 + Real.log X / δ) ^ 2 *
        ((T - H) / X + 26 * Real.log X / δ) :=
      mul_le_mul_of_nonneg_left (add_le_add hfrac le_rfl) (by positivity)
    _ ≤ Real.exp (-2 * δ) * ((1 + 1 / δ) * (1 + Real.log X)) ^ 2 *
        ((1 + 26 / δ) * B) :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hlinear 2)
          (Real.exp_pos _).le)
        hsecond (by positivity) (by positivity)
    _ = _ := by unfold movingRightMomentConstant B; ring

end RiemannResearch.Analysis.InghamMollifier
