/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.DirichletPolynomialMeanValue
import RiemannResearch.Analysis.ActualInghamCriticalMoment
import RiemannResearch.Analysis.ActualMobiusZeroDetector
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import RiemannResearch.Analysis.FiniteTwistedMoment
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# The unconditional actual Ingham mollifier second moment

Source: the uploaded Ingham/Z03 remaining-obligations note, obligation I2.
The analytic target follows Chourasiya--Simonic,
https://arxiv.org/html/2507.15184v2, Section 4. The Gaussian majorant and
coefficient-energy proof here discharge the actual finite-mollifier input.

The exact signed interval identity precedes the estimates. The explicit
constant is independent of the cutoff and height. A translated-interval
version retains the actual interval length, and the mixed 4/3 moment now
requires only the actual zeta fourth-moment integral.

No asymptotic fourth-moment provider, global Ingham density provider, or
near-line Selberg provider is assumed or proved by the mollifier bound.
-/
noncomputable section
open MeasureTheory Complex Set
open scoped BigOperators


namespace RiemannResearch.Analysis.InghamMollifier
def criticalCoefficient (n : ℕ) : ℂ :=
  (ArithmeticFunction.moebius n : ℂ) * Complex.exp (-(1 / 2 : ℂ) * (Real.log n : ℂ))

theorem mollifier_critical_exp_sum (X : ℕ) (t : ℝ) :
    mollifier X ((1 / 2 : ℂ) + Complex.I * t) =
      ∑ n ∈ Finset.Icc 1 X, criticalCoefficient n *
        Complex.exp (Complex.I * t * (-Real.log n)) := by
  unfold mollifier criticalCoefficient
  apply Finset.sum_congr rfl
  intro n hn
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Exact signed interval identity, retaining every off-diagonal term. -/
theorem mollifier_second_moment_identity (X : ℕ) (T : ℝ) :
    ((∫ t in (0 : ℝ)..T, ‖mollifier X ((1 / 2 : ℂ) + Complex.I * t)‖ ^ 2 : ℝ) : ℂ) =
      (((∑ n ∈ Finset.Icc 1 X, ‖criticalCoefficient n‖ ^ 2) * T : ℝ) : ℂ) +
      Complex.finiteTwistedOffDiagonal (Finset.Icc 1 X) criticalCoefficient
        (fun n => -Real.log n) (fun _ => 1) 0 T := by
  simp_rw [mollifier_critical_exp_sum]
  have h := Complex.integral_finite_sum_norm_sq_diagonal (Finset.Icc 1 X)
    criticalCoefficient (fun n => -Real.log n) (fun _ => 1) 0 T continuousOn_const
  simpa only [one_mul, norm_one, one_pow, intervalIntegral.integral_const,
    sub_zero, smul_eq_mul, mul_one, Complex.ofReal_neg] using h

theorem criticalCoefficient_norm_sq_le {n : ℕ} (hn : 0 < n) :
    ‖criticalCoefficient n‖ ^ 2 ≤ 1 / (n : ℝ) := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hm : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  have he : ‖Complex.exp (-(1 / 2 : ℂ) * (Real.log n : ℂ))‖ ^ 2 = 1 / (n : ℝ) := by
    have hr : Complex.exp (-(1 / 2 : ℂ) * (Real.log n : ℂ)) =
        (Real.exp (-Real.log (n : ℝ) / 2) : ℂ) := by
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    rw [hr, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      ← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show 2 * (-Real.log (n : ℝ) / 2) = -Real.log n by ring,
      Real.exp_neg, Real.exp_log hn0]
    simp only [one_div]
  unfold criticalCoefficient
  rw [norm_mul, mul_pow, he]
  have hb := pow_le_pow_left₀ (norm_nonneg _) hm 2
  calc
    _ ≤ 1 ^ 2 * (1 / (n : ℝ)) := mul_le_mul_of_nonneg_right hb (by positivity)
    _ = _ := by ring

theorem criticalCoefficient_energy_le (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, ‖criticalCoefficient n‖ ^ 2) ≤ 1 + Real.log X := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 X, 1 / (n : ℝ) := Finset.sum_le_sum (fun n hn =>
      criticalCoefficient_norm_sq_le (by have hh := (Finset.mem_Icc.mp hn).1; omega))
    _ = (harmonic X : ℝ) := by simp [harmonic_eq_sum_Icc, one_div]
    _ ≤ _ := harmonic_le_one_add_log X

/-- An unconditional actual-mollifier mean value, uniform in both parameters. -/
theorem mollifier_second_moment_le {X : ℕ} (hX : 1 ≤ X) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖mollifier X ((1 / 2 : ℂ) + Complex.I * t)‖ ^ 2) ≤
      (12 * Real.sqrt (2 * Real.pi) * Real.exp (1 / 2 : ℝ)) * (T + X) *
        (1 + Real.log X) := by
  simp_rw [mollifier_critical_exp_sum]
  exact (dirichlet_polynomial_second_moment_le X criticalCoefficient hT (by omega)).trans
    (mul_le_mul_of_nonneg_left (criticalCoefficient_energy_le X) (by positivity))

/-- The precise logarithmic shape requested by obligation I2. -/
theorem mollifier_second_moment_log_two_mul_le {X : ℕ} (hX : 1 ≤ X) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖mollifier X ((1 / 2 : ℂ) + Complex.I * t)‖ ^ 2) ≤
      (36 * Real.sqrt (2 * Real.pi) * Real.exp (1 / 2 : ℝ)) * (T + X) *
        Real.log (2 * (X : ℝ)) := by
  have hXr : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hlX : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX)
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hb : 1 + Real.log X ≤ 3 * Real.log (2 * (X : ℝ)) := by
    rw [Real.log_mul (by norm_num) hXr.ne']
    linarith
  calc
    _ ≤ (12 * Real.sqrt (2 * Real.pi) * Real.exp (1 / 2 : ℝ)) * (T + X) *
        (1 + Real.log X) := mollifier_second_moment_le hX hT
    _ ≤ (12 * Real.sqrt (2 * Real.pi) * Real.exp (1 / 2 : ℝ)) * (T + X) *
        (3 * Real.log (2 * (X : ℝ))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

theorem exists_mollifier_second_moment_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 2 ≤ X → ∀ T : ℝ, 2 ≤ T →
      (∫ t in (0 : ℝ)..T, ‖mollifier X ((1 / 2 : ℂ) + Complex.I * t)‖ ^ 2) ≤
        C * (T + X) * Real.log (2 * (X : ℝ)) := by
  refine ⟨36 * Real.sqrt (2 * Real.pi) * Real.exp (1 / 2 : ℝ), by positivity, ?_⟩
  intro X hX T hT
  exact mollifier_second_moment_log_two_mul_le (by omega) (by linarith)

/-- Uniform on every translated interval, with its actual length. -/
theorem mollifier_second_moment_window_le {X : ℕ} (hX : 1 ≤ X) {H T : ℝ}
    (hHT : H ≤ T) :
    (∫ t in H..T, ‖mollifier X ((1 / 2 : ℂ) + Complex.I * t)‖ ^ 2) ≤
      (12 * Real.sqrt (2 * Real.pi) * Real.exp (1 / 2 : ℝ)) * (T - H + X) *
        (1 + Real.log X) := by
  simp_rw [mollifier_critical_exp_sum]
  exact (dirichlet_polynomial_second_moment_window_le X criticalCoefficient hHT (by omega)).trans
    (mul_le_mul_of_nonneg_left (criticalCoefficient_energy_le X) (by positivity))

/-- Only the actual zeta fourth moment remains on the right-hand side. -/
theorem critical_error_moment_le_fourth_moment {X : ℕ} (hX : 1 ≤ X) {H T : ℝ}
    (hHT : H ≤ T) :
    (∫ t in H..T, ‖riemannZeta ((1 / 2 : ℂ) + Complex.I * t) *
      mollifier X ((1 / 2 : ℂ) + Complex.I * t) - 1‖ ^ (4 / 3 : ℝ)) ≤
      (2 : ℝ) ^ (1 / 3 : ℝ) *
        ((∫ t in H..T, ‖riemannZeta ((1 / 2 : ℂ) + Complex.I * t)‖ ^ 4) ^ (1 / 3 : ℝ) *
          ((12 * Real.sqrt (2 * Real.pi) * Real.exp (1 / 2 : ℝ)) * (T - H + X) *
            (1 + Real.log X)) ^ (2 / 3 : ℝ) + (T - H)) := by
  apply (critical_error_moment_le X hHT).trans
  have hm := mollifier_second_moment_window_le hX hHT
  have hnon : 0 ≤ ∫ t in H..T, ‖mollifier X ((1 / 2 : ℂ) + Complex.I * t)‖ ^ 2 :=
    intervalIntegral.integral_nonneg hHT (fun _ _ => sq_nonneg _)
  have hp := Real.rpow_le_rpow hnon hm (by norm_num : (0 : ℝ) ≤ 2 / 3)
  have hz0 : 0 ≤ ∫ t in H..T, ‖riemannZeta ((1 / 2 : ℂ) + Complex.I * t)‖ ^ 4 :=
    intervalIntegral.integral_nonneg hHT (fun _ _ => by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add _ le_rfl
  exact mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hz0 _)
end RiemannResearch.Analysis.InghamMollifier
