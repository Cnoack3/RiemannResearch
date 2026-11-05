/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QDisplacementPolylogHeadMeans
import RiemannResearch.RH.QSquarefreeChebyshevAveraging
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
Polylogarithmic mean-square budgets for the resolvent and Chebyshev schemes
of FourCriteriaContinuation20261105.md.
-/
noncomputable section
namespace RiemannResearch.RH.QSquarefreeChebyshev
open ZetaTwoHilbert QMeanSquareDisplacement QSquarefreeDisplacementRigidity
open QSquarefreeDisplacementResolvent
open RiemannResearch.Analysis.ChebyshevEnergy

/-- The exact Chebyshev heads allow any fixed polylogarithmic inflation in
the mean square required from the accelerated approximant. -/
theorem riemannHypothesis_of_accelerated_polylog_mean_square
    (m : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ j, headEnergy (acceleratedHead j) (accelerated j) ≤
      C * (acceleratedHead j : ℝ) * (6 + Real.log (acceleratedHead j : ℝ)) ^ (2 * m)) :
    RiemannHypothesis :=
  riemannHypothesis_of_covered_polylog_head_means acceleratedHead accelerated 36 C
    (‖displacement‖ ^ 2) m (by norm_num) hC (sq_nonneg _) acceleratedHead_cover h
    accelerated_exact_head_error

theorem riemannHypothesis_of_resolvent_polylog_mean_square
    (m : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ j, headEnergy (9 ^ j) (resolventApprox j) ≤
      C * ((9 ^ j : ℕ) : ℝ) * (6 + Real.log ((9 ^ j : ℕ) : ℝ)) ^ (2 * m)) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_covered_polylog_head_means (fun j => 9 ^ j)
    resolventApprox 9 C (‖displacement‖ ^ 2) m (by norm_num) hC (sq_nonneg _) ?_ h
    resolvent_nine_head_error
  intro N hN
  obtain ⟨j, hj, hmax⟩ := geometric_head_cover 9 N (by norm_num) hN
  exact ⟨j, hj, by exact_mod_cast hmax⟩

/-- The polynomial family identified in the leakage/Chebyshev catalogue:
the head and its allowed mean square both grow by (j+1)^p. -/
theorem riemannHypothesis_of_accelerated_polynomial_heads
    (p : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ j, headEnergy (acceleratedHead j * (j + 1) ^ p) (accelerated j) ≤
      C * ((acceleratedHead j * (j + 1) ^ p : ℕ) : ℝ) * ((j : ℝ) + 1) ^ p) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_accelerated_polylog_mean_square p C hC
  intro j
  let H := acceleratedHead j
  have hmul : 1 ≤ (j + 1) ^ p := by
    have hp : 0 < (j + 1) ^ p := by positivity
    omega
  have hhead : H ≤ H * (j + 1) ^ p := by
    calc
      H = H * 1 := by simp
      _ ≤ H * (j + 1) ^ p := Nat.mul_le_mul_left H hmul
  have hpow : 1 ≤ (3 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hden := denominator_ge_pow j
  have hlower : (3 : ℝ) ^ j ≤ (H : ℝ) := by
    dsimp [H]
    rw [acceleratedHead_cast]
    nlinarith [mul_nonneg (sub_nonneg.mpr (hpow.trans hden))
      (show 0 ≤ denominator j by exact (denominator_pos j).le)]
  have hlog := Real.log_le_log (show 0 < (3 : ℝ) ^ j by positivity) hlower
  rw [Real.log_pow] at hlog
  have hl3 : (1 : ℝ) ≤ Real.log 3 := by linarith [Real.log_three_gt_d9]
  have hLj : (j : ℝ) + 1 ≤ 6 + Real.log (H : ℝ) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) j) (sub_nonneg.mpr hl3)]
  have hcomp := pow_le_pow_left₀ (show (0 : ℝ) ≤ (j : ℝ) + 1 by positivity) hLj (2 * p)
  have hbudget := hb j
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one] at hbudget
  calc
    headEnergy H (accelerated j) ≤ headEnergy (H * (j + 1) ^ p) (accelerated j) :=
      headEnergy_mono (accelerated j) hhead
    _ ≤ C * ((H : ℝ) * ((j : ℝ) + 1) ^ p) * ((j : ℝ) + 1) ^ p := hbudget
    _ = C * (H : ℝ) * ((j : ℝ) + 1) ^ (2 * p) := by rw [two_mul, pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcomp (by positivity)

end RiemannResearch.RH.QSquarefreeChebyshev
