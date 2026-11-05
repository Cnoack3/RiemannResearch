/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeDisplacementResolvent
import RiemannResearch.RH.QMeanSquareDisplacement
import RiemannResearch.RH.QSquarefreeChebyshev
import RiemannResearch.Analysis.ChebyshevScale
/-!
# Finite averaging criteria for centered and accelerated resolvents
Source: the user's four-criteria continuation, 5 November 2026.
One physical mean-square bound per iteration, on heads 9^j or 33^j,
suffices for Mathlib's RiemannHypothesis. Those mean bounds remain OPEN.
-/
noncomputable section

namespace RiemannResearch.RH.QSquarefreeChebyshev
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeDisplacementRigidity
open QSquarefreeDisplacementResolvent QMeanSquareDisplacement
open RiemannResearch.Analysis.ChebyshevEnergy

/-- Scaled squared error for the original centered resolvent, as used in
riemannHypothesis_of_resolvent_mean_square. -/
theorem resolvent_nine_head_error (j : ℕ) :
    ((9 ^ j : ℕ) : ℝ) * ‖displacement - resolventApprox j‖ ^ 2 ≤ ‖displacement‖ ^ 2 := by
  have hn := resolvent_error_norm_le j
  have hpos : 0 ≤ (1 / 3 : ℝ) ^ j * ‖displacement‖ := by positivity
  have hsq : ‖displacement - resolventApprox j‖ ^ 2 ≤
      ((1 / 3 : ℝ) ^ j * ‖displacement‖) ^ 2 := by
    nlinarith [norm_nonneg (displacement - resolventApprox j)]
  have hscale : (9 : ℝ) ^ j * ((1 / 3 : ℝ) ^ j) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm j 2, pow_mul, ← mul_pow]
    norm_num
  calc
    _ ≤ ((9 ^ j : ℕ) : ℝ) * ((1 / 3 : ℝ) ^ j * ‖displacement‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _)
    _ = ‖displacement‖ ^ 2 := by
      simp only [Nat.cast_pow, Nat.cast_ofNat, mul_pow, ← mul_assoc, hscale, one_mul]

theorem riemannHypothesis_of_resolvent_mean_square
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ j, headEnergy (9 ^ j) (resolventApprox j) ≤ C * ((9 ^ j : ℕ) : ℝ)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_geometric_head_means 9 (by norm_num)
    resolventApprox C (‖displacement‖ ^ 2) hC (sq_nonneg _) hb
  exact resolvent_nine_head_error

theorem accelerated_head33_error (j : ℕ) :
    ((33 ^ j : ℕ) : ℝ) * ‖displacement - accelerated j‖ ^ 2 ≤ 4 * ‖displacement‖ ^ 2 := by
  have hroot : (33 : ℝ) ≤ 17 + 12 * Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 33) hroot j
  have hb := accelerated_head_lower_bound j
  have hhead : ((33 ^ j : ℕ) : ℝ) ≤ 4 * (denominator j) ^ 2 := by
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    linarith
  have hn := (le_div_iff₀ (denominator_pos j)).mp (accelerated_error_norm_le j)
  have he : (denominator j) ^ 2 * ‖displacement - accelerated j‖ ^ 2 ≤ ‖displacement‖ ^ 2 := by
    have hsq := mul_self_le_mul_self
      (mul_nonneg (norm_nonneg (displacement - accelerated j)) (denominator_pos j).le) hn
    nlinarith
  have hh := mul_le_mul_of_nonneg_right hhead (sq_nonneg ‖displacement - accelerated j‖)
  nlinarith

theorem riemannHypothesis_of_accelerated_mean_square
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ j, headEnergy (33 ^ j) (accelerated j) ≤ C * ((33 ^ j : ℕ) : ℝ)) :
    RiemannHypothesis :=
  riemannHypothesis_of_geometric_head_means 33 (by norm_num) accelerated
    C (4 * ‖displacement‖ ^ 2) hC (by positivity) hb accelerated_head33_error

end RiemannResearch.RH.QSquarefreeChebyshev

namespace RiemannResearch.RH.QSquarefreeChebyshev
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeDisplacementRigidity QMeanSquareDisplacement
open RiemannResearch.Analysis.ChebyshevEnergy

theorem accelerated_exact_head_error (j : ℕ) :
    (acceleratedHead j : ℝ) * ‖displacement - accelerated j‖ ^ 2 ≤ ‖displacement‖ ^ 2 := by
  rw [acceleratedHead_cast]
  have hn := (le_div_iff₀ (denominator_pos j)).mp (accelerated_error_norm_le j)
  have hs := mul_self_le_mul_self
    (mul_nonneg (norm_nonneg (displacement - accelerated j)) (denominator_pos j).le) hn
  nlinarith

theorem riemannHypothesis_of_accelerated_exact_head_mean_square
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ j, headEnergy (acceleratedHead j) (accelerated j) ≤ C * (acceleratedHead j : ℝ)) :
    RiemannHypothesis :=
  riemannHypothesis_of_covered_head_means acceleratedHead accelerated 36 C
    (‖displacement‖ ^ 2) (by norm_num) hC (sq_nonneg _)
    acceleratedHead_cover hb accelerated_exact_head_error

/-- Only the physical sites strictly above the preceding exact head occur
in the averaging hypothesis. -/
theorem riemannHypothesis_of_accelerated_annular_mean_square
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ j,
      headEnergy (acceleratedHead (j + 1)) (accelerated (j + 1)) -
        headEnergy (acceleratedHead j) (accelerated (j + 1)) ≤
          C * (acceleratedHead (j + 1) : ℝ)) : RiemannHypothesis := by
  let D : ℝ := 2 * C + 2 * zetaTwo * ‖displacement‖ ^ 2
  have hz := zetaTwo_pos
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let K : ℝ := headEnergy 1 displacement + 2 * D
  have hK : 0 ≤ K := by
    dsimp [K]
    linarith [headEnergy_nonneg 1 displacement]
  have hg (j : ℕ) :
      2 * (acceleratedHead j : ℝ) ≤ (acceleratedHead (j + 1) : ℝ) := by
    rw [acceleratedHead_cast, acceleratedHead_cast]
    have hpos := denominator_pos j
    have h := mul_self_le_mul_self
      (show 0 ≤ 3 * denominator j by positivity) (denominator_growth j).2
    nlinarith [sq_nonneg (denominator j)]
  have hd (j : ℕ) :
      headEnergy (acceleratedHead (j + 1)) displacement -
        headEnergy (acceleratedHead j) displacement ≤
          D * (acceleratedHead (j + 1) : ℝ) := by
    have hmono : acceleratedHead j ≤ acceleratedHead (j + 1) := by
      have hr : (acceleratedHead j : ℝ) ≤ (acceleratedHead (j + 1) : ℝ) := by
        linarith [hg j, Nat.cast_nonneg (α := ℝ) (acceleratedHead j)]
      exact_mod_cast hr
    have h₁ := annular_headEnergy_add_error _ _ hmono displacement (accelerated (j + 1))
    have h₂ := headEnergy_norm_le (acceleratedHead (j + 1)) (displacement - accelerated (j + 1))
    have h₃ := mul_le_mul_of_nonneg_left (accelerated_exact_head_error (j + 1))
      (show 0 ≤ zetaTwo * (acceleratedHead (j + 1) : ℝ) by positivity)
    have h₄ := hb j
    dsimp [D]
    nlinarith
  have hhead (j : ℕ) : headEnergy (acceleratedHead j) displacement ≤
      K * (acceleratedHead j : ℝ) := by
    induction j with
    | zero =>
      have hzero : acceleratedHead 0 = 1 := by norm_num [acceleratedHead, denominator]
      rw [hzero, Nat.cast_one, mul_one]
      dsimp [K]
      linarith
    | succ j ih =>
      have h₁ := mul_le_mul_of_nonneg_left (hg j) hK
      have h₂ : 2 * D ≤ K := by
        dsimp [K]
        linarith [headEnergy_nonneg 1 displacement]
      have h₃ := mul_le_mul_of_nonneg_right h₂ (Nat.cast_nonneg (α := ℝ) (acceleratedHead (j + 1)))
      nlinarith [hd j]
  apply riemannHypothesis_of_covered_head_means acceleratedHead (fun _ => displacement)
    36 K 0 (by norm_num) hK le_rfl acceleratedHead_cover hhead
  simp

end RiemannResearch.RH.QSquarefreeChebyshev
