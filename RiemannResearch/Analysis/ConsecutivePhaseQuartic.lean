/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConsecutivePhaseTaylor

/-!
# The exact squared-gap contribution to consecutive cosine correlation

Source: the user-provided consecutive-phase argument. This retains the
quartic remainder separately; no asymptotic gap-moment theorem is assumed.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.OrdinateLagPhase

/-- The exact remainder after the cubic phase term. -/
def phaseCubicDefect (t : ℝ) : ℂ :=
  phaseQuadraticDefect t + Complex.I * ((t ^ 3 / 6 : ℝ) : ℂ)

theorem norm_phaseCubicDefect_le (t : ℝ) :
    ‖phaseCubicDefect t‖ ≤ 4 * |t| ^ 4 := by
  by_cases ht : |t| ≤ 1
  · have h := Complex.exp_bound
      (x := Complex.I * (t : ℂ)) (by simpa using ht) (n := 4) (by decide)
    have hp : (∑ m ∈ Finset.range 4,
        (Complex.I * (t : ℂ)) ^ m / (m.factorial : ℂ)) =
        1 + Complex.I * (t : ℂ) - ((t ^ 2 / 2 : ℝ) : ℂ) -
          Complex.I * ((t ^ 3 / 6 : ℝ) : ℂ) := by
      norm_num [Finset.sum_range_succ, Nat.factorial, mul_pow, pow_succ, Complex.I_sq]
      push_cast
      ring
    rw [hp] at h
    have he : Complex.exp (Complex.I * (t : ℂ)) -
        (1 + Complex.I * (t : ℂ) - ((t ^ 2 / 2 : ℝ) : ℂ) -
          Complex.I * ((t ^ 3 / 6 : ℝ) : ℂ)) = phaseCubicDefect t := by
      unfold phaseCubicDefect phaseQuadraticDefect phaseLinearDefect phase
      simp only [one_mul]
      ring
    rw [he] at h
    norm_num [Nat.factorial] at h
    nlinarith [pow_nonneg (abs_nonneg t) 4]
  · have ht' : 1 ≤ |t| := le_of_lt (lt_of_not_ge ht)
    have h : ‖phaseCubicDefect t‖ ≤ 3 * |t| ^ 3 + |t| ^ 3 / 6 := by
      calc
        ‖phaseCubicDefect t‖ ≤ ‖phaseQuadraticDefect t‖ +
            ‖Complex.I * ((t ^ 3 / 6 : ℝ) : ℂ)‖ := norm_add_le _ _
        _ ≤ 3 * |t| ^ 3 + |t| ^ 3 / 6 := by
          apply add_le_add (norm_phaseQuadraticDefect_le t)
          simp [abs_div, abs_pow]
    have hc : |t| ^ 3 ≤ |t| ^ 4 := by
      calc
        |t| ^ 3 = |t| ^ 3 * 1 := by ring
        _ ≤ |t| ^ 3 * |t| :=
          mul_le_mul_of_nonneg_left ht' (pow_nonneg (abs_nonneg _) 3)
        _ = |t| ^ 4 := by ring
    nlinarith [pow_nonneg (abs_nonneg t) 3]

/-- The cubic term is purely imaginary, so the real defect starts at order
four. This equality retains its sign. -/
theorem phase_cosine_defect_eq (t : ℝ) :
    1 - (phase 1 t).re = t ^ 2 / 2 - (phaseCubicDefect t).re := by
  simp only [phaseCubicDefect, phaseQuadraticDefect, phaseLinearDefect,
    Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, add_zero]
  ring

/-- Exact finite cosine defect, with squared-gap and quartic-defect sums. -/
theorem consecutive_cosine_defect_eq (γ : ℕ → ℝ) (J : ℕ) (b : ℝ) :
    (∑ j ∈ Finset.range J, (1 - (phase b (γ (j + 1) - γ j)).re)) =
      b ^ 2 / 2 * (∑ j ∈ Finset.range J, (γ (j + 1) - γ j) ^ 2) -
        ∑ j ∈ Finset.range J, (phaseCubicDefect (b * (γ (j + 1) - γ j))).re := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have h := phase_cosine_defect_eq (b * (γ (j + 1) - γ j))
  have he : phase 1 (b * (γ (j + 1) - γ j)) =
      phase b (γ (j + 1) - γ j) := by simp [phase]
  rw [he] at h
  rw [h]
  ring

theorem norm_consecutive_quartic_remainder_le
    (γ : ℕ → ℝ) (J : ℕ) (b : ℝ) :
    ‖∑ j ∈ Finset.range J, phaseCubicDefect (b * (γ (j + 1) - γ j))‖ ≤
      4 * |b| ^ 4 * (∑ j ∈ Finset.range J, |γ (j + 1) - γ j| ^ 4) := by
  calc
    _ ≤ ∑ j ∈ Finset.range J,
        ‖phaseCubicDefect (b * (γ (j + 1) - γ j))‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range J, 4 * |b| ^ 4 * |γ (j + 1) - γ j| ^ 4 := by
      apply Finset.sum_le_sum
      intro j hj
      simpa [abs_mul, mul_pow, mul_assoc] using
        norm_phaseCubicDefect_le (b * (γ (j + 1) - γ j))
    _ = _ := by rw [Finset.mul_sum]

end RiemannResearch.Analysis.OrdinateLagPhase
