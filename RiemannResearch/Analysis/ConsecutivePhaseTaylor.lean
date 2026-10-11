/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.OrdinateLagPhase
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Exact consecutive-phase Taylor transport

Source: user-provided argument, developed from Ford--Zaharescu,
https://ford126.web.illinois.edu/wwwpapers/fz.pdf, equation (3.8), and
Fujii's gap moments as recorded in Ivić, https://arxiv.org/pdf/1610.01317,
equation (1.2). Those sources motivate the asymptotic applications;
this module proves finite identities and estimates directly. It does not
assume their zeta-distribution conclusions and does not assume RH.

The complete signed Taylor defects and endpoint terms are retained first.
Global numerical constants 2 and 3 are convenient, nonoptimal constants.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.OrdinateLagPhase

/-- The exact remainder after the constant and linear phase terms. -/
def phaseLinearDefect (t : ℝ) : ℂ :=
  phase 1 t - 1 - Complex.I * (t : ℂ)

/-- The exact remainder after the quadratic phase term. -/
def phaseQuadraticDefect (t : ℝ) : ℂ :=
  phaseLinearDefect t + ((t ^ 2 / 2 : ℝ) : ℂ)

/-- A direct global Taylor provider, with a nonoptimal constant. -/
theorem norm_phaseLinearDefect_le (t : ℝ) :
    ‖phaseLinearDefect t‖ ≤ 2 * t ^ 2 := by
  by_cases ht : |t| ≤ 1
  · have h := Complex.norm_exp_sub_one_sub_id_le
      (x := Complex.I * (t : ℂ)) (by simpa using ht)
    have h' : ‖phaseLinearDefect t‖ ≤ t ^ 2 := by
      simpa [phaseLinearDefect, phase, sq_abs] using h
    nlinarith [sq_nonneg t]
  · have ht' : 1 ≤ |t| := le_of_lt (lt_of_not_ge ht)
    have h : ‖phaseLinearDefect t‖ ≤ 2 * |t| := by
      calc
        ‖phaseLinearDefect t‖ ≤
            ‖phase 1 t - 1‖ + ‖Complex.I * (t : ℂ)‖ := norm_sub_le _ _
        _ ≤ |t| + |t| := by
          apply add_le_add
          · simpa [phase, Real.norm_eq_abs] using
              (Real.norm_exp_I_mul_ofReal_sub_one_le (x := t))
          · simp
        _ = 2 * |t| := by ring
    have hs : |t| ^ 2 = t ^ 2 := sq_abs t
    nlinarith [sq_nonneg (|t| - 1)]

/-- A global cubic Taylor provider. No bounded-gap hypothesis is needed. -/
theorem norm_phaseQuadraticDefect_le (t : ℝ) :
    ‖phaseQuadraticDefect t‖ ≤ 3 * |t| ^ 3 := by
  by_cases ht : |t| ≤ 1
  · have h := Complex.exp_bound
      (x := Complex.I * (t : ℂ)) (by simpa using ht) (n := 3) (by decide)
    have hp : (∑ m ∈ Finset.range 3,
        (Complex.I * (t : ℂ)) ^ m / (m.factorial : ℂ)) =
        1 + Complex.I * (t : ℂ) - ((t ^ 2 / 2 : ℝ) : ℂ) := by
      norm_num [Finset.sum_range_succ, Nat.factorial, mul_pow, Complex.I_sq]
      ring
    rw [hp] at h
    have he : Complex.exp (Complex.I * (t : ℂ)) -
        (1 + Complex.I * (t : ℂ) - ((t ^ 2 / 2 : ℝ) : ℂ)) =
        phaseQuadraticDefect t := by
      unfold phaseQuadraticDefect phaseLinearDefect phase
      simp only [one_mul]
      ring
    rw [he] at h
    norm_num [Nat.factorial] at h
    nlinarith [pow_nonneg (abs_nonneg t) 3]
  · have ht' : 1 ≤ |t| := le_of_lt (lt_of_not_ge ht)
    have h : ‖phaseQuadraticDefect t‖ ≤ 2 * t ^ 2 + t ^ 2 / 2 := by
      calc
        ‖phaseQuadraticDefect t‖ ≤
            ‖phaseLinearDefect t‖ + ‖((t ^ 2 / 2 : ℝ) : ℂ)‖ := norm_add_le _ _
        _ ≤ 2 * t ^ 2 + t ^ 2 / 2 := by
          apply add_le_add (norm_phaseLinearDefect_le t)
          simp
    have hs : |t| ^ 2 = t ^ 2 := sq_abs t
    have hc : |t| ^ 2 ≤ |t| ^ 3 := by
      calc
        |t| ^ 2 = |t| ^ 2 * 1 := by ring
        _ ≤ |t| ^ 2 * |t| := mul_le_mul_of_nonneg_left ht' (sq_nonneg _)
        _ = |t| ^ 3 := by ring
    nlinarith [sq_nonneg t]

theorem phase_add_times (u x d : ℝ) :
    phase u (x + d) = phase u x * phase 1 (u * d) := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem consecutive_phase_factor (a b x y : ℝ) :
    phase a x * phase b y = phase (a + b) x * phase 1 (b * (y - x)) := by
  unfold phase
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The one-step exact transport identity, including its signed defect. -/
theorem consecutive_phase_transport_step (a b c x y : ℝ)
    (hc : b = c * (a + b)) :
    phase a x * phase b y = phase (a + b) x +
      (c : ℂ) * (phase (a + b) y - phase (a + b) x) +
      phase (a + b) x * (phaseLinearDefect (b * (y - x)) -
        (c : ℂ) * phaseLinearDefect ((a + b) * (y - x))) := by
  rw [consecutive_phase_factor]
  have hy : phase (a + b) y =
      phase (a + b) x * phase 1 ((a + b) * (y - x)) := by
    convert phase_add_times (a + b) x (y - x) using 1 <;> ring
  rw [hy]
  unfold phaseLinearDefect
  have hc' : (b : ℂ) = (c : ℂ) * ((a : ℂ) + (b : ℂ)) := by
    exact_mod_cast hc
  push_cast
  linear_combination phase (a + b) x * Complex.I * ((y : ℂ) - (x : ℂ)) * hc'

/-- The signed transport remainder. -/
def consecutiveTransportDefect (γ : ℕ → ℝ) (J : ℕ) (q b c : ℝ) : ℂ :=
  ∑ j ∈ Finset.range J, phase q (γ j) *
    (phaseLinearDefect (b * (γ (j + 1) - γ j)) -
      (c : ℂ) * phaseLinearDefect (q * (γ (j + 1) - γ j)))

/-- Exact finite consecutive-pair formula. Take `c = b / (a + b)` when
`a + b ≠ 0`. No monotonicity or zeta-zero hypothesis occurs. -/
theorem consecutive_phase_transport_eq (γ : ℕ → ℝ) (J : ℕ) (a b c : ℝ)
    (hc : b = c * (a + b)) :
    (∑ j ∈ Finset.range J, phase a (γ j) * phase b (γ (j + 1))) =
      (∑ j ∈ Finset.range J, phase (a + b) (γ j)) +
      (c : ℂ) * (phase (a + b) (γ J) - phase (a + b) (γ 0)) +
      consecutiveTransportDefect γ J (a + b) b c := by
  unfold consecutiveTransportDefect
  induction J with
  | zero => simp
  | succ J ih =>
    simp only [Finset.sum_range_succ]
    rw [ih, consecutive_phase_transport_step a b c (γ J) (γ (J + 1)) hc]
    ring

/-- The exact transport remainder is bounded by the squared-gap energy. -/
theorem norm_consecutiveTransportDefect_le
    (γ : ℕ → ℝ) (J : ℕ) (q b c : ℝ) :
    ‖consecutiveTransportDefect γ J q b c‖ ≤
      2 * (b ^ 2 + |c| * q ^ 2) *
        (∑ j ∈ Finset.range J, (γ (j + 1) - γ j) ^ 2) := by
  unfold consecutiveTransportDefect
  calc
    _ ≤ ∑ j ∈ Finset.range J, ‖phase q (γ j) *
        (phaseLinearDefect (b * (γ (j + 1) - γ j)) -
          (c : ℂ) * phaseLinearDefect (q * (γ (j + 1) - γ j)))‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range J,
        2 * (b ^ 2 + |c| * q ^ 2) * (γ (j + 1) - γ j) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul, norm_phase, one_mul]
      calc
        _ ≤ ‖phaseLinearDefect (b * (γ (j + 1) - γ j))‖ +
            ‖(c : ℂ) * phaseLinearDefect (q * (γ (j + 1) - γ j))‖ := norm_sub_le _ _
        _ = ‖phaseLinearDefect (b * (γ (j + 1) - γ j))‖ +
            |c| * ‖phaseLinearDefect (q * (γ (j + 1) - γ j))‖ := by simp
        _ ≤ 2 * (b * (γ (j + 1) - γ j)) ^ 2 +
            |c| * (2 * (q * (γ (j + 1) - γ j)) ^ 2) :=
          add_le_add (norm_phaseLinearDefect_le _)
            (mul_le_mul_of_nonneg_left (norm_phaseLinearDefect_le _) (abs_nonneg c))
        _ = _ := by ring
    _ = _ := by rw [Finset.mul_sum]

/-- Exact resonant expansion through the squared-gap term. -/
theorem consecutive_gap_phase_quadratic_eq (γ : ℕ → ℝ) (J : ℕ) (b : ℝ) :
    (∑ j ∈ Finset.range J, phase b (γ (j + 1) - γ j)) =
      (J : ℂ) + Complex.I * (b : ℂ) * ((γ J - γ 0 : ℝ) : ℂ) -
      ((b ^ 2 / 2 : ℝ) : ℂ) *
        (∑ j ∈ Finset.range J, (((γ (j + 1) - γ j) ^ 2 : ℝ) : ℂ)) +
      ∑ j ∈ Finset.range J, phaseQuadraticDefect (b * (γ (j + 1) - γ j)) := by
  induction J with
  | zero => simp
  | succ J ih =>
    simp only [Finset.sum_range_succ]
    rw [ih]
    unfold phaseQuadraticDefect phaseLinearDefect
    have he : phase 1 (b * (γ (J + 1) - γ J)) =
        phase b (γ (J + 1) - γ J) := by simp [phase]
    rw [he]
    push_cast
    ring

/-- The retained cubic remainder has a direct, global cubic-moment bound. -/
theorem norm_consecutive_gap_quadratic_remainder_le
    (γ : ℕ → ℝ) (J : ℕ) (b : ℝ) :
    ‖∑ j ∈ Finset.range J, phaseQuadraticDefect (b * (γ (j + 1) - γ j))‖ ≤
      3 * |b| ^ 3 * (∑ j ∈ Finset.range J, |γ (j + 1) - γ j| ^ 3) := by
  calc
    _ ≤ ∑ j ∈ Finset.range J,
        ‖phaseQuadraticDefect (b * (γ (j + 1) - γ j))‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range J, 3 * |b| ^ 3 * |γ (j + 1) - γ j| ^ 3 := by
      apply Finset.sum_le_sum
      intro j hj
      simpa [abs_mul, mul_pow, mul_assoc] using
        norm_phaseQuadraticDefect_le (b * (γ (j + 1) - γ j))
    _ = _ := by rw [Finset.mul_sum]

/-- Exact transport from the gap-weighted phase sum to its endpoints. -/
theorem gapWeightedPhaseSum_identity (γ : ℕ → ℝ) (J : ℕ) (q : ℝ) :
    phase q (γ J) - phase q (γ 0) =
      Complex.I * (q : ℂ) *
        (∑ j ∈ Finset.range J,
          ((γ (j + 1) - γ j : ℝ) : ℂ) * phase q (γ j)) +
      ∑ j ∈ Finset.range J,
        phase q (γ j) * phaseLinearDefect (q * (γ (j + 1) - γ j)) := by
  induction J with
  | zero => simp
  | succ J ih =>
    simp only [Finset.sum_range_succ]
    have he : phase q (γ (J + 1)) =
        phase q (γ J) * phase 1 (q * (γ (J + 1) - γ J)) := by
      convert phase_add_times q (γ J) (γ (J + 1) - γ J) using 1 <;> ring
    rw [he]
    unfold phaseLinearDefect at ih ⊢
    push_cast at ih ⊢
    linear_combination ih

theorem norm_gapWeightedPhaseRemainder_le (γ : ℕ → ℝ) (J : ℕ) (q : ℝ) :
    ‖∑ j ∈ Finset.range J,
      phase q (γ j) * phaseLinearDefect (q * (γ (j + 1) - γ j))‖ ≤
      2 * q ^ 2 * (∑ j ∈ Finset.range J, (γ (j + 1) - γ j) ^ 2) := by
  calc
    _ ≤ ∑ j ∈ Finset.range J,
        ‖phase q (γ j) * phaseLinearDefect (q * (γ (j + 1) - γ j))‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range J, 2 * q ^ 2 * (γ (j + 1) - γ j) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul, norm_phase, one_mul]
      simpa [mul_pow, mul_assoc] using
        norm_phaseLinearDefect_le (q * (γ (j + 1) - γ j))
    _ = _ := by rw [Finset.mul_sum]

/-- A nonzero-frequency gap-weighted phase estimate. The endpoint contribution
`2` and the full squared-gap energy are both retained. -/
theorem norm_gapWeightedPhaseSum_le (γ : ℕ → ℝ) (J : ℕ) (q : ℝ) (hq : q ≠ 0) :
    ‖∑ j ∈ Finset.range J,
      ((γ (j + 1) - γ j : ℝ) : ℂ) * phase q (γ j)‖ ≤
      (2 + 2 * q ^ 2 * (∑ j ∈ Finset.range J, (γ (j + 1) - γ j) ^ 2)) / |q| := by
  have he := gapWeightedPhaseSum_identity γ J q
  have he' : Complex.I * (q : ℂ) *
        (∑ j ∈ Finset.range J,
          ((γ (j + 1) - γ j : ℝ) : ℂ) * phase q (γ j)) =
      (phase q (γ J) - phase q (γ 0)) -
        ∑ j ∈ Finset.range J,
          phase q (γ j) * phaseLinearDefect (q * (γ (j + 1) - γ j)) := by
    exact (eq_sub_iff_add_eq).2 he.symm
  have hmul : |q| * ‖∑ j ∈ Finset.range J,
      ((γ (j + 1) - γ j : ℝ) : ℂ) * phase q (γ j)‖ ≤
      2 + 2 * q ^ 2 * (∑ j ∈ Finset.range J, (γ (j + 1) - γ j) ^ 2) := by
    calc
      _ = ‖Complex.I * (q : ℂ) *
          (∑ j ∈ Finset.range J,
            ((γ (j + 1) - γ j : ℝ) : ℂ) * phase q (γ j))‖ := by simp
      _ ≤ ‖phase q (γ J) - phase q (γ 0)‖ +
          ‖∑ j ∈ Finset.range J,
            phase q (γ j) * phaseLinearDefect (q * (γ (j + 1) - γ j))‖ := by
        rw [he']
        exact norm_sub_le _ _
      _ ≤ 2 + 2 * q ^ 2 * (∑ j ∈ Finset.range J, (γ (j + 1) - γ j) ^ 2) := by
        apply add_le_add _ (norm_gapWeightedPhaseRemainder_le γ J q)
        calc
          _ ≤ ‖phase q (γ J)‖ + ‖phase q (γ 0)‖ := norm_sub_le _ _
          _ = 2 := by simp only [norm_phase]; norm_num
  apply (le_div_iff₀ (abs_pos.mpr hq)).mpr
  simpa [mul_comm] using hmul

end RiemannResearch.Analysis.OrdinateLagPhase
