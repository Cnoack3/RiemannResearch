/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QAnnihilatorTailEscape
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import RiemannResearch.Analysis.ResidualizedProjectionKernel
import RiemannResearch.RH.QSquarefreeCorrectionKernel
import RiemannResearch.RH.QShiftedReciprocalTail
import RiemannResearch.RH.QUniformTail
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Lower-site localization of the actual squarefree correction

Source: direct centered-kernel analysis of the user's signed regularity handoff.
The complete upper tail is controlled unconditionally. The finite lower-site
response is still an open arithmetic regularity obligation.
-/

noncomputable section
namespace RiemannResearch.RH.QSquarefreeCorrectionKernel
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage QShiftedReciprocal
open QAnnihilatorTailEscape QFiniteSupportDualCriterion
open RiemannResearch.Analysis.ResidualizedProjectionKernel

theorem evaluation_norm_sq (n : ℕ) :
    ‖evaluation (n + 1)‖ ^ 2 = zetaTwo * ((n : ℝ) + 1) ^ 2 := by
  calc
    ‖evaluation (n + 1)‖ ^ 2 =
        inner ℝ (evaluation (n + 1)) (evaluation (n + 1)) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = qSequence (evaluation (n + 1)) (n + 1) := inner_evaluation _ _
    _ = (1 / Real.sqrt (qWeight n)) / Real.sqrt (qWeight n) := by
      simp [evaluation, lp.single_apply]
    _ = 1 / qWeight n := by
      rw [div_div, ← pow_two, Real.sq_sqrt (qWeight_pos n).le]
    _ = zetaTwo * ((n : ℝ) + 1) ^ 2 := by
      simp [qWeight, positiveQWeight]

theorem kernel_norm_sq_le (N n : ℕ) :
    ‖kernel N (n + 1)‖ ^ 2 ≤ zetaTwo * ((n : ℝ) + 1) ^ 2 := by
  have h := sq_nonneg ‖evaluation (n + 1) -
    (stage N).starProjection (evaluation (n + 1))‖
  rw [residual_norm_sq, evaluation_norm_sq] at h
  change ‖(stage N).starProjection (evaluation (n + 1))‖ ^ 2 ≤ _
  linarith

/-- Uniform complete upper-tail localization for the centered evaluation kernel.
The open arithmetic localization problem is confined to physical sites m < n+1. -/
theorem centeredKernel_upperTail_energy_le (N n : ℕ) :
    ‖tail n (B (kernel N (n + 1)) -
      (1 / ((n : ℝ) + 2)) • kernel N (n + 1))‖ ^ 2 ≤ zetaTwo := by
  calc
    _ ≤ (1 / ((n : ℝ) + 2)) ^ 2 * ‖kernel N (n + 1)‖ ^ 2 :=
      centered_upperTail_energy_le _ _
    _ ≤ (1 / ((n : ℝ) + 2)) ^ 2 * (zetaTwo * ((n : ℝ) + 1) ^ 2) :=
      mul_le_mul_of_nonneg_left (kernel_norm_sq_le N n) (sq_nonneg _)
    _ = zetaTwo * ((n : ℝ) + 1) ^ 2 / ((n : ℝ) + 2) ^ 2 := by
      field_simp
    _ ≤ zetaTwo := by
      apply (div_le_iff₀ (sq_pos_of_pos (by positivity : 0 < (n : ℝ) + 2))).mpr
      exact mul_le_mul_of_nonneg_left
        (by nlinarith [Nat.cast_nonneg (α := ℝ) n]) zetaTwo_pos.le

/-- The entire upper-triangular signed contribution is controlled by the
residual's complete tail, not its full norm. -/
theorem centeredKernel_upperTail_pairing_sq_le (N n : ℕ) (r : QHilbert) :
    (inner ℝ (tail n r)
      (tail n (B (kernel N (n + 1)) -
        (1 / ((n : ℝ) + 2)) • kernel N (n + 1)))) ^ 2 ≤
      zetaTwo * ‖tail n r‖ ^ 2 := by
  let u := tail n (B (kernel N (n + 1)) -
    (1 / ((n : ℝ) + 2)) • kernel N (n + 1))
  have h := abs_real_inner_le_norm (tail n r) u
  have hs := mul_self_le_mul_self (abs_nonneg (inner ℝ (tail n r) u)) h
  have hsq : (inner ℝ (tail n r) u) ^ 2 ≤ ‖tail n r‖ ^ 2 * ‖u‖ ^ 2 := by
    nlinarith [sq_abs (inner ℝ (tail n r) u)]
  calc
    _ ≤ ‖tail n r‖ ^ 2 * ‖u‖ ^ 2 := hsq
    _ ≤ ‖tail n r‖ ^ 2 * zetaTwo :=
      mul_le_mul_of_nonneg_left (centeredKernel_upperTail_energy_le N n) (sq_nonneg _)
    _ = _ := by ring

/-- The exact physical correction splits into a finite lower-site sum and a
complete upper-tail contribution. The kernel's physical diagonal vanishes. -/
theorem movingCorrection_lowerHead_upperTail (N n : ℕ) :
    qSequence (QSquarefreeSmoothedProjection.movingCorrection N) (n + 1) =
      inner ℝ (residual N)
        (finiteHead n (B (kernel N (n + 1)) -
          (1 / ((n : ℝ) + 2)) • kernel N (n + 1))) +
      inner ℝ (tail n (residual N))
        (tail n (B (kernel N (n + 1)) -
          (1 / ((n : ℝ) + 2)) • kernel N (n + 1))) := by
  rw [movingCorrection_eq_centered_pairing N (n + 1) (1 / ((n : ℝ) + 2))]
  let u := B (kernel N (n + 1)) -
    (1 / ((n : ℝ) + 2)) • kernel N (n + 1)
  have ho : inner ℝ (finiteHead n (residual N)) (tail n u) = 0 :=
    inner_finiteHead_tail n (residual N) u
  have he : inner ℝ (tail n (residual N)) (tail n u) =
      inner ℝ (residual N) (tail n u) := by
    change inner ℝ (residual N - finiteHead n (residual N)) (tail n u) = _
    rw [inner_sub_left, ho, sub_zero]
  change inner ℝ (residual N) u =
    inner ℝ (residual N) (finiteHead n u) +
      inner ℝ (tail n (residual N)) (tail n u)
  rw [he]
  change inner ℝ (residual N) u =
    inner ℝ (residual N) (finiteHead n u) +
      inner ℝ (residual N) (u - finiteHead n u)
  rw [inner_sub_right (residual N) u (finiteHead n u)]
  ring

/-- Only the finite lower-site response can create unbounded physical values;
the omitted complete tail has an unconditional, tail-sensitive bound. -/
theorem movingCorrection_lowerHead_remainder_sq_le (N n : ℕ) :
    (qSequence (QSquarefreeSmoothedProjection.movingCorrection N) (n + 1) -
      inner ℝ (residual N)
        (finiteHead n (B (kernel N (n + 1)) -
          (1 / ((n : ℝ) + 2)) • kernel N (n + 1)))) ^ 2 ≤
      zetaTwo * ‖tail n (residual N)‖ ^ 2 := by
  rw [movingCorrection_lowerHead_upperTail]
  simp only [add_sub_cancel_left]
  exact centeredKernel_upperTail_pairing_sq_le N n (residual N)

/-- The exact localization split retains the projected norm-square subtraction. -/
theorem kernelEnergy_lowerHead_upperTail_exact (N n : ℕ) :
    kernelEnergy N (n + 1) =
      ‖finiteHead n (B (kernel N (n + 1)) -
        (1 / ((n : ℝ) + 2)) • kernel N (n + 1))‖ ^ 2 +
      ‖tail n (B (kernel N (n + 1)) -
        (1 / ((n : ℝ) + 2)) • kernel N (n + 1))‖ ^ 2 -
      ‖(stage N).starProjection (B (kernel N (n + 1)) -
        (1 / ((n : ℝ) + 2)) • kernel N (n + 1))‖ ^ 2 := by
  rw [kernelEnergy_centered_exact N (n + 1) (1 / ((n : ℝ) + 2))]
  rw [finiteHead_norm_sq_split n
    (B (kernel N (n + 1)) - (1 / ((n : ℝ) + 2)) • kernel N (n + 1))]
  rfl

/-- An unconditional uniform bound for the upper half reduces localization
to a finite lower-site head. This does not bound that remaining head. -/
theorem kernelEnergy_le_lowerHead_add_zeta (N n : ℕ) :
    kernelEnergy N (n + 1) ≤
      ‖finiteHead n (B (kernel N (n + 1)) -
        (1 / ((n : ℝ) + 2)) • kernel N (n + 1))‖ ^ 2 + zetaTwo := by
  rw [kernelEnergy_lowerHead_upperTail_exact]
  have ht := centeredKernel_upperTail_energy_le N n
  have hp := sq_nonneg ‖(stage N).starProjection (B (kernel N (n + 1)) -
    (1 / ((n : ℝ) + 2)) • kernel N (n + 1))‖
  linarith


/-- The complete upper-site response vanishes uniformly in the stage.
This leaves the finite lower-site response as the regularity problem. -/
theorem lowerHead_response_uniform_error (ε : ℝ) (hε : 0 < ε) :
    ∃ H : ℕ, ∀ n ≥ H, ∀ N : ℕ,
      (qSequence (QSquarefreeSmoothedProjection.movingCorrection N) (n + 1) -
        inner ℝ (residual N)
          (finiteHead n (B (kernel N (n + 1)) -
            (1 / ((n : ℝ) + 2)) • kernel N (n + 1)))) ^ 2 ≤ ε := by
  obtain ⟨H, hH⟩ := uniform_tail_tightness_of_tendsto
    residual limitingResidual residual_tendsto (Real.sqrt (ε / zetaTwo))
    (Real.sqrt_pos.2 (div_pos hε zetaTwo_pos))
  refine ⟨H, ?_⟩
  intro n hn N
  have hs := hH n hn N
  have hsq : ‖tail n (residual N)‖ ^ 2 ≤ ε / zetaTwo := by
    have ht := Real.sq_sqrt (div_nonneg hε.le zetaTwo_pos.le)
    nlinarith [norm_nonneg (tail n (residual N)),
      Real.sqrt_nonneg (ε / zetaTwo)]
  have hb := mul_le_mul_of_nonneg_left hsq zetaTwo_pos.le
  have hc : zetaTwo * (ε / zetaTwo) = ε := by
    field_simp [ne_of_gt zetaTwo_pos]
  rw [hc] at hb
  exact (movingCorrection_lowerHead_remainder_sq_le N n).trans hb

end RiemannResearch.RH.QSquarefreeCorrectionKernel
