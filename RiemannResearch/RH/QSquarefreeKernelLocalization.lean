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
import Lean.Elab.Tactic.Omega

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

theorem centeredKernel_relativeTail_energy_le (N n H : ℕ) (C : ℝ)
    (hC : 1 ≤ C) (hscale : (n : ℝ) + 2 ≤ (C + 1) * ((H : ℝ) + 2)) :
    ‖tail H (B (kernel N (n + 1)) -
      (1 / ((n : ℝ) + 2)) • kernel N (n + 1))‖ ^ 2 ≤ zetaTwo * C ^ 2 := by
  calc
    _ ≤ (C / ((n : ℝ) + 2)) ^ 2 * ‖kernel N (n + 1)‖ ^ 2 :=
      centered_relativeTail_energy_le _ n H C hC hscale
    _ ≤ (C / ((n : ℝ) + 2)) ^ 2 * (zetaTwo * ((n : ℝ) + 1) ^ 2) :=
      mul_le_mul_of_nonneg_left (kernel_norm_sq_le N n) (sq_nonneg _)
    _ = zetaTwo * C ^ 2 * ((n : ℝ) + 1) ^ 2 / ((n : ℝ) + 2) ^ 2 := by
      field_simp
    _ ≤ zetaTwo * C ^ 2 := by
      apply (div_le_iff₀ (sq_pos_of_pos (by positivity : 0 < (n : ℝ) + 2))).mpr
      exact mul_le_mul_of_nonneg_left
        (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
        (mul_nonneg zetaTwo_pos.le (sq_nonneg C))

/-- Exact decomposition at any cutoff and any scalar center. -/
theorem movingCorrection_head_tail (N n H : ℕ) (a : ℝ) :
    qSequence (QSquarefreeSmoothedProjection.movingCorrection N) (n + 1) =
      inner ℝ (residual N) (finiteHead H (B (kernel N (n + 1)) - a • kernel N (n + 1))) +
      inner ℝ (tail H (residual N)) (tail H (B (kernel N (n + 1)) - a • kernel N (n + 1))) := by
  rw [movingCorrection_eq_centered_pairing N (n + 1) a]
  let u := B (kernel N (n + 1)) - a • kernel N (n + 1)
  have ho : inner ℝ (finiteHead H (residual N)) (tail H u) = 0 :=
    inner_finiteHead_tail H (residual N) u
  have he : inner ℝ (tail H (residual N)) (tail H u) =
      inner ℝ (residual N) (tail H u) := by
    change inner ℝ (residual N - finiteHead H (residual N)) (tail H u) = _
    rw [inner_sub_left, ho, sub_zero]
  change inner ℝ (residual N) u =
    inner ℝ (residual N) (finiteHead H u) +
      inner ℝ (tail H (residual N)) (tail H u)
  rw [he]
  change inner ℝ (residual N) u =
    inner ℝ (residual N) (finiteHead H u) +
      inner ℝ (residual N) (u - finiteHead H u)
  rw [inner_sub_right (residual N) u (finiteHead H u)]
  ring

theorem movingCorrection_relativeHead_remainder_sq_le (N n H : ℕ) (C : ℝ)
    (hC : 1 ≤ C) (hscale : (n : ℝ) + 2 ≤ (C + 1) * ((H : ℝ) + 2)) :
    (qSequence (QSquarefreeSmoothedProjection.movingCorrection N) (n + 1) -
      inner ℝ (residual N) (finiteHead H (B (kernel N (n + 1)) -
        (1 / ((n : ℝ) + 2)) • kernel N (n + 1)))) ^ 2 ≤
      zetaTwo * C ^ 2 * ‖tail H (residual N)‖ ^ 2 := by
  rw [movingCorrection_head_tail N n H (1 / ((n : ℝ) + 2))]
  simp only [add_sub_cancel_left]
  let u := tail H (B (kernel N (n + 1)) -
    (1 / ((n : ℝ) + 2)) • kernel N (n + 1))
  have h := abs_real_inner_le_norm (tail H (residual N)) u
  have hs := mul_self_le_mul_self (abs_nonneg (inner ℝ (tail H (residual N)) u)) h
  have hsq : (inner ℝ (tail H (residual N)) u) ^ 2 ≤
      ‖tail H (residual N)‖ ^ 2 * ‖u‖ ^ 2 := by
    nlinarith [sq_abs (inner ℝ (tail H (residual N)) u)]
  calc
    _ ≤ ‖tail H (residual N)‖ ^ 2 * ‖u‖ ^ 2 := hsq
    _ ≤ ‖tail H (residual N)‖ ^ 2 * (zetaTwo * C ^ 2) :=
      mul_le_mul_of_nonneg_left (centeredKernel_relativeTail_energy_le N n H C hC hscale)
        (sq_nonneg _)
    _ = _ := by ring

/-- Every fixed relative-scale complement has uniformly vanishing signed response.
No rate of tail convergence, inverse Gram bound, or RH premise is assumed. -/
theorem relativeHead_response_uniform_error (C : ℝ) (hC : 1 ≤ C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ H₀ : ℕ, ∀ H ≥ H₀, ∀ n : ℕ,
      (n : ℝ) + 2 ≤ (C + 1) * ((H : ℝ) + 2) → ∀ N : ℕ,
      (qSequence (QSquarefreeSmoothedProjection.movingCorrection N) (n + 1) -
        inner ℝ (residual N) (finiteHead H (B (kernel N (n + 1)) -
          (1 / ((n : ℝ) + 2)) • kernel N (n + 1)))) ^ 2 ≤ ε := by
  have hCp : 0 < C := by linarith
  have hd : 0 < zetaTwo * C ^ 2 := mul_pos zetaTwo_pos (sq_pos_of_pos hCp)
  obtain ⟨H₀, hH₀⟩ := uniform_tail_tightness_of_tendsto
    residual limitingResidual residual_tendsto (Real.sqrt (ε / (zetaTwo * C ^ 2)))
    (Real.sqrt_pos.2 (div_pos hε hd))
  refine ⟨H₀, ?_⟩
  intro H hH n hn N
  have hs := hH₀ H hH N
  have hsq : ‖tail H (residual N)‖ ^ 2 ≤ ε / (zetaTwo * C ^ 2) := by
    have ht := Real.sq_sqrt (div_nonneg hε.le hd.le)
    nlinarith [norm_nonneg (tail H (residual N)),
      Real.sqrt_nonneg (ε / (zetaTwo * C ^ 2))]
  have hb := mul_le_mul_of_nonneg_left hsq hd.le
  have hc : (zetaTwo * C ^ 2) * (ε / (zetaTwo * C ^ 2)) = ε := by
    field_simp [ne_of_gt zetaTwo_pos, ne_of_gt hCp]
  rw [hc] at hb
  exact (movingCorrection_relativeHead_remainder_sq_le N n H C hC hn).trans hb


/-- Uniform localization into an arbitrarily small relative head, at every
sufficiently large evaluation site. The head may simultaneously be required to
exceed any prescribed absolute cutoff. All physical tails remain complete. -/
theorem shrinkingHead_response_uniform_error (η ε : ℝ) (hη : 0 < η) (hε : 0 < ε)
    (M : ℕ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ H : ℕ,
      M ≤ H ∧ (H : ℝ) ≤ η * ((n : ℝ) + 1) ∧ ∀ N : ℕ,
      (qSequence (QSquarefreeSmoothedProjection.movingCorrection N) (n + 1) -
        inner ℝ (residual N) (finiteHead H (B (kernel N (n + 1)) -
          (1 / ((n : ℝ) + 2)) • kernel N (n + 1)))) ^ 2 ≤ ε := by
  obtain ⟨j, hj⟩ := exists_nat_gt (1 / η)
  have hjp : 0 < j := by
    exact_mod_cast (lt_trans (one_div_pos.mpr hη) hj)
  have hj1 : 1 ≤ (j : ℝ) := by exact_mod_cast hjp
  have hηj : 1 ≤ η * (j : ℝ) := by
    have h := (div_lt_iff₀ hη).mp hj
    nlinarith
  obtain ⟨H₀, hH₀⟩ := relativeHead_response_uniform_error (j : ℝ) hj1 ε hε
  refine ⟨j * max H₀ M, ?_⟩
  intro n hn
  let H := n / j
  have hrem : n % j < j := Nat.mod_lt n hjp
  have hdecomp : n % j + j * H = n := Nat.mod_add_div n j
  have hfloor : n < j * (H + 1) := by nlinarith
  have hlarge : max H₀ M ≤ H := by
    by_contra hh
    have hh' : H + 1 ≤ max H₀ M := by omega
    have hm := Nat.mul_le_mul_left j hh'
    omega
  have hprod : j * H ≤ n := by omega
  have hprodR : (j : ℝ) * (H : ℝ) ≤ (n : ℝ) := by exact_mod_cast hprod
  have hfloorR : (n : ℝ) < (j : ℝ) * ((H : ℝ) + 1) := by exact_mod_cast hfloor
  have hscale : (n : ℝ) + 2 ≤ ((j : ℝ) + 1) * ((H : ℝ) + 2) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) H]
  refine ⟨H, (le_max_right _ _).trans hlarge, ?_, ?_⟩
  · have h₁ := mul_le_mul_of_nonneg_right hηj (Nat.cast_nonneg (α := ℝ) H)
    have h₂ := mul_le_mul_of_nonneg_left hprodR hη.le
    nlinarith
  · exact hH₀ H ((le_max_left _ _).trans hlarge) n hscale

/-- Arbitrary-cutoff localization retains the full Schur subtraction. -/
theorem kernelEnergy_head_tail_exact (N n H : ℕ) (a : ℝ) :
    kernelEnergy N (n + 1) =
      ‖finiteHead H (B (kernel N (n + 1)) - a • kernel N (n + 1))‖ ^ 2 +
      ‖tail H (B (kernel N (n + 1)) - a • kernel N (n + 1))‖ ^ 2 -
      ‖(stage N).starProjection
        (B (kernel N (n + 1)) - a • kernel N (n + 1))‖ ^ 2 := by
  rw [kernelEnergy_centered_exact N (n + 1) a]
  rw [finiteHead_norm_sq_split H (B (kernel N (n + 1)) - a • kernel N (n + 1))]
  rfl

/-- The relative-tail estimate preserves the signed projected square. -/
theorem kernelEnergy_relativeHead_le (N n H : ℕ) (C : ℝ) (hC : 1 ≤ C)
    (hscale : (n : ℝ) + 2 ≤ (C + 1) * ((H : ℝ) + 2)) :
    kernelEnergy N (n + 1) ≤
      ‖finiteHead H (B (kernel N (n + 1)) -
        (1 / ((n : ℝ) + 2)) • kernel N (n + 1))‖ ^ 2 +
      zetaTwo * C ^ 2 -
      ‖(stage N).starProjection (B (kernel N (n + 1)) -
        (1 / ((n : ℝ) + 2)) • kernel N (n + 1))‖ ^ 2 := by
  rw [kernelEnergy_head_tail_exact N n H (1 / ((n : ℝ) + 2))]
  have ht := centeredKernel_relativeTail_energy_le N n H C hC hscale
  linarith

/-- Conditional research reduction: the common signed lower-head bound remains Open. -/
theorem riemannHypothesis_of_lowerHead_bound (C : ℝ) (hC : 0 ≤ C)
    (hL : ∀ N n : ℕ, n + 1 ≤ N →
      |inner ℝ (residual N) (finiteHead n (B (kernel N (n + 1)) -
        (1 / ((n : ℝ) + 2)) • kernel N (n + 1)))| ≤ C) :
    RiemannHypothesis := by
  apply QSquarefreeSmoothedProjection.riemannHypothesis_of_moving_head_bound
    (C + Real.sqrt zetaTwo) (add_nonneg hC (Real.sqrt_nonneg _))
  intro N k hk hkN
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  let L := inner ℝ (residual N) (finiteHead n (B (kernel N (n + 1)) -
    (1 / ((n : ℝ) + 2)) • kernel N (n + 1)))
  have hr : ‖residual N‖ ^ 2 ≤ 1 := by
    have hp := residual_norm_sq (stage N) qOne
    rw [qOne_norm] at hp
    change ‖residual N‖ ^ 2 = _ at hp
    nlinarith [sq_nonneg ‖(stage N).starProjection qOne‖]
  have ht : ‖tail n (residual N)‖ ^ 2 ≤ 1 := by
    have h := tail_norm_le n (residual N)
    nlinarith [norm_nonneg (tail n (residual N)), norm_nonneg (residual N)]
  have he := movingCorrection_lowerHead_remainder_sq_le N n
  have he' : (qSequence (QSquarefreeSmoothedProjection.movingCorrection N) (n + 1) -
      L) ^ 2 ≤ zetaTwo := he.trans (by nlinarith [zetaTwo_pos])
  have heabs : |qSequence (QSquarefreeSmoothedProjection.movingCorrection N) (n + 1) -
      L| ≤ Real.sqrt zetaTwo := by
    nlinarith [sq_abs (qSequence (QSquarefreeSmoothedProjection.movingCorrection N)
      (n + 1) - L), Real.sq_sqrt zetaTwo_pos.le, Real.sqrt_nonneg zetaTwo]
  have hl : |L| ≤ C := hL N n hkN
  calc
    _ ≤ |qSequence (QSquarefreeSmoothedProjection.movingCorrection N) (n + 1) - L| +
        |L| := by simpa only [sub_add_cancel] using
          abs_add_le (qSequence (QSquarefreeSmoothedProjection.movingCorrection N)
            (n + 1) - L) L
    _ ≤ Real.sqrt zetaTwo + C := add_le_add heabs hl
    _ = _ := by ring

end RiemannResearch.RH.QSquarefreeCorrectionKernel
