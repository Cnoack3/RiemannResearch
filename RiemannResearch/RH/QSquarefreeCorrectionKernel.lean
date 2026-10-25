/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ResidualizedProjectionKernel
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Actual squarefree residualized evaluation kernels

Source: user-provided RH_Measure_Change_Regularity_Research_Handoff_2026-10-25,
Section A2. Every stage is the masked squarefree dictionary's actual stage.
The complete Hilbert norm is used throughout. The uniform product estimate
in the final conditional theorem is an OPEN arithmetic obligation.
-/

noncomputable section
namespace RiemannResearch.RH.QSquarefreeCorrectionKernel
open ZetaTwoHilbert ZetaTwoOptimizerStage QShiftedReciprocal
open QSquarefreeSmoothedProjection
open RiemannResearch.Analysis.ResidualizedProjectionKernel

/-- Riesz vector for physical evaluation, including the convention at zero. -/
def evaluation : ℕ → QHilbert
  | 0 => 0
  | n + 1 => lp.single 2 n (1 / Real.sqrt (qWeight n))

theorem inner_evaluation (f : QHilbert) (n : ℕ) :
    inner ℝ f (evaluation n) = qSequence f n := by
  cases n with
  | zero => simp [evaluation, qSequence]
  | succ n =>
    simp only [evaluation, lp.inner_single_right, RCLike.inner_apply,
      conj_trivial, qSequence_succ]
    ring

theorem B_evaluation_succ (n : ℕ) :
    B (evaluation (n + 1)) =
      (1 / ((n : ℝ) + 2)) • evaluation (n + 1) := by
  apply lp.ext
  funext i
  rw [B_apply]
  change (lp.single 2 n (1 / Real.sqrt (qWeight n)) : QHilbert) i /
      ((i : ℝ) + 2) =
    (1 / ((n : ℝ) + 2)) *
      (lp.single 2 n (1 / Real.sqrt (qWeight n)) : QHilbert) i
  by_cases hi : i = n
  · subst i
    ring
  · simp [lp.single_apply, hi]

def kernel (N n : ℕ) : QHilbert := (stage N).starProjection (evaluation n)

def residualizedKernel (N n : ℕ) : QHilbert :=
  B (kernel N n) - (stage N).starProjection (B (kernel N n))

def kernelEnergy (N n : ℕ) : ℝ := ‖residualizedKernel N n‖ ^ 2

theorem residualizedKernel_mem_orthogonal (N n : ℕ) :
    residualizedKernel N n ∈ (stage N)ᗮ :=
  Submodule.sub_starProjection_mem_orthogonal (B (kernel N n))

/-- Exact signed pairing; cancellation has not yet been estimated. -/
theorem movingCorrection_eq_pairing (N n : ℕ) :
    qSequence (movingCorrection N) n =
      inner ℝ (residual N) (residualizedKernel N n) := by
  rw [← inner_evaluation]
  exact pairing_eq_residualized (stage N) B B_symmetric
    (residual_mem_orthogonal N) (evaluation n)

/-- Exact Schur-energy subtraction in physical Hilbert coordinates. -/
theorem kernelEnergy_exact (N n : ℕ) :
    kernelEnergy N n = ‖B (kernel N n)‖ ^ 2 -
      ‖(stage N).starProjection (B (kernel N n))‖ ^ 2 :=
  residual_norm_sq (stage N) (B (kernel N n))

theorem residualizedKernel_centered_complement (N n : ℕ) :
    residualizedKernel N (n + 1) =
      ((1 / ((n : ℝ) + 2)) • (evaluation (n + 1) - kernel N (n + 1)) -
        B (evaluation (n + 1) - kernel N (n + 1))) -
      (stage N).starProjection
        ((1 / ((n : ℝ) + 2)) • (evaluation (n + 1) - kernel N (n + 1)) -
          B (evaluation (n + 1) - kernel N (n + 1))) :=
  residualized_of_eigenvector (stage N) B (evaluation (n + 1))
    (1 / ((n : ℝ) + 2)) (B_evaluation_succ n)

theorem kernelEnergy_le_centered_complement (N n : ℕ) :
    kernelEnergy N (n + 1) ≤
      ‖(1 / ((n : ℝ) + 2)) • (evaluation (n + 1) - kernel N (n + 1)) -
        B (evaluation (n + 1) - kernel N (n + 1))‖ ^ 2 :=
  residualized_sq_le_centered_complement (stage N) B (evaluation (n + 1))
    (1 / ((n : ℝ) + 2)) (B_evaluation_succ n)

theorem kernelEnergy_nonneg (N n : ℕ) : 0 ≤ kernelEnergy N n := sq_nonneg _

theorem movingCorrection_sq_le (N n : ℕ) :
    (qSequence (movingCorrection N) n) ^ 2 ≤ error N * kernelEnergy N n := by
  rw [movingCorrection_eq_pairing]
  have h := abs_real_inner_le_norm (residual N) (residualizedKernel N n)
  have hh := mul_le_mul h h (abs_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  simpa only [← pow_two, sq_abs, mul_pow, error, kernelEnergy] using hh

theorem movingCorrection_sq_le_exact (N n : ℕ) :
    (qSequence (movingCorrection N) n) ^ 2 ≤ error N *
      (‖B (kernel N n)‖ ^ 2 -
        ‖(stage N).starProjection (B (kernel N n))‖ ^ 2) := by
  rw [← kernelEnergy_exact]
  exact movingCorrection_sq_le N n

/-- Conditional research reduction. The common growing-head product bound
is Open; this theorem does not provide it. -/
theorem riemannHypothesis_of_head_kernel_product_bound (C : ℝ) (hC : 0 ≤ C)
    (hK : ∀ N n : ℕ, 0 < n → n ≤ N → error N * kernelEnergy N n ≤ C ^ 2) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_moving_head_bound C hC
  intro N n hn hnN
  have h := (movingCorrection_sq_le N n).trans (hK N n hn hnN)
  have habs : |qSequence (movingCorrection N) n| ^ 2 ≤ C ^ 2 := by
    simpa only [sq_abs] using h
  nlinarith [abs_nonneg (qSequence (movingCorrection N) n)]

/-- Physical reproducing-kernel symmetry, including the convention at zero. -/
theorem kernel_physical_symmetry (N n m : ℕ) :
    qSequence (kernel N n) m = qSequence (kernel N m) n := by
  rw [← inner_evaluation, ← inner_evaluation]
  change inner ℝ ((stage N).starProjection (evaluation n)) (evaluation m) =
    inner ℝ ((stage N).starProjection (evaluation m)) (evaluation n)
  rw [projection_inner]
  exact real_inner_comm _ _

/-- Every scalar shift retains the same residualized kernel. -/
theorem residualizedKernel_centered (N n : ℕ) (a : ℝ) :
    residualizedKernel N n =
      (B (kernel N n) - a • kernel N n) -
        (stage N).starProjection (B (kernel N n) - a • kernel N n) := by
  exact (residualized_shift (stage N) B (evaluation n) a).symm

/-- Exact centered Schur subtraction; its second square must be retained. -/
theorem kernelEnergy_centered_exact (N n : ℕ) (a : ℝ) :
    kernelEnergy N n =
      ‖B (kernel N n) - a • kernel N n‖ ^ 2 -
        ‖(stage N).starProjection (B (kernel N n) - a • kernel N n)‖ ^ 2 := by
  rw [kernelEnergy, residualizedKernel_centered, residual_norm_sq]

/-- Center the signed pairing before applying any Cauchy--Schwarz estimate. -/
theorem movingCorrection_eq_centered_pairing (N n : ℕ) (a : ℝ) :
    qSequence (movingCorrection N) n =
      inner ℝ (residual N) (B (kernel N n) - a • kernel N n) := by
  have hk : inner ℝ (residual N) (kernel N n) = 0 :=
    orthogonal_inner_projection (stage N) (residual_mem_orthogonal N) (evaluation n)
  have hB : inner ℝ (residual N)
      ((stage N).starProjection (B (kernel N n))) = 0 :=
    orthogonal_inner_projection (stage N) (residual_mem_orthogonal N) _
  rw [movingCorrection_eq_pairing, residualizedKernel,
    inner_sub_right, inner_sub_right, real_inner_smul_right, hk, hB]
  ring

/-- The centered kernel has a physical multiplier difference at every site. -/
theorem centeredKernel_physical (N n m : ℕ) (a : ℝ) :
    qSequence (B (kernel N n) - a • kernel N n) m =
      (1 / ((m : ℝ) + 1) - a) * qSequence (kernel N n) m := by
  have hsub := congrFun (qSequenceLinear.map_sub
    (B (kernel N n)) (a • kernel N n)) m
  have hsmul := congrFun (qSequenceLinear.map_smul a (kernel N n)) m
  change qSequence (B (kernel N n) - a • kernel N n) m =
    qSequence (B (kernel N n)) m - qSequence (a • kernel N n) m at hsub
  change qSequence (a • kernel N n) m = a * qSequence (kernel N n) m at hsmul
  rw [hsub, hsmul, qSequence_B]
  ring

/-- Centering at the evaluation site's multiplier cancels its diagonal exactly. -/
theorem centeredKernel_diagonal_zero (N n : ℕ) :
    qSequence (B (kernel N n) -
      (1 / ((n : ℝ) + 1)) • kernel N n) n = 0 := by
  rw [centeredKernel_physical, sub_self, zero_mul]

/-- Complete complementary localization identity, retaining the projected square. -/
theorem kernelEnergy_centered_complement_exact (N n : ℕ) :
    kernelEnergy N (n + 1) =
      ‖(1 / ((n : ℝ) + 2)) • (evaluation (n + 1) - kernel N (n + 1)) -
        B (evaluation (n + 1) - kernel N (n + 1))‖ ^ 2 -
      ‖(stage N).starProjection
        ((1 / ((n : ℝ) + 2)) • (evaluation (n + 1) - kernel N (n + 1)) -
          B (evaluation (n + 1) - kernel N (n + 1)))‖ ^ 2 := by
  rw [kernelEnergy, residualizedKernel_centered_complement, residual_norm_sq]


end RiemannResearch.RH.QSquarefreeCorrectionKernel
