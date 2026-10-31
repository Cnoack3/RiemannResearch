/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.CenteredProjectionResponse
import RiemannResearch.Analysis.DenseProjectionTesting
import RiemannResearch.Analysis.NestedProjectionEnergy
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.RH.QSquarefreeCorrectionKernel
import RiemannResearch.RH.QSquarefreeKernelLocalization
import RiemannResearch.RH.QSquarefreeTailResponse
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Actual signed squarefree short-head responses

Source: SquarefreeShortHeadSchurResearch20261030.md, sections 4--5,
and the partial normal equations in SquarefreePrefixResponseResearch20261030.md.
The residual is the ordinary canonical projection residual for the complete
squarefree stage, including composite conductors. All inner products are full Q.
These are exact identities and finite inequalities; the common arithmetic
short-head envelope remains Open.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeShortHeadResponse
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage
open QFiniteSupportDualCriterion QShiftedReciprocal QSquarefreeCorrectionKernel
open RiemannResearch.Analysis.CenteredProjectionResponse
open QSquarefreeTailResponse

/-- The actual residual multiplied by the centered, finite physical head. -/
def source (N H n : ℕ) : QHilbert :=
  finiteHead H (B (residual N) - (1 / ((n : ℝ) + 1)) • residual N)

/-- The signed response retains the complete canonical projection kernel. -/
def response (N H n : ℕ) : ℝ := inner ℝ (kernel N n) (source N H n)

theorem response_eq_projected_source (N H n : ℕ) :
    response N H n = qSequence ((stage N).starProjection (source N H n)) n := by
  change inner ℝ ((stage N).starProjection (evaluation n)) (source N H n) = _
  rw [RiemannResearch.Analysis.ResidualizedProjectionKernel.projection_inner,
    real_inner_comm, inner_evaluation]

def loss (N H n : ℕ) : QHilbert :=
  sourceLoss (stage N) (residual N) (source N H n)

def variance (N H n : ℕ) : ℝ :=
  ‖source N H n‖ ^ 2 - (inner ℝ (residual N) (source N H n)) ^ 2 / error N

/-- This identifies the source formulation with the existing exact localization. -/
theorem response_eq_head_pairing (N H n : ℕ) :
    response N H n = inner ℝ (residual N)
      (finiteHead H (B (kernel N n) - (1 / ((n : ℝ) + 1)) • kernel N n)) := by
  rw [response, source, inner_finiteHead_eq_sum, inner_finiteHead_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change ((B (residual N)) i - (1 / ((n : ℝ) + 1)) * (residual N) i) *
    (kernel N n) i =
      ((B (kernel N n)) i - (1 / ((n : ℝ) + 1)) * (kernel N n) i) * (residual N) i
  rw [B_apply, B_apply]
  ring

theorem source_inner_evaluation (N H n : ℕ) (hn : H < n) :
    inner ℝ (evaluation n) (source N H n) = 0 := by
  rw [real_inner_comm, inner_evaluation]
  cases n with
  | zero => omega
  | succ n =>
    rw [qSequence_succ, source, finiteHead_apply_eq_zero H _ n (by omega), zero_div]

theorem evaluation_norm_sq_of_pos (n : ℕ) (hn : 0 < n) :
    ‖evaluation n‖ ^ 2 = zetaTwo * (n : ℝ) ^ 2 := by
  cases n with
  | zero => omega
  | succ n => simpa only [Nat.cast_add, Nat.cast_one] using evaluation_norm_sq n

/-- Exact full-Q source energy, including the projection-loss square. -/
theorem source_energy_exact (N H n : ℕ) :
    ‖(stage N).starProjection (source N H n)‖ ^ 2 =
      variance N H n - ‖loss N H n‖ ^ 2 := by
  exact source_variance_exact (stage N) (residual N) (source N H n)
    (residual_mem_orthogonal N) (ne_of_gt (error_pos N))

theorem response_sq_le (N H n : ℕ) :
    response N H n ^ 2 ≤ ‖kernel N n‖ ^ 2 *
      (variance N H n - ‖loss N H n‖ ^ 2) := by
  exact response_sq_le_source_variance (stage N) (residual N)
    (evaluation n) (source N H n) (residual_mem_orthogonal N)
    (ne_of_gt (error_pos N))

/-- Signed complementary estimate for the actual canonical squarefree residual. -/
theorem signed_response_sq_le (N H n : ℕ) (hn : H < n) :
    (response N H n + qSequence (residual N) n *
        inner ℝ (residual N) (source N H n) / error N) ^ 2 ≤
      (zetaTwo * (n : ℝ) ^ 2 - ‖kernel N n‖ ^ 2 -
        (qSequence (residual N) n) ^ 2 / error N) * ‖loss N H n‖ ^ 2 := by
  have h := signed_complement_sq_le (stage N) (residual N)
    (evaluation n) (source N H n) (residual_mem_orthogonal N)
    (ne_of_gt (error_pos N)) (source_inner_evaluation N H n hn)
  rw [inner_evaluation, evaluation_norm_sq_of_pos n (by omega)] at h
  exact h

/-- A stronger joint energy constraint follows by combining both channels.
No pointwise or asymptotic arithmetic bound is assumed. -/
theorem response_joint_ellipse (N H n : ℕ) (hn : H < n) :
    let K := ‖kernel N n‖ ^ 2
    let L := zetaTwo * (n : ℝ) ^ 2 - K -
      (qSequence (residual N) n) ^ 2 / error N
    let a := qSequence (residual N) n *
      inner ℝ (residual N) (source N H n) / error N
    ((K + L) * response N H n + K * a) ^ 2 ≤
      K * L * ((K + L) * variance N H n - a ^ 2) := by
  have h := response_joint_bound (stage N) (residual N)
    (evaluation n) (source N H n) (residual_mem_orthogonal N)
    (ne_of_gt (error_pos N)) (source_inner_evaluation N H n hn)
  dsimp only at h ⊢
  rw [inner_evaluation, evaluation_norm_sq_of_pos n (by omega)] at h
  exact h

/-- The kernel gain is its exact projection-gap square. -/
theorem kernel_gap_norm_sq (M N n : ℕ) (hMN : M ≤ N) :
    ‖kernel N n - kernel M n‖ ^ 2 = ‖kernel N n‖ ^ 2 - ‖kernel M n‖ ^ 2 := by
  have hs : stage M ≤ stage N :=
    RiemannResearch.Analysis.ExhaustiveWalk.walkSpan_mono squarefreeAtom id hMN
  have h := RiemannResearch.Analysis.NestedProjectionEnergy.captured_energy_eq_add_gap
    hs (evaluation n)
  change ‖kernel N n‖ ^ 2 = ‖kernel M n‖ ^ 2 + ‖kernel N n - kernel M n‖ ^ 2 at h
  linarith

theorem optimizer_gap_norm_sq (M N : ℕ) (hMN : M ≤ N) :
    ‖optimizer N - optimizer M‖ ^ 2 = error M - error N := by
  have hs : stage M ≤ stage N :=
    RiemannResearch.Analysis.ExhaustiveWalk.walkSpan_mono squarefreeAtom id hMN
  have h := RiemannResearch.Analysis.NestedProjectionEnergy.residual_energy_eq_add_gap
    hs qOne
  change error M = error N + ‖optimizer N - optimizer M‖ ^ 2 at h
  linarith

/-- Exact two-stage signed response; neither source term is discarded. -/
theorem response_difference_exact (M N H n : ℕ) :
    response N H n - response M H n =
      inner ℝ (kernel N n - kernel M n) (source N H n) -
        inner ℝ (kernel M n) (source M H n - source N H n) := by
  simp only [response, inner_sub_left, inner_sub_right]
  ring

theorem response_difference_abs_le (M N H n : ℕ) :
    |response N H n - response M H n| ≤
      ‖kernel N n - kernel M n‖ * ‖source N H n‖ +
        ‖kernel M n‖ * ‖source M H n - source N H n‖ := by
  rw [response_difference_exact]
  exact (abs_sub _ _).trans (add_le_add (abs_real_inner_le_norm _ _)
    (abs_real_inner_le_norm _ _))

/-- The partial normal equation retains its signed complete-tail term. -/
theorem residual_partial_normal_equation (N H : ℕ) (v : QHilbert)
    (hv : v ∈ stage N) :
    inner ℝ v (finiteHead H (residual N)) =
      -inner ℝ v (residual N - finiteHead H (residual N)) := by
  have ho : inner ℝ v (residual N) = 0 := by
    rw [RiemannResearch.Analysis.DenseProjectionTesting.inner_eq_projected_test
      (stage N) hv (residual N),
      (stage N).starProjection_apply_eq_zero_iff.mpr (residual_mem_orthogonal N),
      inner_zero_right]
  rw [inner_sub_right, ho]
  ring

/-- The actual short source annihilates every head-null vector. -/
theorem source_inner_headNull (N H n : ℕ) (v : QHilbert) (hv : v ∈ headNull H) :
    inner ℝ v (source N H n) = 0 := by
  rw [source, inner_finiteHead_eq_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [hv i (Finset.mem_range.mp hi), mul_zero]

/-- Removing the full legal head-null projection preserves each source moment. -/
theorem source_screened_moment (N H n : ℕ) (v : QHilbert) :
    inner ℝ (v - (tailStage N H).starProjection v) (source N H n) =
      inner ℝ v (source N H n) := by
  rw [inner_sub_left, source_inner_headNull N H n _
    ((tailStage N H).starProjection_apply_mem v).2, sub_zero]

/-- The projected source satisfies the actual stage normal equations. -/
theorem source_normal_equation (N H n : ℕ) (v : QHilbert) (hv : v ∈ stage N) :
    inner ℝ v ((stage N).starProjection (source N H n)) =
      inner ℝ v (source N H n) :=
  (RiemannResearch.Analysis.DenseProjectionTesting.inner_eq_projected_test
    (stage N) hv (source N H n)).symm

end RiemannResearch.RH.QSquarefreeShortHeadResponse
