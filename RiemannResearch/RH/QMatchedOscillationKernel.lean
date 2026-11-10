/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QParetoClosedProjectionComparison
import RiemannResearch.RH.QParetoMetric
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.QSquarefreeCorrectionKernel
import RiemannResearch.Analysis.ResidualizedProjectionKernel
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith


/-!
# Matched Q/P projection kernels for physical oscillation

Source: user-provided fixed-modulus oscillation audit, 9 November 2026.
The matched normal equations give an exact signed pairing with the Pareto
residual after projecting the reciprocal test off the SAME legal subspace.
The energy equality retains the subtracted projection norm square.
The imported evaluation vector has no squarefree hypothesis; no squarefree
stage or closure is used here. The spaces S and T remain explicit.
No uniform kernel estimate is asserted.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QMatchedOscillationKernel
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QParetoEquivalence QParetoMetric QParetoClosedProjectionComparison
open RiemannResearch.Analysis.ResidualizedProjectionKernel
open QSquarefreeCorrectionKernel (evaluation inner_evaluation)

variable (S : Submodule ℝ QHilbert) (T : Submodule ℝ ThresholdHilbert)
variable [S.HasOrthogonalProjection] [T.HasOrthogonalProjection]

def pairKernel (n m : ℕ) : QHilbert :=
  S.starProjection (evaluation n - evaluation m)

def screenedPairKernel (n m : ℕ) : ThresholdHilbert :=
  reciprocalD (toPareto (pairKernel S n m)) -
    T.starProjection (reciprocalD (toPareto (pairKernel S n m)))

theorem inner_pairKernel (f : QHilbert) (hf : f ∈ S) (n m : ℕ) :
    inner ℝ f (pairKernel S n m) = qSequence f n - qSequence f m := by
  rw [pairKernel, ← projection_inner,
    Submodule.starProjection_eq_self_iff.mpr hf,
    inner_sub_right, inner_evaluation, inner_evaluation]

theorem screenedPairKernel_energy (n m : ℕ) :
    ‖screenedPairKernel S T n m‖ ^ 2 =
      ‖reciprocalD (toPareto (pairKernel S n m))‖ ^ 2 -
        ‖T.starProjection (reciprocalD (toPareto (pairKernel S n m)))‖ ^ 2 :=
  residual_norm_sq T _

/-- The reciprocal test screened against the same physical dictionary in P. -/
def screenReciprocal (v : QHilbert) : ThresholdHilbert :=
  reciprocalD (toPareto v) - T.starProjection (reciprocalD (toPareto v))

theorem screenReciprocal_sub (v u : QHilbert) :
    screenReciprocal T (v - u) = screenReciprocal T v - screenReciprocal T u := by
  simp only [screenReciprocal, toPareto_sub, map_sub]
  abel

/-- Keep the raw evaluation term and subtract its complementary-projection
contribution. The auxiliary vector can be chosen as a physical head cutoff. -/
theorem screenedPairKernel_raw_sub_split (n m : ℕ) (h : QHilbert) :
    let v := evaluation n - evaluation m
    let u := v - S.starProjection v
    screenedPairKernel S T n m =
      screenReciprocal T v - screenReciprocal T h - screenReciprocal T (u - h) := by
  dsimp only
  change screenReciprocal T (S.starProjection (evaluation n - evaluation m)) = _
  let v := evaluation n - evaluation m
  let u := v - S.starProjection v
  change screenReciprocal T (S.starProjection v) =
    screenReciprocal T v - screenReciprocal T h - screenReciprocal T (u - h)
  have hv : S.starProjection v = v - u := (sub_sub_cancel v _).symm
  calc
    screenReciprocal T (S.starProjection v) = screenReciprocal T (v - u) :=
      congrArg (screenReciprocal T) hv
    _ = screenReciprocal T v - screenReciprocal T u := screenReciprocal_sub T v u
    _ = _ := by
      rw [screenReciprocal_sub T u h]
      abel

/-- Exact split of the complete screened kernel at an arbitrary test head. -/
theorem screenedPairKernel_split (n m : ℕ) (h : QHilbert) :
    screenedPairKernel S T n m =
      screenReciprocal T h + screenReciprocal T (pairKernel S n m - h) := by
  change screenReciprocal T (pairKernel S n m) = _
  rw [screenReciprocal_sub T (pairKernel S n m) h]
  abel

variable (hsame : ∀ f : QHilbert, toPareto f ∈ T ↔ f ∈ S)
include hsame

theorem matched_test_identity (x h : QHilbert) (hh : h ∈ S) :
    zetaTwo * inner ℝ (qFit S x - pFit T x) h =
      inner ℝ (toPareto (x - pFit T x))
        (reciprocalD (toPareto h) - T.starProjection (reciprocalD (toPareto h))) := by
  have hq : inner ℝ (x - qFit S x) h = 0 := by
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal hh
      (Submodule.sub_starProjection_mem_orthogonal (K := S) x)
  have hp (v : ThresholdHilbert) (hv : v ∈ T) :
      inner ℝ (toPareto (x - pFit T x)) v = 0 := by
    rw [toPareto_sub, toPareto_pFit, real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal hv
      (Submodule.sub_starProjection_mem_orthogonal (K := T) (toPareto x))
  have he : inner ℝ (qFit S x - pFit T x) h =
      inner ℝ (x - pFit T x) h := by
    rw [inner_sub_left] at hq
    simp only [inner_sub_left]
    linarith
  rw [he, inner_identity, hp _ ((hsame h).mpr hh), zero_add,
    metricPairing, inner_sub_right, hp _ (T.starProjection_apply_mem _), sub_zero]

theorem matched_pair_identity (x : QHilbert) (n m : ℕ) :
    zetaTwo * (qSequence (qFit S x - pFit T x) n -
      qSequence (qFit S x - pFit T x) m) =
      inner ℝ (toPareto (x - pFit T x)) (screenedPairKernel S T n m) := by
  have hd : qFit S x - pFit T x ∈ S :=
    S.sub_mem (S.starProjection_apply_mem x) (pFit_mem S T hsame x)
  rw [← inner_pairKernel S _ hd n m]
  exact matched_test_identity S T hsame x _ (S.starProjection_apply_mem _)

theorem matched_pair_bound (x : QHilbert) (n m : ℕ) :
    zetaTwo * |qSequence (qFit S x - pFit T x) n -
      qSequence (qFit S x - pFit T x) m| ≤
      ‖toPareto (x - pFit T x)‖ * ‖screenedPairKernel S T n m‖ := by
  have h := abs_real_inner_le_norm
    (toPareto (x - pFit T x)) (screenedPairKernel S T n m)
  rw [← matched_pair_identity S T hsame x n m, abs_mul,
    abs_of_pos zetaTwo_pos] at h
  exact h

end RiemannResearch.RH.QMatchedOscillationKernel
