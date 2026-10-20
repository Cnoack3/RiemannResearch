/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QRationalPeriodRefinement
import RiemannResearch.RH.QRationalMinimumLimit
import RiemannResearch.RH.QRationalCoprimeMinimum
import RiemannResearch.RH.QSquarefreePrimorialCofinality
import Mathlib.Tactic.Linarith

/-!
# Exact gains between actual rational minimizers

Source: independent development from the user-provided continuation agenda,
20 October 2026. The stage drop is the sum of a rational-metric refinement
term and the full weighted optimizer-displacement square. Neither term is
discarded. Large cofinal period steps make the metric term nonnegative;
no positive relative lower bound for the legal gain is asserted.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QRationalCoprimeTail
open ZetaTwoProbability ZetaTwoHilbert
open QSquarefreePrimorialCofinality
open Pareto.SquarefreeStageExhaustion

/-- Actual optimizer displacement measured in the later rational metric. -/
def rationalStageDisplacement (n m : ℕ) : ℝ :=
  ∑ a ∈ sites (primorialPeriod m), weight (primorialPeriod m) a *
    (qSequence (rationalMinimizer (primorialPeriod n)) a -
      qSequence (rationalMinimizer (primorialPeriod m)) a)^2

theorem rationalStageDisplacement_nonneg (n m : ℕ) :
    0 ≤ rationalStageDisplacement n m :=
  Finset.sum_nonneg (fun _ _ =>
    mul_nonneg (weight_nonneg _ _) (sq_nonneg _))

/-- Completion of the square at the actual later minimizer. -/
theorem rationalMinimum_completion_previous {n m : ℕ} (hnm : n ≤ m) :
    rationalError (primorialPeriod m)
        (qSequence (rationalMinimizer (primorialPeriod n))) =
      rationalMinimum (primorialPeriod m) + rationalStageDisplacement n m := by
  have hmem := primorialStage_mono hnm (rationalMinimizer_mem n)
  obtain ⟨b, hb⟩ := exists_qDivisorFit_of_mem hmem
  have hseq : divisorFit (primorialPeriod m) b =
      qSequence (rationalMinimizer (primorialPeriod n)) := by
    simpa only [qSequence_qDivisorFit] using congrArg qSequence hb
  have he := divisorFit_completion (primorialPeriod m)
    (rationalCoefficients (primorialPeriod m)) b
    (rationalCoefficients_normal (primorialPeriod m))
  rw [hseq] at he
  simpa only [rationalMinimum, rationalStageDisplacement, rationalMinimizer,
    qSequence_qDivisorFit] using he

/-- Exact cross-stage minimum drop. The metric change and full displacement
square are separated; the signed metric difference is retained. -/
theorem rationalMinimum_drop_exact {n m : ℕ} (hnm : n ≤ m) :
    rationalMinimum (primorialPeriod n) - rationalMinimum (primorialPeriod m) =
      rationalGap (primorialPeriod n)
        (qSequence (rationalMinimizer (primorialPeriod n))) -
      rationalGap (primorialPeriod m)
        (qSequence (rationalMinimizer (primorialPeriod n))) +
      rationalStageDisplacement n m := by
  have hf := rationalMinimizer_mem n
  have hfm := primorialStage_mono hnm hf
  have hb : ∀ k, |1 - qSequence (rationalMinimizer (primorialPeriod n)) k| ≤
      1 + ∑ d ∈ (primorialPeriod n).divisors,
        |rationalCoefficients (primorialPeriod n) d| := by
    intro k
    simpa only [rationalMinimizer, qSequence_qDivisorFit] using
      divisorFit_residual_bound (primorialPeriod n)
        (rationalCoefficients (primorialPeriod n)) k
  have heL := rationalError_exact_gap (primorialPeriod n)
    (primorialPeriod_pos n) _ hb (qSequence_periodic_of_mem hf)
  have heM := rationalError_exact_gap (primorialPeriod m)
    (primorialPeriod_pos m) _ hb (qSequence_periodic_of_mem hfm)
  have he := rationalMinimum_completion_previous hnm
  have hval : rationalError (primorialPeriod n)
      (qSequence (rationalMinimizer (primorialPeriod n))) =
        rationalMinimum (primorialPeriod n) := by
    simp only [rationalMinimizer, qSequence_qDivisorFit, rationalMinimum]
  rw [hval] at heL
  linarith

/-- Large cofinal steps decrease the actual rational minimum, and the full
weighted displacement square is paid for by that decrease. -/
theorem rationalMinimum_drop_ge_displacement {n m k : ℕ} (hnm : n ≤ m)
    (hperiod : primorialPeriod m = primorialPeriod n * k) (hk : 120 ≤ k) :
    rationalStageDisplacement n m ≤
      rationalMinimum (primorialPeriod n) - rationalMinimum (primorialPeriod m) := by
  have hg := rationalGap_mul_le_self (primorialPeriod n) k
    (primorialPeriod_pos n) hk
    (qSequence (rationalMinimizer (primorialPeriod n)))
    (qSequence_periodic_of_mem (rationalMinimizer_mem n))
  rw [← hperiod] at hg
  rw [rationalMinimum_drop_exact hnm]
  linarith

theorem rationalMinimum_le_of_large_refinement {n m k : ℕ} (hnm : n ≤ m)
    (hperiod : primorialPeriod m = primorialPeriod n * k) (hk : 120 ≤ k) :
    rationalMinimum (primorialPeriod m) ≤ rationalMinimum (primorialPeriod n) := by
  have h := rationalMinimum_drop_ge_displacement hnm hperiod hk
  have hn := rationalStageDisplacement_nonneg n m
  linarith

/-- The metric part alone refunds at least half the coarse discrepancy
at a factor-240 refinement, independently of the optimizer coefficients. -/
theorem rationalMinimum_drop_ge_half_gap_add_displacement {n m k : ℕ}
    (hnm : n ≤ m) (hperiod : primorialPeriod m = primorialPeriod n * k)
    (hk : 240 ≤ k) :
    rationalGap (primorialPeriod n)
        (qSequence (rationalMinimizer (primorialPeriod n))) / 2 +
      rationalStageDisplacement n m ≤
        rationalMinimum (primorialPeriod n) - rationalMinimum (primorialPeriod m) := by
  have hg := rationalGap_mul_le_half (primorialPeriod n) k
    (primorialPeriod_pos n) hk
    (qSequence (rationalMinimizer (primorialPeriod n)))
    (qSequence_periodic_of_mem (rationalMinimizer_mem n))
  rw [← hperiod] at hg
  rw [rationalMinimum_drop_exact hnm]
  linarith

/-- Exact cumulative metric refunds and actual optimizer movements, with
the terminal minimum retained. -/
theorem rationalMinimum_chain_exact (σ : ℕ → ℕ) (hσ : Monotone σ) (N : ℕ) :
    rationalMinimum (primorialPeriod (σ N)) +
      (∑ j ∈ Finset.range N, (
        rationalGap (primorialPeriod (σ j))
            (qSequence (rationalMinimizer (primorialPeriod (σ j)))) -
        rationalGap (primorialPeriod (σ (j + 1)))
            (qSequence (rationalMinimizer (primorialPeriod (σ j)))) +
        rationalStageDisplacement (σ j) (σ (j + 1)))) =
      rationalMinimum (primorialPeriod (σ 0)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have he := rationalMinimum_drop_exact (hσ (Nat.le_succ N))
      linarith

/-- Uniform finite budget along any actual stage chain whose successive
period ratios are at least 240. It controls moving coefficients directly. -/
theorem rationalMinimum_chain_budget (σ k : ℕ → ℕ) (hσ : Monotone σ)
    (hperiod : ∀ j, primorialPeriod (σ (j + 1)) = primorialPeriod (σ j) * k j)
    (hk : ∀ j, 240 ≤ k j) (N : ℕ) :
    (∑ j ∈ Finset.range N, (
      rationalGap (primorialPeriod (σ j))
          (qSequence (rationalMinimizer (primorialPeriod (σ j)))) / 2 +
      rationalStageDisplacement (σ j) (σ (j + 1)))) ≤
      rationalMinimum (primorialPeriod (σ 0)) -
        rationalMinimum (primorialPeriod (σ N)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have he := rationalMinimum_drop_ge_half_gap_add_displacement
        (hσ (Nat.le_succ N)) (hperiod N) (hk N)
      linarith

theorem rationalMinimum_chain_budget_le_initial (σ k : ℕ → ℕ) (hσ : Monotone σ)
    (hperiod : ∀ j, primorialPeriod (σ (j + 1)) = primorialPeriod (σ j) * k j)
    (hk : ∀ j, 240 ≤ k j) (N : ℕ) :
    (∑ j ∈ Finset.range N, (
      rationalGap (primorialPeriod (σ j))
          (qSequence (rationalMinimizer (primorialPeriod (σ j)))) / 2 +
      rationalStageDisplacement (σ j) (σ (j + 1)))) ≤
      rationalMinimum (primorialPeriod (σ 0)) := by
  have he := rationalMinimum_chain_budget σ k hσ hperiod hk N
  have hnonneg : 0 ≤ rationalMinimum (primorialPeriod (σ N)) := by
    have h := rationalMinimum_lower (σ N)
    have hp : 0 ≤ zetaTwo * primorialError (σ N) :=
      mul_nonneg zetaTwo_pos.le (primorialError_pos (σ N)).le
    exact hp.trans h
  linarith


end RiemannResearch.RH.QRationalCoprimeTail
