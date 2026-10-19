/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeAffineHead
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.QSquarefreeExactHeadAverages
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.QSquarefreeHeadSchedule
import RiemannResearch.RH.QSquarefreeHeadStep
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Evaluated signed head-cost versus period-gain budgets

Source: user-provided LCM telescoping question, 19 October 2026.
The finite identities specialize QSquarefreeAffineHead and QSquarefreeHeadStep.
Actual complete-Q refits precede each new constraint. The final RH consumers
are conditional research reductions: their displayed arithmetic budgets remain
open, including for the explicit primorialSchedule.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeBlockBalance
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeAffineHead
open QSquarefreeHeadSchedule QSquarefreeHeadStep

def energy (s : Schedule) (i : ℕ) : ℝ :=
  minimumError (i + 1) (s.period i) (s.anchor i) (s.anchor_mem i)

def refit (s : Schedule) (i : ℕ) : QHilbert :=
  optimizer (i + 1) (s.period (i + 1)) (s.anchor (i + 1)) (s.anchor_mem (i + 1))

def gain (s : Schedule) (i : ℕ) : ℝ :=
  ‖optimizer (i + 1) (s.period i) (s.anchor i) (s.anchor_mem i) - refit s i‖ ^ 2

def defect (s : Schedule) (i : ℕ) : ℝ :=
  1 - qSequence (refit s i) (i + 2)

def capacity (s : Schedule) (i : ℕ) : ℝ :=
  stepCapacity (i + 2) (s.period (i + 1)) (s.anchor (i + 1)) (s.anchor_mem (i + 1))

def cost (s : Schedule) (i : ℕ) : ℝ :=
  if Squarefree (i + 2) then (defect s i)^2 / capacity s i else 0

def weightedDefect (s : Schedule) (i : ℕ) : ℝ :=
  if Squarefree (i + 2) then
    (defect s i)^2 * ((1 / zetaTwo) * (4 / (i + 1 : ℝ))) else 0

private theorem small_old (s : Schedule) (i : ℕ) :
    ∀ d, 1 < d → d ≤ i + 1 → Squarefree d → d ∣ s.period (i + 1) := by
  intro d hd hdi hsf
  exact s.small (i + 1) d hd (by omega) hsf

theorem refit_period_gain (s : Schedule) (i : ℕ) :
    energy s i = ‖qOne - refit s i‖ ^ 2 + gain s i := by
  have h := minimumError_period_gain (i + 1) (s.period i) (s.period (i + 1))
    (s.anchor i) (Nat.succ_pos i) (s.positive i) (s.positive (i + 1))
    (s.nested i) (s.anchor_mem i) (s.anchor_mem_next i) (s.anchor_gt i) (s.small i)
  have he := optimizer_anchor_independent (i + 1) (s.period (i + 1))
    (s.anchor i) (s.anchor (i + 1)) (Nat.succ_pos i) (s.positive (i + 1))
    (s.anchor_mem_next i) (s.anchor_mem (i + 1)) (s.anchor_gt i)
    (by have := s.anchor_gt (i + 1); omega) (small_old s i)
  unfold minimumError at h
  rw [he] at h
  exact h

theorem head_cost_eq (s : Schedule) (i : ℕ) :
    energy s (i + 1) = ‖qOne - refit s i‖ ^ 2 + cost s i := by
  by_cases hs : Squarefree (i + 2)
  · have h := minimumError_single_head_cost (i + 2) (s.period (i + 1))
      (s.anchor (i + 1)) (by omega) (s.positive (i + 1))
      (s.small (i + 1) (i + 2) (by omega) (by omega) hs)
      (s.anchor_mem (i + 1)) (by have := s.anchor_gt (i + 1); omega)
      (fun d hd hdi hsf => s.small (i + 1) d hd (by omega) hsf)
    simpa [energy, cost, hs, defect, capacity, refit, minimumError,
      show i + 2 - 1 = i + 1 by omega, Nat.add_assoc] using h
  · have h := nonsquarefree_boundary_no_cost (i + 2) (s.period (i + 1))
      (s.anchor (i + 1)) (by omega) hs (s.positive (i + 1))
      (s.squarefree (i + 1)) (s.anchor_mem (i + 1))
      (by have := s.anchor_gt (i + 1); omega)
      (fun d hd hdi hsf => s.small (i + 1) d hd (by omega) hsf)
    simpa [energy, cost, hs, refit, minimumError,
      show i + 2 - 1 = i + 1 by omega, Nat.add_assoc] using h.2

theorem cost_le_weightedDefect (s : Schedule) (i : ℕ) :
    cost s i ≤ weightedDefect s i := by
  by_cases hs : Squarefree (i + 2)
  · have h := minimumError_single_head_near_anchor_bound (i + 2)
      (s.period (i + 1)) (s.anchor (i + 1)) (by omega) (s.positive (i + 1))
      (s.small (i + 1) (i + 2) (by omega) (by omega) hs)
      (s.anchor_mem (i + 1)) (by have := s.anchor_gt (i + 1); omega)
      (by have := s.anchor_le (i + 1); omega)
      (fun d hd hdi hsf => s.small (i + 1) d hd (by omega) hsf)
    have he := head_cost_eq s i
    have hh : energy s (i + 1) ≤ ‖qOne - refit s i‖ ^ 2 + weightedDefect s i := by
      simpa [energy, weightedDefect, hs, defect, refit, minimumError,
        show i + 2 - 1 = i + 1 by omega, Nat.add_assoc] using h
    linarith
  · simp only [cost, weightedDefect, if_neg hs, le_refl]

theorem step_balance (s : Schedule) (i : ℕ) :
    energy s (i + 1) + gain s i = energy s i + cost s i := by
  have hg := refit_period_gain s i
  have hc := head_cost_eq s i
  linarith

/-- Exact evaluated telescope; no signed summand has been discarded. -/
theorem evaluated_telescope (s : Schedule) (N : ℕ) :
    energy s N + ∑ i ∈ Finset.range N, gain s i =
      energy s 0 + ∑ i ∈ Finset.range N, cost s i := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have h := step_balance s N
      linarith

theorem signed_balance_eq (s : Schedule) (N : ℕ) :
    energy s N = energy s 0 + ∑ i ∈ Finset.range N, (cost s i - gain s i) := by
  rw [Finset.sum_sub_distrib]
  have h := evaluated_telescope s N
  linarith

/-- The upper estimate retains every actual nonnegative period gain. -/
theorem signed_weighted_bound (s : Schedule) (N : ℕ) :
    energy s N ≤ energy s 0 +
      ∑ i ∈ Finset.range N, (weightedDefect s i - gain s i) := by
  rw [signed_balance_eq s N]
  apply add_le_add le_rfl
  exact Finset.sum_le_sum fun i _ => sub_le_sub_right (cost_le_weightedDefect s i) _

theorem bounded_energy_iff_signed_budget (s : Schedule) (B : ℝ) :
    (∀ N, energy s N ≤ B) ↔
      ∀ N, ∑ i ∈ Finset.range N, (cost s i - gain s i) ≤ B - energy s 0 := by
  constructor
  · intro h N
    have he := signed_balance_eq s N
    have hb := h N
    linarith
  · intro h N
    have he := signed_balance_eq s N
    have hb := h N
    linarith

/-- Conditional research reduction. The signed arithmetic budget is Open. -/
theorem rh_of_signed_budget (s : Schedule) (B : ℝ)
    (hbudget : ∀ N, ∑ i ∈ Finset.range N, (cost s i - gain s i) ≤ B) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_bounded_affine_minima s.period s.anchor s.positive
    s.squarefree s.anchor_mem s.anchor_gt s.small (energy s 0 + B)
  intro N
  change energy s N ≤ _
  rw [signed_balance_eq]
  exact add_le_add le_rfl (hbudget N)

/-- Sufficient but potentially stronger budget, using the nearby-anchor bound. -/
theorem rh_of_weighted_defect_budget (s : Schedule) (B : ℝ)
    (hbudget : ∀ N, ∑ i ∈ Finset.range N, (weightedDefect s i - gain s i) ≤ B) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_bounded_affine_minima s.period s.anchor s.positive
    s.squarefree s.anchor_mem s.anchor_gt s.small (energy s 0 + B)
  intro N
  exact (signed_weighted_bound s N).trans (add_le_add le_rfl (hbudget N))

/-- Absolute weighted summability is sufficient, but the signed criterion is weaker. -/
theorem rh_of_weighted_partial_sums (s : Schedule) (B : ℝ)
    (hbudget : ∀ N, ∑ i ∈ Finset.range N, weightedDefect s i ≤ B) :
    RiemannHypothesis := by
  apply rh_of_weighted_defect_budget s B
  intro N
  apply le_trans (Finset.sum_le_sum (fun i _ =>
    sub_le_self (weightedDefect s i) (sq_nonneg _))) (hbudget N)

/-- It suffices to bound the signed balance at cofinal block endpoints.
No bound on the intermediate head energies is assumed. -/
theorem rh_of_cofinal_signed_budget (s : Schedule) (k : ℕ → ℕ)
    (hk : ∀ j, j ≤ k j) (B : ℝ)
    (hbudget : ∀ j, ∑ i ∈ Finset.range (k j), (cost s i - gain s i) ≤ B) :
    RiemannHypothesis := by
  let F : ℕ → QHilbert := fun j =>
    optimizer (k j + 1) (s.period (k j)) (s.anchor (k j)) (s.anchor_mem (k j))
  have hf (j : ℕ) := optimizer_feasible (k j + 1) (s.period (k j)) (s.anchor (k j))
    (Nat.succ_pos _) (s.positive (k j)) (s.anchor_mem (k j))
    (s.anchor_gt (k j)) (s.small (k j))
  have hl : ∀ j, F j ∈ qSquarefreeCRTSpan := fun j =>
    QSquarefreeLatticePackets.divisorStage_le_squarefreeSpan
      (s.period (k j)) (s.positive (k j)) (s.squarefree (k j)) (hf j).1
  have hb : ∀ j, ‖qOne - F j‖^2 ≤ energy s 0 + B := by
    intro j
    change energy s (k j) ≤ _
    rw [signed_balance_eq]
    exact add_le_add le_rfl (hbudget j)
  have hh : ∀ j n, 0 < n → n ≤ j → qSequence (F j) n = 1 := by
    intro j n hn hnj
    exact (hf j).2 n hn (by have := hk j; omega)
  exact (QSquarefreeExactHeadAverages.squarefree_closure_capacity_and_rh_of_bounded_exact_heads
    F hl hb hh).2.2

end RiemannResearch.RH.QSquarefreeBlockBalance
