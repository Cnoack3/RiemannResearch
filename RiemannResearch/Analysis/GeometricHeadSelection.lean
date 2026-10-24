/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# An online integer selection of physical head lengths

Source: user-provided `RH_Constructive_Approximants_Research_Agenda_2026-10-24`,
Section 8.2. Certified integer physical-amplitude bounds replace exact real
ceilings. The state remembers the largest squared amplitude seen so far.

The recurrence is computable when the amplitude bound is computable. It uses
only previously selected candidates and does not use a uniform Hilbert norm
bound. Its concrete consumer is `ParetoExactHeadPairings`.
-/

namespace RiemannResearch.Analysis

/-- State = (current head length, maximum squared amplitude seen so far). -/
def exactHeadSelectionState (U : ℕ → ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, U 1 ^ 2)
  | j + 1 =>
      let s := exactHeadSelectionState U j
      let n := max (s.1 + 1) (4 ^ (j + 2) * s.2)
      (n, max s.2 (U n ^ 2))

def exactHeadSelection (U : ℕ → ℕ) (j : ℕ) : ℕ :=
  (exactHeadSelectionState U j).1

def exactHeadSelectionBudget (U : ℕ → ℕ) (j : ℕ) : ℕ :=
  (exactHeadSelectionState U j).2

@[simp] theorem exactHeadSelection_zero (U : ℕ → ℕ) :
    exactHeadSelection U 0 = 1 := rfl

theorem exactHeadSelectionBudget_contains_current (U : ℕ → ℕ) (j : ℕ) :
    U (exactHeadSelection U j) ^ 2 ≤ exactHeadSelectionBudget U j := by
  cases j with
  | zero => exact le_rfl
  | succ j => exact le_max_right _ _

theorem exactHeadSelectionBudget_monotone (U : ℕ → ℕ) :
    Monotone (exactHeadSelectionBudget U) := by
  apply monotone_nat_of_le_succ
  intro j
  exact le_max_left _ _

theorem exactHeadSelection_strictMono (U : ℕ → ℕ) :
    StrictMono (exactHeadSelection U) := by
  apply strictMono_nat_of_lt_succ
  intro j
  exact (Nat.lt_succ_self _).trans_le (le_max_left _ _)

theorem exactHeadSelection_succ_ge_budget (U : ℕ → ℕ) (j : ℕ) :
    4 ^ (j + 2) * exactHeadSelectionBudget U j ≤ exactHeadSelection U (j + 1) :=
  le_max_right _ _

/-- Every later selected head dominates the required geometric multiple of
every earlier candidate's certified amplitude. -/
theorem exactHeadSelection_dominates_earlier_amplitude
    (U : ℕ → ℕ) {i j : ℕ} (hij : i < j) :
    4 ^ (j + 1) * U (exactHeadSelection U i) ^ 2 ≤ exactHeadSelection U j := by
  cases j with
  | zero => omega
  | succ j =>
      have hU : U (exactHeadSelection U i) ^ 2 ≤ exactHeadSelectionBudget U j :=
        (exactHeadSelectionBudget_contains_current U i).trans
          (exactHeadSelectionBudget_monotone U (Nat.le_of_lt_succ hij))
      exact (Nat.mul_le_mul_left (4 ^ (j + 2)) hU).trans
        (exactHeadSelection_succ_ge_budget U j)

/-- Real-valued certificate consumed by the complete-tail pairing estimate. -/
theorem exactHeadSelection_real_certificate
    (U : ℕ → ℕ) {i j : ℕ} (hij : i < j) :
    (U (exactHeadSelection U i) : ℝ) ^ 2 ≤
      ((exactHeadSelection U j : ℝ) + 1) * ((1 / 2 : ℝ) ^ (j + 1)) ^ 2 := by
  have hb : (4 : ℝ) ^ (j + 1) * (U (exactHeadSelection U i) : ℝ) ^ 2 ≤
      (exactHeadSelection U j : ℝ) := by
    exact_mod_cast exactHeadSelection_dominates_earlier_amplitude U hij
  have hc : (4 : ℝ) ^ (j + 1) * ((1 / 2 : ℝ) ^ (j + 1)) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm (j + 1) 2, pow_mul, ← mul_pow]
    norm_num
  calc
    (U (exactHeadSelection U i) : ℝ) ^ 2 =
        ((4 : ℝ) ^ (j + 1) * (U (exactHeadSelection U i) : ℝ) ^ 2) *
          ((1 / 2 : ℝ) ^ (j + 1)) ^ 2 := by
      calc
        _ = (U (exactHeadSelection U i) : ℝ) ^ 2 *
            ((4 : ℝ) ^ (j + 1) * ((1 / 2 : ℝ) ^ (j + 1)) ^ 2) := by
          rw [hc, mul_one]
        _ = _ := by ring
    _ ≤ (exactHeadSelection U j : ℝ) * ((1 / 2 : ℝ) ^ (j + 1)) ^ 2 :=
      mul_le_mul_of_nonneg_right hb (sq_nonneg _)
    _ ≤ ((exactHeadSelection U j : ℝ) + 1) * ((1 / 2 : ℝ) ^ (j + 1)) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact le_add_of_nonneg_right zero_le_one

end RiemannResearch.Analysis
