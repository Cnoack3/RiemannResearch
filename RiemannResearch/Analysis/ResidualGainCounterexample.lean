/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ResidualGainProduct
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Positive relative gains need not exhaust the initial error

Source: elementary telescoping-product counterexample for the prime-block
research agenda (4 November 2026). This is an abstract scalar counterexample,
not an assertion about the actual arithmetic projection gains.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.Analysis.ResidualGain

/-- Positive gains may leave one half of the initial error forever. -/
def stallingGain (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2) ^ 2
def stallingError (n : ℕ) : ℝ := ((n : ℝ) + 2) / (2 * ((n : ℝ) + 1))

theorem stallingGain_pos (n : ℕ) : 0 < stallingGain n := by
  unfold stallingGain
  positivity

theorem stallingGain_lt_one (n : ℕ) : stallingGain n < 1 := by
  unfold stallingGain
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  apply (div_lt_one (by positivity : 0 < ((n : ℝ) + 2) ^ 2)).mpr
  nlinarith

theorem stallingError_step (n : ℕ) :
    stallingError (n + 1) = stallingError n * (1 - stallingGain n) := by
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  simp only [stallingError, stallingGain, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

theorem stallingError_lower (n : ℕ) : (1 : ℝ) / 2 ≤ stallingError n := by
  unfold stallingError
  apply (le_div_iff₀ (by positivity : 0 < 2 * ((n : ℝ) + 1))).mpr
  linarith

theorem stallingError_not_tendsto_zero :
    ¬ Tendsto stallingError atTop (𝓝 0) := by
  intro hz
  have hh := ge_of_tendsto hz
    (Filter.Eventually.of_forall stallingError_lower)
  norm_num at hh

theorem positive_gains_do_not_imply_exhaustion :
    ∃ d r : ℕ → ℝ, d 0 = 1 ∧ (∀ n, 0 < r n ∧ r n < 1) ∧
      (∀ n, d (n + 1) = d n * (1 - r n)) ∧
      ¬ Tendsto d atTop (𝓝 0) := by
  refine ⟨stallingError, stallingGain, ?_, ?_, stallingError_step,
    stallingError_not_tendsto_zero⟩
  · norm_num [stallingError]
  · intro n
    exact ⟨stallingGain_pos n, stallingGain_lt_one n⟩

end RiemannResearch.Analysis.ResidualGain
