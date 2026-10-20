/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.PrimePowerTargetMellin
import RiemannResearch.RH.PrimePowerHilbertTarget
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.ThresholdHilbertAdjoint
import RiemannResearch.RH.QSquarefreePeriodicJump
import RiemannResearch.RH.SquarefreeRadicalDifference
import RiemannResearch.RH.ZetaTwoParetoTransfer
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Log
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact complete energy of capped prime-power targets

Source: user-provided RH/CRT continuation agenda, Priority 4, and the
prime-power contraction identity in `PrimePowerHilbertTarget`.
These are ambient approximants. No legal closure membership is claimed.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.PrimePowerTarget
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QParetoEquivalence

/-- The exact error left after capping the logarithmic target at k. -/
def paretoCapError (p : ℕ) (hp : 1 < p) (k : ℕ) : ThresholdHilbert :=
  unscaledDilation (p ^ k) (pow_pos (by omega) _) (paretoTarget p hp)

def paretoCappedTarget (p : ℕ) (hp : 1 < p) (k : ℕ) : ThresholdHilbert :=
  paretoTarget p hp - paretoCapError p hp k

theorem paretoCapError_sequence (p : ℕ) (hp : 1 < p) (k n : ℕ) :
    hilbertSequence (paretoCapError p hp k) n = (Nat.log p n - k : ℕ) := by
  rw [paretoCapError, unscaledDilation_sequence, paretoTarget_sequence,
    Nat.log_div_base_pow]

theorem paretoCappedTarget_sequence (p : ℕ) (hp : 1 < p) (k n : ℕ) :
    hilbertSequence (paretoCappedTarget p hp k) n = (min (Nat.log p n) k : ℕ) := by
  rw [paretoCappedTarget, hilbertSequence_sub, Pi.sub_apply, paretoTarget_sequence,
    paretoCapError_sequence, ← Nat.cast_sub (Nat.sub_le (Nat.log p n) k)]
  congr 1
  omega

theorem paretoCapError_norm_sq (p : ℕ) (hp : 1 < p) (k : ℕ) :
    ‖paretoCapError p hp k‖ ^ 2 =
      (((p : ℝ) + 1) / ((p : ℝ) - 1) ^ 2) / (p : ℝ) ^ k := by
  rw [paretoCapError, unscaledDilation_norm_sq, paretoTarget_norm_sq, Nat.cast_pow]

theorem paretoCappedTarget_error_exact (p : ℕ) (hp : 1 < p) (k : ℕ) :
    ‖paretoTarget p hp - paretoCappedTarget p hp k‖ ^ 2 =
      (((p : ℝ) + 1) / ((p : ℝ) - 1) ^ 2) / (p : ℝ) ^ k := by
  simpa only [paretoCappedTarget, sub_sub_cancel] using paretoCapError_norm_sq p hp k

def qCappedTarget (p : ℕ) (hp : 1 < p) (k : ℕ) : QHilbert :=
  toQ (paretoCappedTarget p hp k)

theorem qCappedTarget_sequence (p : ℕ) (hp : 1 < p) (k n : ℕ) :
    qSequence (qCappedTarget p hp k) n = (min (Nat.log p n) k : ℕ) := by
  rw [qCappedTarget, toQ_sequence, paretoCappedTarget_sequence]

theorem toPareto_qCappedTarget (p : ℕ) (hp : 1 < p) (k : ℕ) :
    toPareto (qCappedTarget p hp k) = paretoCappedTarget p hp k := by
  exact toPareto_toQ _

theorem qCappedTarget_error_lower (p : ℕ) (hp : 1 < p) (k : ℕ) :
    (((p : ℝ) + 1) / ((p : ℝ) - 1) ^ 2) / (p : ℝ) ^ k ≤
      zetaTwo * ‖qTarget p hp - qCappedTarget p hp k‖ ^ 2 := by
  have h := toPareto_norm_sq_le (qTarget p hp - qCappedTarget p hp k)
  have he : toPareto (qTarget p hp - qCappedTarget p hp k) =
      paretoTarget p hp - paretoCappedTarget p hp k := by
    change toParetoLinear (qTarget p hp - qCappedTarget p hp k) = _
    rw [map_sub]
    exact congrArg₂ (· - ·) (toPareto_qTarget p hp) (toPareto_qCappedTarget p hp k)
  rw [he, paretoCappedTarget_error_exact] at h
  exact h

theorem qCappedTarget_error_upper (p : ℕ) (hp : 1 < p) (k : ℕ) :
    zetaTwo * ‖qTarget p hp - qCappedTarget p hp k‖ ^ 2 ≤
      2 * ((((p : ℝ) + 1) / ((p : ℝ) - 1) ^ 2) / (p : ℝ) ^ k) := by
  have h := zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq
    (qTarget p hp - qCappedTarget p hp k)
  have he : toPareto (qTarget p hp - qCappedTarget p hp k) =
      paretoTarget p hp - paretoCappedTarget p hp k := by
    change toParetoLinear (qTarget p hp - qCappedTarget p hp k) = _
    rw [map_sub]
    exact congrArg₂ (· - ·) (toPareto_qTarget p hp) (toPareto_qCappedTarget p hp k)
  rw [he, paretoCappedTarget_error_exact] at h
  exact h

theorem qCappedTarget_error_sq_tendsto_zero (p : ℕ) (hp : 1 < p) :
    Tendsto (fun k => ‖qTarget p hp - qCappedTarget p hp k‖ ^ 2) atTop (𝓝 0) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hpR0 : (0 : ℝ) < p := by linarith
  have hgeom : Tendsto (fun k : ℕ => ((p : ℝ)⁻¹) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      ((inv_lt_one₀ hpR0).2 hpR)
  have hupper : Tendsto
      (fun k : ℕ => 2 * ((((p : ℝ) + 1) / ((p : ℝ) - 1) ^ 2) / (p : ℝ) ^ k))
      atTop (𝓝 0) := by
    convert hgeom.const_mul (2 * (((p : ℝ) + 1) / ((p : ℝ) - 1) ^ 2)) using 1
    · funext k
      rw [inv_pow]
      ring
    · simp
  have hweighted : Tendsto
      (fun k => zetaTwo * ‖qTarget p hp - qCappedTarget p hp k‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun k => mul_nonneg zetaTwo_pos.le (sq_nonneg _))
      (qCappedTarget_error_upper p hp) hupper
  have h := hweighted.div_const zetaTwo
  simpa [ne_of_gt zetaTwo_pos] using h

theorem qCappedTarget_jump_at_base (p : ℕ) (hp : 1 < p) (k : ℕ) (hk : 1 ≤ k) :
    SquarefreeRadicalDifference.qDifference (qCappedTarget p hp k) p = 1 := by
  have hlog : Nat.log p p = 1 := by simpa using Nat.log_pow hp 1
  simp [SquarefreeRadicalDifference.qDifference, qCappedTarget_sequence,
    hlog, Nat.log_of_lt (by omega : p - 1 < p), min_eq_left hk]

theorem qCappedTarget_jump_at_later_power (p : ℕ) (hp : 1 < p) (k : ℕ) :
    SquarefreeRadicalDifference.qDifference (qCappedTarget p hp k) (p ^ (k + 1)) = 0 := by
  have hpow : p ^ k ≤ p ^ (k + 1) - 1 := by
    have hpos : 0 < p ^ k := pow_pos (by omega) _
    rw [pow_succ]
    have hmul : p ^ k < p ^ k * p := by nlinarith
    omega
  have hlog : k ≤ Nat.log p (p ^ (k + 1) - 1) := Nat.le_log_of_pow_le hp hpow
  simp [SquarefreeRadicalDifference.qDifference, qCappedTarget_sequence,
    Nat.log_pow hp, min_eq_right hlog]

/-- Every nonzero finite cap violates a necessary closed squarefree jump relation.
Its ambient norm convergence cannot be used as legal approximation. -/
theorem qCappedTarget_not_mem_squarefreeClosure
    (p : ℕ) (hp : 1 < p) (k : ℕ) (hk : 1 ≤ k) :
    qCappedTarget p hp k ∉ ZetaTwoProbability.qSquarefreeCRTSpan.topologicalClosure := by
  intro hmem
  have h := QSquarefreePeriodicJump.squarefree_closure_difference_pow
    p (k + 1) (by omega) (by omega) (qCappedTarget p hp k) hmem
  rw [qCappedTarget_jump_at_later_power, qCappedTarget_jump_at_base p hp k hk] at h
  norm_num at h

end RiemannResearch.RH.PrimePowerTarget
