/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Exact Cesaro inversion and finite Mellin summation by parts, with boundary terms. -/
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.Probability.ConditionalIID

def cesaro (F : ℕ → ℝ) (t : ℕ) : ℝ := (∑ n ∈ Finset.Icc 1 t, F n) / (t : ℝ)

end RiemannResearch.Probability.ConditionalIID

namespace RiemannResearch.Analysis.Cesaro

/-- Positive-index partial sums; the zero coordinate is never sampled. -/
def partialSum (F : ℕ → ℂ) (N : ℕ) : ℂ := ∑ k ∈ Finset.range N, F (k + 1)

def mean (F : ℕ → ℂ) (N : ℕ) : ℂ := partialSum F N / (N : ℂ)

@[simp] theorem prefix_zero (F : ℕ → ℂ) : partialSum F 0 = 0 := by simp [partialSum]

@[simp] theorem prefix_succ (F : ℕ → ℂ) (N : ℕ) :
    partialSum F (N + 1) = partialSum F N + F (N + 1) := by
  simp only [partialSum, Finset.sum_range_succ]

/-- The complex convention agrees with the arithmetic interval convention. -/
theorem prefix_eq_Icc (F : ℕ → ℂ) (N : ℕ) :
    partialSum F N = ∑ n ∈ Finset.Icc 1 N, F n := by
  induction N with
  | zero => simp [partialSum]
  | succ N ih =>
    rw [prefix_succ, Finset.sum_Icc_succ_top (by omega), ih]

theorem mean_ofReal (F : ℕ → ℝ) (N : ℕ) :
    mean (fun n => (F n : ℂ)) N =
      (Probability.ConditionalIID.cesaro F N : ℂ) := by
  simp [mean, prefix_eq_Icc, Probability.ConditionalIID.cesaro]

@[simp] theorem mean_zero (F : ℕ → ℂ) : mean F 0 = 0 := by simp [mean]

/-- There is no division by zero in the positive-index inversion. -/
theorem nat_mul_mean (F : ℕ → ℂ) (N : ℕ) :
    (N : ℂ) * mean F N = partialSum F N := by
  cases N with
  | zero => simp
  | succ N =>
    have hn : ((N + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
    unfold mean
    field_simp

/-- Cesaro averaging loses no algebraic information at positive indices. -/
theorem recover (F : ℕ → ℂ) (N : ℕ) :
    F (N + 1) = ((N + 1 : ℕ) : ℂ) * mean F (N + 1) - (N : ℂ) * mean F N := by
  rw [nat_mul_mean, nat_mul_mean, prefix_succ]
  ring

theorem mean_injective_on_positive {F G : ℕ → ℂ}
    (h : mean F = mean G) (N : ℕ) : F (N + 1) = G (N + 1) := by
  rw [recover F N, recover G N, h]

/-- Exact finite Abel summation; the terminal contribution is retained. -/
theorem finite_abel (a F : ℕ → ℂ) (N : ℕ) :
    partialSum (fun n => a n * F n) N =
      partialSum (fun n => (a n - a (n + 1)) * partialSum F n) N + a (N + 1) * partialSum F N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [prefix_succ, prefix_succ, ih, prefix_succ]
    ring

/-- Exact finite Cesaro-Mellin bridge, before taking any infinite limits. -/
theorem finite_cesaro_abel (a F : ℕ → ℂ) (N : ℕ) :
    partialSum (fun n => a n * F n) N =
      partialSum (fun n => ((n : ℂ) * (a n - a (n + 1))) * mean F n) N +
        (N : ℂ) * a (N + 1) * mean F N := by
  have he : (fun n => (a n - a (n + 1)) * partialSum F n) =
      (fun n : ℕ => ((n : ℂ) * (a n - a (n + 1))) * mean F n) := by
    funext n
    rw [← nat_mul_mean F n]
    ring
  rw [finite_abel, he, ← nat_mul_mean F N]
  ring

/-- The exact partial sum of the weighted second differences. -/
theorem weighted_second_difference_prefix (z : ℕ → ℂ) (N : ℕ) :
    partialSum (fun n => (n : ℂ) * ((z n - z (n + 1)) -
      (z (n + 1) - z (n + 2)))) N =
        z 1 - z (N + 1) - (N : ℂ) * (z (N + 1) - z (N + 2)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [prefix_succ, ih]
    push_cast
    simp only [Nat.add_assoc]
    ring

/-- First difference of the Mellin power. -/
def mellinFirst (s : ℂ) (n : ℕ) : ℂ :=
  (n : ℂ) ^ (-s) - ((n + 1 : ℕ) : ℂ) ^ (-s)

/-- The transformed dual coefficient after Cesaro averaging. -/
def mellinSecond (s : ℂ) (n : ℕ) : ℂ :=
  (n : ℂ) * (mellinFirst s n - mellinFirst s (n + 1))

/-- The actual power coefficients satisfy the finite pairing identity with boundary term. -/
theorem mellin_pairing_prefix (s : ℂ) (F : ℕ → ℂ) (N : ℕ) :
    partialSum (fun n => mellinFirst s n * F n) N =
      partialSum (fun n => mellinSecond s n * mean F n) N +
        (N : ℂ) * mellinFirst s (N + 1) * mean F N :=
  finite_cesaro_abel (mellinFirst s) F N

/-- Exact coefficient normalization, prior to proving decay of the boundary term. -/
theorem mellinSecond_prefix (s : ℂ) (N : ℕ) :
    partialSum (mellinSecond s) N =
      1 - ((N + 1 : ℕ) : ℂ) ^ (-s) - (N : ℂ) * mellinFirst s (N + 1) := by
  change partialSum (fun n => mellinSecond s n) N = _
  simpa [mellinSecond, mellinFirst, Nat.add_assoc] using
    weighted_second_difference_prefix (fun n => (n : ℂ) ^ (-s)) N

/-- Bounded arithmetic functions have uniformly bounded Cesaro means. -/
theorem mean_norm_le (F : ℕ → ℂ) (B : ℝ)
    (hB : ∀ n, 0 < n → ‖F n‖ ≤ B) (N : ℕ) (hN : 0 < N) : ‖mean F N‖ ≤ B := by
  rw [mean, norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ (show (0 : ℝ) < N by exact_mod_cast hN)).2
  calc
    ‖partialSum F N‖ ≤ ∑ k ∈ Finset.range N, ‖F (k + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range N, B := Finset.sum_le_sum (fun k _ => hB _ (Nat.succ_pos k))
    _ = B * (N : ℝ) := by simp [mul_comm]

end RiemannResearch.Analysis.Cesaro
