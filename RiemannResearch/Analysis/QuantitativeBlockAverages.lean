/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.BoundedMomentAverages
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Quantitative block averages from pairwise geometric control

Source: user-provided `RH_Constructive_Approximants_Research_Agenda_2026-10-24`
handoff, Section 8, for the pairwise geometric control and averaging strategy.
The finite geometric correction and its dependence on the block offset are
derived here. The concrete RH consumer is averaging bounded legal exact-head
residuals in the complete P or Q Hilbert space.

The complete signed Gram equality is reused from `BoundedMomentAverages`.
Only an upper bound on each signed pairing is needed for the estimates.
These estimates do not establish the uniform arithmetic energy bound or the
pairwise bounds for a specified legal arithmetic family.
-/

open scoped BigOperators

namespace RiemannResearch.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact finite geometric correction, including its boundary term. -/
theorem sum_range_mul_half_pow_succ (m : ℕ) :
    (∑ j ∈ Finset.range m, (j : ℝ) * (1 / 2 : ℝ) ^ (j + 1)) =
      1 - ((m : ℝ) + 1) * (1 / 2 : ℝ) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [Nat.cast_succ, pow_succ]
      ring

/-- Signed pairwise bounds give the exact finite upper bound on the entire
off-diagonal contribution of a block starting at offset a. -/
theorem prefixCross_shift_le_of_pairwise_geometric
    (u : ℕ → E) (C : ℝ)
    (hcross : ∀ i j, i < j →
      inner ℝ (u i) (u j) ≤ C * (1 / 2 : ℝ) ^ (j + 1))
    (a m : ℕ) :
    prefixCross (fun i => u (a + i)) m ≤
      C * (1 / 2 : ℝ) ^ a *
        (1 - ((m : ℝ) + 1) * (1 / 2 : ℝ) ^ m) := by
  have hrow (j : ℕ) :
      inner ℝ (∑ i ∈ Finset.range j, u (a + i)) (u (a + j)) ≤
        (j : ℝ) * C * (1 / 2 : ℝ) ^ (a + j + 1) := by
    rw [sum_inner]
    calc
      _ ≤ ∑ _i ∈ Finset.range j,
          C * (1 / 2 : ℝ) ^ (a + j + 1) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hcross (a + i) (a + j)
          (Nat.add_lt_add_left (Finset.mem_range.mp hi) a)
      _ = _ := by simp [mul_assoc]
  calc
    prefixCross (fun i => u (a + i)) m ≤
        ∑ j ∈ Finset.range m,
          (j : ℝ) * C * (1 / 2 : ℝ) ^ (a + j + 1) :=
      Finset.sum_le_sum (fun j _ => hrow j)
    _ = C * (1 / 2 : ℝ) ^ a *
        (∑ j ∈ Finset.range m, (j : ℝ) * (1 / 2 : ℝ) ^ (j + 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [show a + j + 1 = a + (j + 1) by omega, pow_add]
      ring
    _ = _ := by rw [sum_range_mul_half_pow_succ]

/-- Exact complete block energy before any diagonal or mixed term is bounded. -/
theorem norm_sq_block_average_exact (u : ℕ → E) (a m : ℕ) :
    ‖((m : ℝ)⁻¹) • (∑ i ∈ Finset.range m, u (a + i))‖ ^ 2 =
      ((m : ℝ)⁻¹) ^ 2 *
        ((∑ i ∈ Finset.range m, ‖u (a + i)‖ ^ 2) +
          2 * prefixCross (fun i => u (a + i)) m) := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    norm_sq_sum_range_eq_diagonal_add_cross]

/-- Finite quantitative block estimate with its exact geometric boundary term.
The diagonal energy B and pairwise constant C are separate hypotheses. -/
theorem norm_sq_block_average_le_of_pairwise_geometric
    (u : ℕ → E) {B C : ℝ}
    (hbound : ∀ n, ‖u n‖ ^ 2 ≤ B)
    (hcross : ∀ i j, i < j →
      inner ℝ (u i) (u j) ≤ C * (1 / 2 : ℝ) ^ (j + 1))
    (a : ℕ) {m : ℕ} (hm : 0 < m) :
    ‖((m : ℝ)⁻¹) • (∑ i ∈ Finset.range m, u (a + i))‖ ^ 2 ≤
      B / m +
        2 * C * (1 / 2 : ℝ) ^ a *
          (1 - ((m : ℝ) + 1) * (1 / 2 : ℝ) ^ m) / (m : ℝ) ^ 2 := by
  have hdiag : (∑ i ∈ Finset.range m, ‖u (a + i)‖ ^ 2) ≤
      (m : ℝ) * B := by
    calc
      _ ≤ ∑ _i ∈ Finset.range m, B :=
        Finset.sum_le_sum (fun i _ => hbound (a + i))
      _ = _ := by simp
  have hcross' := prefixCross_shift_le_of_pairwise_geometric u C hcross a m
  have hsum :
      (∑ i ∈ Finset.range m, ‖u (a + i)‖ ^ 2) +
        2 * prefixCross (fun i => u (a + i)) m ≤
      (m : ℝ) * B + 2 * C * (1 / 2 : ℝ) ^ a *
        (1 - ((m : ℝ) + 1) * (1 / 2 : ℝ) ^ m) := by
    linarith
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  rw [norm_sq_block_average_exact]
  calc
    _ ≤ ((m : ℝ)⁻¹) ^ 2 * ((m : ℝ) * B +
        2 * C * (1 / 2 : ℝ) ^ a *
          (1 - ((m : ℝ) + 1) * (1 / 2 : ℝ) ^ m)) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = _ := by field_simp [hm']

/-- Removing only the nonnegative finite boundary correction gives a simple
rate; moving the block to offset m multiplies the mixed-term budget by 2^-m. -/
theorem norm_sq_block_average_le_simple
    (u : ℕ → E) {B C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n, ‖u n‖ ^ 2 ≤ B)
    (hcross : ∀ i j, i < j →
      inner ℝ (u i) (u j) ≤ C * (1 / 2 : ℝ) ^ (j + 1))
    (a : ℕ) {m : ℕ} (hm : 0 < m) :
    ‖((m : ℝ)⁻¹) • (∑ i ∈ Finset.range m, u (a + i))‖ ^ 2 ≤
      B / m + 2 * C * (1 / 2 : ℝ) ^ a / (m : ℝ) ^ 2 := by
  have hfac : 1 - ((m : ℝ) + 1) * (1 / 2 : ℝ) ^ m ≤ 1 := by
    have hp : 0 ≤ ((m : ℝ) + 1) * (1 / 2 : ℝ) ^ m := by positivity
    linarith
  have hnonneg : 0 ≤ 2 * C * (1 / 2 : ℝ) ^ a := by positivity
  apply (norm_sq_block_average_le_of_pairwise_geometric u hbound hcross a hm).trans
  apply add_le_add_right
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hfac hnonneg

end RiemannResearch.Analysis
