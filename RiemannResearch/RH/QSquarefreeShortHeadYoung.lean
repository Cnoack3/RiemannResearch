/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.WeightedYoungConstant
import RiemannResearch.RH.QSquarefreeShortHeadBlocks
import RiemannResearch.RH.QSquarefreeShortHeadResponse
import RiemannResearch.RH.QSquarefreeShortHeadCriterion
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Parameterized short-head block comparison with exact loss
Source: direct refinement of the squared-triangle comparison in
SquarefreeShortHeadSchurResearch20261030.md, section 6.
The parameter is deterministic; the actual signed source is unchanged.
The scalar optimization is imported from `Analysis/WeightedYoungConstant.lean`
and instantiated below for the actual canonical response and complete tail.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeShortHeadBlocks
open ZetaTwoHilbert ZetaTwoProbability
open RiemannResearch.Analysis.WeightedYoungConstant
open QSquarefreeSmoothedProjection QSquarefreeShortHeadResponse QSquarefreeShortHeadCriterion

/-- Exact weighted-Young accounting for the actual finite response block. -/
theorem block_energy_young_exact (N M H : ℕ) (t : ℝ) (ht : t ≠ 0) :
    (∑ i ∈ Finset.range M, qSequence (movingCorrection N) (M + i + 1) ^ 2) =
      (1 + t) * (∑ i ∈ Finset.range M, response N H (M + i + 1) ^ 2) +
      (1 + 1 / t) * (∑ i ∈ Finset.range M,
        (qSequence (movingCorrection N) (M + i + 1) - response N H (M + i + 1)) ^ 2) -
      (1 / t) * (∑ i ∈ Finset.range M,
        (t * response N H (M + i + 1) -
          (qSequence (movingCorrection N) (M + i + 1) - response N H (M + i + 1))) ^ 2) := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  field_simp [ht] <;> ring

theorem block_remainder_energy_le (N M : ℕ) (hM : 0 < M) :
    (∑ i ∈ Finset.range M,
      (qSequence (movingCorrection N) (M + i + 1) -
        response N (logarithmicCutoff M) (M + i + 1)) ^ 2) ≤
      4 * zetaTwo * (M : ℝ) * (6 + Real.log (M : ℝ)) ^ 2 := by
  let L : ℝ := 6 + Real.log (M : ℝ)
  have hz := zetaTwo_pos
  have hterm (i : ℕ) (hi : i ∈ Finset.range M) :
      (qSequence (movingCorrection N) (M + i + 1) -
        response N (logarithmicCutoff M) (M + i + 1)) ^ 2 ≤ 4 * zetaTwo * L ^ 2 := by
    have he := block_remainder_abs_le N M i hM (Finset.mem_range.mp hi)
    have hs := mul_self_le_mul_self
      (abs_nonneg (qSequence (movingCorrection N) (M + i + 1) -
        response N (logarithmicCutoff M) (M + i + 1))) he
    have hr := Real.sq_sqrt hz.le
    have heq : (2 * Real.sqrt zetaTwo * L) ^ 2 = 4 * zetaTwo * L ^ 2 := by
      rw [mul_pow, mul_pow, hr]
      ring
    nlinarith [sq_abs (qSequence (movingCorrection N) (M + i + 1) -
      response N (logarithmicCutoff M) (M + i + 1))]
  calc
    _ ≤ ∑ i ∈ Finset.range M, 4 * zetaTwo * L ^ 2 := Finset.sum_le_sum hterm
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      dsimp [L]
      ring

/-- This improves the constant 2*C+8*zetaTwo and retains an additional
nonnegative loss square on the left. Set t=1 to recover the earlier estimate. -/
theorem full_block_meanSquare_young_with_loss_le
    (N M m : ℕ) (hM : 0 < M) (C t : ℝ) (hC : 0 ≤ C) (ht : 0 < t)
    (hb : (∑ i ∈ Finset.range M,
      response N (logarithmicCutoff M) (M + i + 1) ^ 2) ≤
        C * (M : ℝ) * (6 + Real.log (M : ℝ)) ^ (2 * m)) :
    (∑ i ∈ Finset.range M, qSequence (movingCorrection N) (M + i + 1) ^ 2) +
      (1 / t) * (∑ i ∈ Finset.range M,
        (t * response N (logarithmicCutoff M) (M + i + 1) -
          (qSequence (movingCorrection N) (M + i + 1) -
            response N (logarithmicCutoff M) (M + i + 1))) ^ 2) ≤
      ((1 + t) * C + 4 * zetaTwo * (1 + 1 / t)) * (M : ℝ) *
        (6 + Real.log (M : ℝ)) ^ (2 * max m 1) := by
  let L : ℝ := 6 + Real.log (M : ℝ)
  have hz := zetaTwo_pos
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hM1]
  have hp1 : 0 ≤ 1 + t := by linarith
  have hp2 : 0 ≤ 1 + 1 / t := by positivity
  have he := block_energy_young_exact N M (logarithmicCutoff M) t ht.ne'
  have hsum :
      (∑ i ∈ Finset.range M, qSequence (movingCorrection N) (M + i + 1) ^ 2) +
        (1 / t) * (∑ i ∈ Finset.range M,
          (t * response N (logarithmicCutoff M) (M + i + 1) -
            (qSequence (movingCorrection N) (M + i + 1) -
              response N (logarithmicCutoff M) (M + i + 1))) ^ 2) =
      (1 + t) * (∑ i ∈ Finset.range M, response N (logarithmicCutoff M) (M + i + 1) ^ 2) +
      (1 + 1 / t) * (∑ i ∈ Finset.range M,
        (qSequence (movingCorrection N) (M + i + 1) -
          response N (logarithmicCutoff M) (M + i + 1)) ^ 2) := by linarith
  have hm : L ^ (2 * m) ≤ L ^ (2 * max m 1) :=
    pow_le_pow_right₀ hL (Nat.mul_le_mul_left 2 (Nat.le_max_left _ _))
  have h2 : L ^ 2 ≤ L ^ (2 * max m 1) := by
    apply pow_le_pow_right₀ hL
    have h := Nat.le_max_right m 1
    omega
  rw [hsum]
  calc
    _ ≤ (1 + t) * (C * (M : ℝ) * L ^ (2 * m)) +
        (1 + 1 / t) * (4 * zetaTwo * (M : ℝ) * L ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hb hp1)
        (mul_le_mul_of_nonneg_left (block_remainder_energy_le N M hM) hp2)
    _ = ((1 + t) * C * (M : ℝ)) * L ^ (2 * m) +
        (4 * zetaTwo * (1 + 1 / t) * (M : ℝ)) * L ^ 2 := by ring
    _ ≤ ((1 + t) * C * (M : ℝ)) * L ^ (2 * max m 1) +
        (4 * zetaTwo * (1 + 1 / t) * (M : ℝ)) * L ^ (2 * max m 1) :=
      add_le_add (mul_le_mul_of_nonneg_left hm (by positivity))
        (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ = _ := by dsimp [L]; ring

/-- The optimal positive parameter gives the coefficient
`(sqrt C + 2 * sqrt zetaTwo)^2` for the actual block, retaining the loss square.
The arithmetic short-head block bound remains an explicit hypothesis. -/
theorem full_block_meanSquare_optimal_with_loss_le
    (N M m : ℕ) (hM : 0 < M) (C : ℝ) (hC : 0 < C)
    (hb : (∑ i ∈ Finset.range M,
      response N (logarithmicCutoff M) (M + i + 1) ^ 2) ≤
        C * (M : ℝ) * (6 + Real.log (M : ℝ)) ^ (2 * m)) :
    (∑ i ∈ Finset.range M, qSequence (movingCorrection N) (M + i + 1) ^ 2) +
      (1 / (2 * Real.sqrt zetaTwo / Real.sqrt C)) * (∑ i ∈ Finset.range M,
        ((2 * Real.sqrt zetaTwo / Real.sqrt C) *
            response N (logarithmicCutoff M) (M + i + 1) -
          (qSequence (movingCorrection N) (M + i + 1) -
            response N (logarithmicCutoff M) (M + i + 1))) ^ 2) ≤
      (Real.sqrt C + 2 * Real.sqrt zetaTwo) ^ 2 * (M : ℝ) *
        (6 + Real.log (M : ℝ)) ^ (2 * max m 1) := by
  have hsC : 0 < Real.sqrt C := Real.sqrt_pos.mpr hC
  have hsZ : 0 < Real.sqrt zetaTwo := Real.sqrt_pos.mpr zetaTwo_pos
  have ht : 0 < 2 * Real.sqrt zetaTwo / Real.sqrt C := by positivity
  have h := full_block_meanSquare_young_with_loss_le N M m hM C
    (2 * Real.sqrt zetaTwo / Real.sqrt C) hC.le ht hb
  rw [young_constant_at_optimal_parameter C zetaTwo hC zetaTwo_pos] at h
  exact h

/-- A direct optimized comparison of actual full and short-head block energies. -/
theorem full_block_meanSquare_optimal_le
    (N M m : ℕ) (hM : 0 < M) (C : ℝ) (hC : 0 < C)
    (hb : (∑ i ∈ Finset.range M,
      response N (logarithmicCutoff M) (M + i + 1) ^ 2) ≤
        C * (M : ℝ) * (6 + Real.log (M : ℝ)) ^ (2 * m)) :
    (∑ i ∈ Finset.range M, qSequence (movingCorrection N) (M + i + 1) ^ 2) ≤
      (Real.sqrt C + 2 * Real.sqrt zetaTwo) ^ 2 * (M : ℝ) *
        (6 + Real.log (M : ℝ)) ^ (2 * max m 1) := by
  have hsC : 0 < Real.sqrt C := Real.sqrt_pos.mpr hC
  have hsZ : 0 < Real.sqrt zetaTwo := Real.sqrt_pos.mpr zetaTwo_pos
  refine le_trans ?_ (full_block_meanSquare_optimal_with_loss_le N M m hM C hC hb)
  exact le_add_of_nonneg_right (by positivity)

end RiemannResearch.RH.QSquarefreeShortHeadBlocks
