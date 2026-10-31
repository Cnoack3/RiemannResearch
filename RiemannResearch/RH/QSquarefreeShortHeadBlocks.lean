/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeShortHeadResponse
import RiemannResearch.RH.QSquarefreeShortHeadCriterion
import RiemannResearch.RH.QSquarefreeDyadicMeanSquare
import RiemannResearch.RH.QSquarefreeKernelLocalization
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.RH.QAnnihilatorTailEscape
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.Analysis.ResidualizedProjectionKernel
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Common-cutoff short-head block criterion
Source: SquarefreeShortHeadSchurResearch20261030.md, section 6.
All sources, kernels, and residuals use the complete canonical squarefree
dictionary. The common arithmetic block envelope remains Open.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QSquarefreeShortHeadBlocks
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage
open QSquarefreeSmoothedProjection QSquarefreeCorrectionKernel
open QSquarefreeShortHeadResponse QSquarefreeShortHeadCriterion
open QSquarefreeDyadicMeanSquare QFiniteSupportDualCriterion QAnnihilatorTailEscape
open RiemannResearch.Analysis.ResidualizedProjectionKernel

/-- Exact finite block accounting retains the nonnegative loss square before
the squared-triangle estimate is applied. -/
theorem block_energy_exact (N M H : ℕ) :
    (∑ i ∈ Finset.range M, qSequence (movingCorrection N) (M + i + 1) ^ 2) =
      2 * (∑ i ∈ Finset.range M, response N H (M + i + 1) ^ 2) +
      2 * (∑ i ∈ Finset.range M,
        (qSequence (movingCorrection N) (M + i + 1) - response N H (M + i + 1)) ^ 2) -
      (∑ i ∈ Finset.range M,
        (qSequence (movingCorrection N) (M + i + 1) - 2 * response N H (M + i + 1)) ^ 2) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- One logarithmic cutoff works for the whole physical block (M,2M]. -/
theorem logarithmicCutoff_block_scale (M i : ℕ) (hM : 0 < M) (hi : i < M) :
    ((M + i : ℕ) : ℝ) + 2 ≤
      (2 * (6 + Real.log (M : ℝ)) + 1) * ((logarithmicCutoff M : ℝ) + 2) := by
  let L : ℝ := 6 + Real.log (M : ℝ)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hM1]
  have hLp : 0 < L := by linarith
  have hf : (M : ℝ) / L < (logarithmicCutoff M : ℝ) + 1 := Nat.lt_floor_add_one _
  have hm := (div_lt_iff₀ hLp).mp hf
  have hH := Nat.cast_nonneg (α := ℝ) (logarithmicCutoff M)
  have hidx : ((M + i : ℕ) : ℝ) + 2 ≤ 2 * (M : ℝ) + 1 := by
    exact_mod_cast (show M + i + 2 ≤ 2 * M + 1 by omega)
  change ((M + i : ℕ) : ℝ) + 2 ≤ (2 * L + 1) * ((logarithmicCutoff M : ℝ) + 2)
  nlinarith

/-- Complete-tail localization is uniform in the canonical stage and over the
whole block. This is independent of the open short-head estimate. -/
theorem block_remainder_abs_le (N M i : ℕ) (hM : 0 < M) (hi : i < M) :
    |qSequence (movingCorrection N) (M + i + 1) -
        response N (logarithmicCutoff M) (M + i + 1)| ≤
      2 * Real.sqrt zetaTwo * (6 + Real.log (M : ℝ)) := by
  let L : ℝ := 6 + Real.log (M : ℝ)
  have hz := zetaTwo_pos
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hM1]
  have hr : ‖residual N‖ ^ 2 ≤ 1 := by
    have hp := residual_norm_sq (stage N) qOne
    rw [qOne_norm] at hp
    change ‖residual N‖ ^ 2 = _ at hp
    nlinarith [sq_nonneg ‖(stage N).starProjection qOne‖]
  have htail : ‖tail (logarithmicCutoff M) (residual N)‖ ^ 2 ≤ 1 := by
    have ht := tail_norm_le (logarithmicCutoff M) (residual N)
    nlinarith [norm_nonneg (tail (logarithmicCutoff M) (residual N)),
      norm_nonneg (residual N)]
  have he := movingCorrection_relativeHead_remainder_sq_le N (M + i)
    (logarithmicCutoff M) (2 * L) (by linarith)
    (logarithmicCutoff_block_scale M i hM hi)
  have heq := response_eq_head_pairing N (logarithmicCutoff M) (M + i + 1)
  norm_num only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] at heq
  have hcenter : ((M + i : ℕ) : ℝ) + 2 = (M : ℝ) + ((i : ℝ) + 2) := by push_cast; ring
  rw [hcenter] at he
  simp only [Nat.add_assoc] at he heq
  rw [← heq] at he
  have he' : (qSequence (movingCorrection N) (M + i + 1) -
      response N (logarithmicCutoff M) (M + i + 1)) ^ 2 ≤ zetaTwo * (2 * L) ^ 2 := by
    simpa only [Nat.add_assoc] using
      he.trans (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left htail (mul_nonneg hz.le (sq_nonneg (2 * L))))
  have hroot := Real.sq_sqrt hz.le
  have hroot0 := Real.sqrt_nonneg zetaTwo
  have hprod : 0 ≤ 2 * Real.sqrt zetaTwo * L := by positivity
  have hprodSq : (2 * Real.sqrt zetaTwo * L) ^ 2 = zetaTwo * (2 * L) ^ 2 := by
    rw [mul_pow, mul_pow, hroot]
    ring
  change |qSequence (movingCorrection N) (M + i + 1) -
    response N (logarithmicCutoff M) (M + i + 1)| ≤ 2 * Real.sqrt zetaTwo * L
  nlinarith [sq_abs (qSequence (movingCorrection N) (M + i + 1) -
    response N (logarithmicCutoff M) (M + i + 1)),
    abs_nonneg (qSequence (movingCorrection N) (M + i + 1) -
      response N (logarithmicCutoff M) (M + i + 1))]

/-- Finite source mean squares control the corresponding full-response block.
The exact lost square is recorded by block_energy_exact. -/
theorem full_block_meanSquare_le (N M m : ℕ) (hM : 0 < M)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : (∑ i ∈ Finset.range M,
      response N (logarithmicCutoff M) (M + i + 1) ^ 2) ≤
        C * (M : ℝ) * (6 + Real.log (M : ℝ)) ^ (2 * m)) :
    (∑ i ∈ Finset.range M, qSequence (movingCorrection N) (M + i + 1) ^ 2) ≤
      (2 * C + 8 * zetaTwo) * (M : ℝ) * (6 + Real.log (M : ℝ)) ^ (2 * max m 1) := by
  let L : ℝ := 6 + Real.log (M : ℝ)
  have hz := zetaTwo_pos
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hM1]
  have hterm (i : ℕ) (hi : i ∈ Finset.range M) :
      qSequence (movingCorrection N) (M + i + 1) ^ 2 ≤
        2 * response N (logarithmicCutoff M) (M + i + 1) ^ 2 + 8 * zetaTwo * L ^ 2 := by
    have he := block_remainder_abs_le N M i hM (Finset.mem_range.mp hi)
    have hs := mul_self_le_mul_self
      (abs_nonneg (qSequence (movingCorrection N) (M + i + 1) -
        response N (logarithmicCutoff M) (M + i + 1))) he
    have hr := Real.sq_sqrt hz.le
    have heq : (2 * Real.sqrt zetaTwo * L) ^ 2 = 4 * zetaTwo * L ^ 2 := by
      rw [mul_pow, mul_pow, hr]
      ring
    have hrem : (qSequence (movingCorrection N) (M + i + 1) -
        response N (logarithmicCutoff M) (M + i + 1)) ^ 2 ≤ 4 * zetaTwo * L ^ 2 := by
      nlinarith [sq_abs (qSequence (movingCorrection N) (M + i + 1) -
        response N (logarithmicCutoff M) (M + i + 1))]
    nlinarith [sq_nonneg (qSequence (movingCorrection N) (M + i + 1) -
      2 * response N (logarithmicCutoff M) (M + i + 1))]
  have hpowM : L ^ (2 * m) ≤ L ^ (2 * max m 1) :=
    pow_le_pow_right₀ hL (Nat.mul_le_mul_left 2 (Nat.le_max_left _ _))
  have hpow2 : L ^ 2 ≤ L ^ (2 * max m 1) := by
    apply pow_le_pow_right₀ hL
    have h := Nat.le_max_right m 1
    omega
  calc
    _ ≤ ∑ i ∈ Finset.range M,
        (2 * response N (logarithmicCutoff M) (M + i + 1) ^ 2 + 8 * zetaTwo * L ^ 2) :=
      Finset.sum_le_sum hterm
    _ = 2 * (∑ i ∈ Finset.range M,
        response N (logarithmicCutoff M) (M + i + 1) ^ 2) + (M : ℝ) * (8 * zetaTwo * L ^ 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ 2 * (C * (M : ℝ) * L ^ (2 * m)) + (M : ℝ) * (8 * zetaTwo * L ^ 2) := by
      have h := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2)
      exact add_le_add h le_rfl
    _ = (2 * C * (M : ℝ)) * L ^ (2 * m) + (8 * zetaTwo * (M : ℝ)) * L ^ 2 := by ring
    _ ≤ (2 * C * (M : ℝ)) * L ^ (2 * max m 1) + (8 * zetaTwo * (M : ℝ)) * L ^ (2 * max m 1) :=
      add_le_add (mul_le_mul_of_nonneg_left hpowM (by positivity))
        (mul_le_mul_of_nonneg_left hpow2 (by positivity))
    _ = _ := by dsimp [L]; ring

/-- Conditional research reduction, using a single cutoff for each dyadic
block and allowing a different unbounded stage set for each block. -/
theorem riemannHypothesis_of_frequently_dyadic_shortHead_meanSquare
    (m : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ j : ℕ, ∃ᶠ N : ℕ in atTop,
      (∑ i ∈ Finset.range (2 ^ j),
        response N (logarithmicCutoff (2 ^ j)) (2 ^ j + i + 1) ^ 2) ≤
          C * ((2 ^ j : ℕ) : ℝ) * (6 + Real.log ((2 ^ j : ℕ) : ℝ)) ^ (2 * m)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_frequently_dyadic_moving_meanSquare (max m 1)
    (2 * C + 8 * zetaTwo) (by have hz := zetaTwo_pos; positivity)
  intro j
  exact (hb j).mono (fun N hN =>
    full_block_meanSquare_le N (2 ^ j) m (pow_pos (by norm_num) j) C hC hN)

end RiemannResearch.RH.QSquarefreeShortHeadBlocks
