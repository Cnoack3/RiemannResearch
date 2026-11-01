/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeShortHeadResponse
import RiemannResearch.RH.QSquarefreePrefixDispersion
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.RH.QShiftedReciprocalBounds
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Complete-Q head leakage and compensated prefix blocks

Source: user-requested investigation of SquarefreePrefixAbelDispersion20261031.md,
1 November 2026. The off-head output of the actual canonical stage is retained
exactly. The block estimate sums over physical sites before taking energy bounds.
All composite squarefree conductors and the complete Q inner product are inherited
from the canonical stage. The required arithmetic leakage rate remains Open.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeHeadLeakage
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage
open QFiniteSupportDualCriterion QSquarefreeShortHeadResponse QShiftedReciprocal
open RiemannResearch.Analysis.DenseProjectionTesting
open QSquarefreePrefixAbel

def projectedHead (N H : ℕ) (z : QHilbert) : QHilbert :=
  (stage N).starProjection (finiteHead H z)

def leakage (N H : ℕ) (z : QHilbert) : QHilbert :=
  projectedHead N H z - finiteHead H (projectedHead N H z)

theorem leakage_energy_exact (N H : ℕ) (z : QHilbert) :
    ‖leakage N H z‖ ^ 2 =
      ‖projectedHead N H z‖ ^ 2 -
        ‖finiteHead H (projectedHead N H z)‖ ^ 2 := by
  have h := finiteHead_norm_sq_split H (projectedHead N H z)
  unfold leakage
  linarith

theorem leakage_quarter_exact (N H : ℕ) (z : QHilbert) :
    ‖leakage N H z‖ ^ 2 +
      ‖finiteHead H (projectedHead N H z) - (1 / 2 : ℝ) • finiteHead H z‖ ^ 2 =
        ‖finiteHead H z‖ ^ 2 / 4 := by
  have hi : inner ℝ (finiteHead H (projectedHead N H z)) (finiteHead H z) =
      ‖projectedHead N H z‖ ^ 2 := by
    rw [finiteHead_inner, finiteHead_idem]
    have hp := inner_eq_projected_test (stage N)
      ((stage N).starProjection_apply_mem (finiteHead H z)) (finiteHead H z)
    change inner ℝ (projectedHead N H z) (finiteHead H z) =
      ‖projectedHead N H z‖ ^ 2
    change inner ℝ ((stage N).starProjection (finiteHead H z)) (finiteHead H z) =
      ‖(stage N).starProjection (finiteHead H z)‖ ^ 2
    rw [hp, real_inner_self_eq_norm_sq]
  rw [leakage_energy_exact, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, real_inner_smul_right, hi]
  norm_num
  ring

theorem leakage_sq_le_quarter (N H : ℕ) (z : QHilbert) :
    ‖leakage N H z‖ ^ 2 ≤ ‖finiteHead H z‖ ^ 2 / 4 := by
  have h := leakage_quarter_exact N H z
  nlinarith [sq_nonneg
    ‖finiteHead H (projectedHead N H z) - (1 / 2 : ℝ) • finiteHead H z‖]

theorem source_split (N H n : ℕ) :
    source N H n = finiteHead H (B (residual N)) -
      (1 / ((n : ℝ) + 1)) • finiteHead H (residual N) := by
  apply lp.ext
  funext i
  by_cases hi : i < H
  · change finiteHead H (B (residual N) - (1 / ((n : ℝ) + 1)) • residual N) i =
      finiteHead H (B (residual N)) i -
        (1 / ((n : ℝ) + 1)) * finiteHead H (residual N) i
    rw [finiteHead_apply_of_lt H _ i hi, finiteHead_apply_of_lt H _ i hi,
      finiteHead_apply_of_lt H _ i hi]
    rfl
  · change finiteHead H (B (residual N) - (1 / ((n : ℝ) + 1)) • residual N) i =
      finiteHead H (B (residual N)) i -
        (1 / ((n : ℝ) + 1)) * finiteHead H (residual N) i
    rw [finiteHead_apply_eq_zero H _ i (by omega),
      finiteHead_apply_eq_zero H _ i (by omega),
      finiteHead_apply_eq_zero H _ i (by omega)]
    simp

theorem response_eq_leakage (N H k : ℕ) (hk : H ≤ k) :
    response N H (k + 1) =
      qSequence (leakage N H (B (residual N))) (k + 1) -
        (1 / ((k : ℝ) + 2)) * qSequence (leakage N H (residual N)) (k + 1) := by
  rw [response_eq_projected_source, source_split, map_sub, map_smul]
  simp only [qSequence_succ, leakage]
  change (projectedHead N H (B (residual N)) k -
    (1 / (((k + 1 : ℕ) : ℝ) + 1)) * projectedHead N H (residual N) k) /
      Real.sqrt (qWeight k) =
    (projectedHead N H (B (residual N)) k -
      finiteHead H (projectedHead N H (B (residual N))) k) / Real.sqrt (qWeight k) -
    (1 / ((k : ℝ) + 2)) *
      ((projectedHead N H (residual N) k -
        finiteHead H (projectedHead N H (residual N)) k) / Real.sqrt (qWeight k))
  rw [finiteHead_apply_eq_zero H _ k hk, finiteHead_apply_eq_zero H _ k hk]
  norm_num only [Nat.cast_add, Nat.cast_one]
  dsimp only [projectedHead]
  ring

theorem coordinate_block_sq_le (f : QHilbert) (M : ℕ) :
    (∑ i ∈ Finset.range M, (f (M + i)) ^ 2) ≤ ‖f‖ ^ 2 := by
  have hn : (∑ i ∈ Finset.range (M + M), (f i) ^ 2) =
      ‖finiteHead (M + M) f‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_finiteHead_eq_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [finiteHead_apply_of_lt (M + M) f i (Finset.mem_range.mp hi)]
    ring
  have hs := finiteHead_norm_sq_split (M + M) f
  rw [← hn, Finset.sum_range_add] at hs
  have hnon : 0 ≤ ∑ i ∈ Finset.range M, (f i) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg (f i))
  nlinarith [sq_nonneg ‖f - finiteHead (M + M) f‖]

theorem qSequence_sq_scale (f : QHilbert) (k : ℕ) :
    qSequence f (k + 1) ^ 2 =
      zetaTwo * ((k : ℝ) + 1) ^ 2 * (f k) ^ 2 := by
  rw [qSequence_succ, div_pow, Real.sq_sqrt (qWeight_pos k).le]
  unfold qWeight positiveQWeight
  push_cast
  field_simp

theorem physical_block_sq_le (f : QHilbert) (M : ℕ) :
    (∑ i ∈ Finset.range M, qSequence f (M + i + 1) ^ 2) ≤
      4 * zetaTwo * (M : ℝ) ^ 2 * ‖f‖ ^ 2 := by
  have hZ := zetaTwo_pos
  calc
    _ ≤ ∑ i ∈ Finset.range M,
        (4 * zetaTwo * (M : ℝ) ^ 2) * (f (M + i)) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      rw [qSequence_sq_scale]
      have hidx : ((M + i : ℕ) : ℝ) + 1 ≤ 2 * (M : ℝ) := by
        exact_mod_cast (show M + i + 1 ≤ 2 * M by
          have := Finset.mem_range.mp hi
          omega)
      have hidx0 : 0 ≤ ((M + i : ℕ) : ℝ) + 1 := by positivity
      have hsq : (((M + i : ℕ) : ℝ) + 1) ^ 2 ≤ 4 * (M : ℝ) ^ 2 := by
        nlinarith
      have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsq zetaTwo_pos.le) (sq_nonneg (f (M+i)))
      nlinarith only [h]
    _ = (4 * zetaTwo * (M : ℝ) ^ 2) *
        ∑ i ∈ Finset.range M, (f (M + i)) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (coordinate_block_sq_le f M) (by positivity)

theorem affine_block_sq_le (x y : QHilbert) (M : ℕ) :
    (∑ i ∈ Finset.range M,
      (qSequence x (M + i + 1) -
        (1 / (((M + i : ℕ) : ℝ) + 2)) * qSequence y (M + i + 1)) ^ 2) ≤
      8 * zetaTwo * (M : ℝ) ^ 2 *
        (‖x‖ ^ 2 + ‖y‖ ^ 2 / ((M : ℝ) + 2) ^ 2) := by
  have hZ := zetaTwo_pos
  have hb (i : ℕ) :
      (1 / (((M + i : ℕ) : ℝ) + 2)) ^ 2 ≤ 1 / ((M : ℝ) + 2) ^ 2 := by
    have h : 1 / (((M + i : ℕ) : ℝ) + 2) ≤ 1 / ((M : ℝ) + 2) := by
      apply one_div_le_one_div_of_le (by positivity)
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) i]
    have h0 : 0 ≤ 1 / (((M + i : ℕ) : ℝ) + 2) := by positivity
    simpa only [← pow_two, one_div_pow] using mul_self_le_mul_self h0 h
  calc
    _ ≤ ∑ i ∈ Finset.range M,
        (2 * qSequence x (M + i + 1) ^ 2 +
          (2 / ((M : ℝ) + 2) ^ 2) * qSequence y (M + i + 1) ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      have h := mul_le_mul_of_nonneg_right (hb i)
        (sq_nonneg (qSequence y (M + i + 1)))
      calc
        _ ≤ 2 * qSequence x (M + i + 1) ^ 2 +
            2 * ((1 / (((M + i : ℕ) : ℝ) + 2)) ^ 2 *
              qSequence y (M + i + 1) ^ 2) := by
          nlinarith [sq_nonneg (qSequence x (M + i + 1) +
            (1 / (((M + i : ℕ) : ℝ) + 2)) * qSequence y (M + i + 1))]
        _ ≤ _ := by
          have h' := add_le_add_left (mul_le_mul_of_nonneg_left h
            (by norm_num : (0 : ℝ) ≤ 2)) (2 * qSequence x (M + i + 1) ^ 2)
          ring_nf at h' ⊢
          exact h'
    _ = 2 * (∑ i ∈ Finset.range M, qSequence x (M + i + 1) ^ 2) +
        (2 / ((M : ℝ) + 2) ^ 2) *
          (∑ i ∈ Finset.range M, qSequence y (M + i + 1) ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 2 * (4 * zetaTwo * (M : ℝ) ^ 2 * ‖x‖ ^ 2) +
        (2 / ((M : ℝ) + 2) ^ 2) * (4 * zetaTwo * (M : ℝ) ^ 2 * ‖y‖ ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left (physical_block_sq_le x M) (by norm_num))
        (mul_le_mul_of_nonneg_left (physical_block_sq_le y M) (by positivity))
    _ = _ := by ring

theorem compensated_block_le_leakage (N H M : ℕ) (hHM : H ≤ M) :
    (∑ i ∈ Finset.range M,
      (abelMass H (M + i + 1) * abelEnergy N H (M + i + 1) -
        abelDispersion N H (M + i + 1))) ≤
      8 * zetaTwo * (M : ℝ) ^ 2 *
        (‖leakage N H (B (residual N))‖ ^ 2 +
          ‖leakage N H (residual N)‖ ^ 2 / ((M : ℝ) + 2) ^ 2) := by
  have he (i : ℕ) :
      abelMass H (M + i + 1) * abelEnergy N H (M + i + 1) -
        abelDispersion N H (M + i + 1) =
      (qSequence (leakage N H (B (residual N))) (M+i+1) -
        (1 / (((M+i : ℕ) : ℝ) + 2)) *
          qSequence (leakage N H (residual N)) (M+i+1)) ^ 2 := by
    have h := response_energy_dispersion_exact N H (M+i+1)
    rw [response_eq_leakage N H (M+i) (by omega)] at h
    linarith
  calc
    _ = ∑ i ∈ Finset.range M,
        (qSequence (leakage N H (B (residual N))) (M+i+1) -
          (1 / (((M+i : ℕ) : ℝ) + 2)) *
            qSequence (leakage N H (residual N)) (M+i+1)) ^ 2 :=
      Finset.sum_congr rfl (fun i _ => he i)
    _ ≤ _ := affine_block_sq_le _ _ M

/-- Unconditional quadratic block bound; no residual decay rate is assumed. -/
theorem compensated_block_le_quadratic (N H M : ℕ) (hHM : H ≤ M) :
    (∑ i ∈ Finset.range M,
      (abelMass H (M + i + 1) * abelEnergy N H (M + i + 1) -
        abelDispersion N H (M + i + 1))) ≤
      8 * zetaTwo * (M : ℝ) ^ 2 *
        (error N / 16 + (error N / 4) / ((M : ℝ) + 2) ^ 2) := by
  have hB : ‖leakage N H (B (residual N))‖ ^ 2 ≤ error N / 16 := by
    have hq := leakage_sq_le_quarter N H (B (residual N))
    have hh := finiteHead_norm_le H (B (residual N))
    have hb := B_norm_le_half (residual N)
    change ‖leakage N H (B (residual N))‖ ^ 2 ≤ ‖residual N‖ ^ 2 / 16
    nlinarith [norm_nonneg (finiteHead H (B (residual N))),
      norm_nonneg (B (residual N)), norm_nonneg (residual N)]
  have hR : ‖leakage N H (residual N)‖ ^ 2 ≤ error N / 4 := by
    have hq := leakage_sq_le_quarter N H (residual N)
    have hh := finiteHead_norm_le H (residual N)
    change ‖leakage N H (residual N)‖ ^ 2 ≤ ‖residual N‖ ^ 2 / 4
    nlinarith [norm_nonneg (finiteHead H (residual N)), norm_nonneg (residual N)]
  have hZ := zetaTwo_pos
  exact (compensated_block_le_leakage N H M hHM).trans
    (mul_le_mul_of_nonneg_left
      (add_le_add hB (div_le_div_of_nonneg_right hR (by positivity))) (by positivity))

end RiemannResearch.RH.QSquarefreeHeadLeakage
