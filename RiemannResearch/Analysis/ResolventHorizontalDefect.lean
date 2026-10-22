/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact horizontal defect of a reflected resolvent pair

Source: continuation of the user-provided Ordinate_Harmonic_Theory_20261010
argument. The rational identity is independently derived here. Suzuki,
Aspects of the screw function corresponding to the Riemann zeta-function,
https://arxiv.org/html/2206.03682v4, Section 2.1, supplies the neighboring
xi logarithmic-derivative context, not a provider for the identity below.
The variable y is the squared ordinate. No RH assumption occurs.
-/

noncomputable section
namespace RiemannResearch.Analysis.ResolventHorizontalDefect

def denominator (x d y : ℝ) : ℝ :=
  (x ^ 2 + y) * ((x - d) ^ 2 + y) * ((x + d) ^ 2 + y)

def gap (x d y : ℝ) : ℝ :=
  2 * x / (x ^ 2 + y) -
    ((x - d) / ((x - d) ^ 2 + y) + (x + d) / ((x + d) ^ 2 + y))

def weight (x d y : ℝ) : ℝ :=
  2 * x * (3 * y + d ^ 2 - x ^ 2) / denominator x d y

theorem denominator_pos (x d : ℝ) {y : ℝ} (hy : 0 < y) :
    0 < denominator x d y := by
  unfold denominator
  positivity

/-- Exact reflected-pair identity; every denominator and square is retained. -/
theorem gap_eq_square_mul_weight (x d : ℝ) {y : ℝ} (hy : 0 < y) :
    gap x d y = d ^ 2 * weight x d y := by
  have h0 : x ^ 2 + y ≠ 0 := ne_of_gt (by positivity)
  have hm : (x - d) ^ 2 + y ≠ 0 := ne_of_gt (by positivity)
  have hp : (x + d) ^ 2 + y ≠ 0 := ne_of_gt (by positivity)
  unfold gap weight denominator
  field_simp
  ring

theorem weight_pos {x d y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hheight : x ^ 2 < 3 * y) : 0 < weight x d y := by
  apply div_pos _ (denominator_pos x d hy)
  have hn : 0 < 3 * y + d ^ 2 - x ^ 2 := by nlinarith [sq_nonneg d]
  exact mul_pos (by positivity) hn

theorem gap_nonneg {x d y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hheight : x ^ 2 < 3 * y) : 0 ≤ gap x d y := by
  rw [gap_eq_square_mul_weight x d hy]
  exact mul_nonneg (sq_nonneg d) (weight_pos hx hy hheight).le

theorem gap_eq_zero_iff {x d y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hheight : x ^ 2 < 3 * y) : gap x d y = 0 ↔ d = 0 := by
  rw [gap_eq_square_mul_weight x d hy, mul_eq_zero]
  simp [(weight_pos hx hy hheight).ne']

/-- At the sigma=2 probe, the exact defect has a summable fourth-order scale. -/
theorem gap_two_bounds {d y : ℝ} (hd : |d| ≤ 1 / 2) (hy : 1 ≤ y) :
    (1 / 5 : ℝ) * (d ^ 2 / (1 + y) ^ 2) ≤ gap (3 / 2) d y ∧
      gap (3 / 2) d y ≤ 9 * (d ^ 2 / (1 + y) ^ 2) := by
  have hy0 : 0 < y := by linarith
  have hb := abs_le.mp hd
  have hq : d ^ 2 ≤ 1 / 4 := by nlinarith [hb.1, hb.2]
  have hbase : 0 < (1 + y) ^ 2 := by positivity
  have hA : 0 < (3 / 2 : ℝ) ^ 2 + y := by positivity
  have hm : 1 + y ≤ ((3 / 2 : ℝ) - d) ^ 2 + y := by nlinarith [hb.2]
  have hp : 1 + y ≤ ((3 / 2 : ℝ) + d) ^ 2 + y := by nlinarith [hb.1]
  let D := (((3 / 2 : ℝ) - d) ^ 2 + y) * (((3 / 2 : ℝ) + d) ^ 2 + y)
  have hDlo : (1 + y) ^ 2 ≤ D := by
    dsimp [D]
    nlinarith [mul_le_mul hm hp (by positivity) (by positivity)]
  have hDidentity : D = (y + 9 / 4 + d ^ 2) ^ 2 - 9 * d ^ 2 := by
    dsimp [D]; ring
  have hDhi : D ≤ (y + 5 / 2) ^ 2 := by
    rw [hDidentity]
    have hs : (y + 9 / 4 + d ^ 2) ^ 2 ≤ (y + 5 / 2) ^ 2 := by
      nlinarith [sq_nonneg d]
    nlinarith [sq_nonneg d]
  have hscale : (y + 5 / 2) ^ 2 ≤ (49 / 16 : ℝ) * (1 + y) ^ 2 := by
    nlinarith [sq_nonneg (y - 1)]
  have hAhi : (3 / 2 : ℝ) ^ 2 + y ≤ (13 / 8 : ℝ) * (1 + y) := by
    nlinarith
  have hNlo : (9 / 8 : ℝ) * (1 + y) ≤ 3 * (3 * y + d ^ 2 - 9 / 4) := by
    nlinarith [sq_nonneg d]
  have hNhi : 3 * (3 * y + d ^ 2 - 9 / 4) ≤ 9 * ((3 / 2 : ℝ) ^ 2 + y) := by
    nlinarith
  have hDpos : 0 < D := lt_of_lt_of_le hbase hDlo
  have hden : denominator (3 / 2) d y = ((3 / 2 : ℝ) ^ 2 + y) * D := by
    unfold denominator; dsimp [D]; ring
  have hlo : (1 / 5 : ℝ) / (1 + y) ^ 2 ≤ weight (3 / 2) d y := by
    rw [weight, hden]
    apply (div_le_div_iff₀ hbase (mul_pos hA hDpos)).mpr
    have hDu : D ≤ (49 / 16 : ℝ) * (1 + y) ^ 2 := hDhi.trans hscale
    have hu := mul_le_mul hAhi hDu hDpos.le (by positivity)
    have hn := mul_le_mul_of_nonneg_right hNlo hbase.le
    nlinarith
  have hhi : weight (3 / 2) d y ≤ 9 / (1 + y) ^ 2 := by
    rw [weight, hden]
    apply (div_le_div_iff₀ (mul_pos hA hDpos) hbase).mpr
    have hl := mul_le_mul_of_nonneg_left hDlo hA.le
    have hn := mul_le_mul_of_nonneg_right hNhi hbase.le
    nlinarith
  rw [gap_eq_square_mul_weight (3 / 2) d hy0]
  constructor
  · have h := mul_le_mul_of_nonneg_left hlo (sq_nonneg d)
    calc
      _ = d ^ 2 * ((1 / 5 : ℝ) / (1 + y) ^ 2) := by ring
      _ ≤ _ := h
  · have h := mul_le_mul_of_nonneg_left hhi (sq_nonneg d)
    calc
      _ ≤ d ^ 2 * (9 / (1 + y) ^ 2) := h
      _ = _ := by ring

end RiemannResearch.Analysis.ResolventHorizontalDefect
