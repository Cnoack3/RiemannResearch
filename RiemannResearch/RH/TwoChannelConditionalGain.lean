/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Exact two-channel conditional gain

Scalar two-channel Gram algebra for the conditional-gain and common-optimizer
steps described in Sections G.70 and G.77 of the user-provided continuation.
That source motivates the statements and Schur-residualization strategy.

The parameters are arbitrary real scalars. This file does not construct
arithmetic Gram/pairing data, prove legal support or optimizer admissibility,
bound arithmetic signed overlaps, or establish sampling, return-covariance,
G3, or RH.
-/

noncomputable section

namespace RiemannResearch.RH.CombinedGain.TwoChannel

/-- Determinant of the real symmetric two-channel Gram matrix. -/
def det (a b c : ℝ) : ℝ := a * b - c ^ 2

/-- Exact gain in the actual signed correlation direction (s,t). -/
def gain (a b c s t : ℝ) : ℝ :=
  (b * s ^ 2 + a * t ^ 2 - 2 * c * s * t) / det a b c

/-- The concave joint dual objective, evaluated at one common pair (x,y). -/
def score (a b c s t x y : ℝ) : ℝ :=
  2 * (s * x + t * y) - (a * x ^ 2 + 2 * c * x * y + b * y ^ 2)

def optimizerX (a b c s t : ℝ) : ℝ := (b * s - c * t) / det a b c
def optimizerY (a b c s t : ℝ) : ℝ := (a * t - c * s) / det a b c

/-- Exact sequential conditional-gain ledger, without square-root normalization. -/
theorem gain_eq_first_add_conditional {a b c s t : ℝ}
    (ha : a ≠ 0) (hd : det a b c ≠ 0) :
    gain a b c s t =
      s ^ 2 / a + (a * t - c * s) ^ 2 / (a * det a b c) := by
  unfold gain
  field_simp [ha, hd]
  simp only [det]
  ring

/-- The added gain vanishes precisely when the second actual correlation
is predicted by the signed overlap with the first channel. -/
theorem gain_eq_first_iff {a b c s t : ℝ}
    (ha : a ≠ 0) (hd : det a b c ≠ 0) :
    gain a b c s t = s ^ 2 / a ↔ a * t = c * s := by
  rw [gain_eq_first_add_conditional ha hd]
  constructor
  · intro h
    have hq : (a * t - c * s) ^ 2 / (a * det a b c) = 0 := by linarith
    have hs : (a * t - c * s) ^ 2 = 0 :=
      (div_eq_zero_iff.mp hq).resolve_right (mul_ne_zero ha hd)
    nlinarith [sq_nonneg (a * t - c * s)]
  · intro h
    simp [h]

theorem first_le_gain {a b c s t : ℝ}
    (ha : 0 < a) (hd : 0 < det a b c) :
    s ^ 2 / a ≤ gain a b c s t := by
  rw [gain_eq_first_add_conditional (ne_of_gt ha) (ne_of_gt hd)]
  exact le_add_of_nonneg_right (div_nonneg (sq_nonneg _) (mul_pos ha hd).le)

theorem first_lt_gain_iff {a b c s t : ℝ}
    (ha : 0 < a) (hd : 0 < det a b c) :
    s ^ 2 / a < gain a b c s t ↔ a * t ≠ c * s := by
  constructor
  · intro h heq
    have hz := (gain_eq_first_iff (ne_of_gt ha) (ne_of_gt hd)).2 heq
    linarith
  · intro hne
    have hle := first_le_gain (s := s) (t := t) ha hd
    have hneq : s ^ 2 / a ≠ gain a b c s t := by
      intro h
      exact hne ((gain_eq_first_iff (ne_of_gt ha) (ne_of_gt hd)).1 h.symm)
    exact lt_of_le_of_ne hle hneq

/-- Exact completion of squares for the same joint optimizer; no separately
optimized channel scores are added. -/
theorem gain_sub_score_eq_schur_squares {a b c s t : ℝ}
    (ha : a ≠ 0) (hd : det a b c ≠ 0) (x y : ℝ) :
    gain a b c s t - score a b c s t x y =
      a * (x + (c * y - s) / a) ^ 2 +
        (det a b c / a) * (y - optimizerY a b c s t) ^ 2 := by
  unfold gain score optimizerY
  field_simp [ha, hd]
  simp only [det]
  ring

theorem score_le_gain {a b c s t : ℝ}
    (ha : 0 < a) (hd : 0 < det a b c) (x y : ℝ) :
    score a b c s t x y ≤ gain a b c s t := by
  have h := gain_sub_score_eq_schur_squares (s := s) (t := t)
    (ne_of_gt ha) (ne_of_gt hd) x y
  have h1 := mul_nonneg ha.le (sq_nonneg (x + (c * y - s) / a))
  have h2 := mul_nonneg (div_pos hd ha).le
    (sq_nonneg (y - optimizerY a b c s t))
  linarith

/-- The displayed inverse-Gram pair attains the joint gain. -/
theorem score_optimizer_eq_gain {a b c s t : ℝ}
    (hd : det a b c ≠ 0) :
    score a b c s t (optimizerX a b c s t) (optimizerY a b c s t) =
      gain a b c s t := by
  unfold score optimizerX optimizerY gain
  field_simp [hd]
  simp only [det]
  ring

/-- Exact signed Cauchy defect for any trial direction (x,y). -/
theorem gain_mul_gram_sub_pairing_sq {a b c s t : ℝ}
    (hd : det a b c ≠ 0) (x y : ℝ) :
    gain a b c s t * (a * x ^ 2 + 2 * c * x * y + b * y ^ 2) -
        (s * x + t * y) ^ 2 =
      ((a * t - c * s) * x - (b * s - c * t) * y) ^ 2 / det a b c := by
  unfold gain
  field_simp [hd]
  simp only [det]
  ring

/-- Unit-diagonal specialization, retaining the sign of the overlap. -/
theorem normalized_gain_eq_first_add_conditional {ρ s t : ℝ}
    (hρ : 1 - ρ ^ 2 ≠ 0) :
    (s ^ 2 + t ^ 2 - 2 * ρ * s * t) / (1 - ρ ^ 2) =
      s ^ 2 + (t - ρ * s) ^ 2 / (1 - ρ ^ 2) := by
  field_simp [hρ]
  ring

/-- The first normal equation for the one common optimizer. -/
theorem optimizer_normal_first {a b c s t : ℝ}
    (hd : det a b c ≠ 0) :
    a * optimizerX a b c s t + c * optimizerY a b c s t = s := by
  unfold optimizerX optimizerY
  field_simp [hd]
  simp only [det]
  ring

/-- Positive pivots make the joint maximizer unique. -/
theorem score_eq_gain_iff {a b c s t : ℝ}
    (ha : 0 < a) (hd : 0 < det a b c) (x y : ℝ) :
    score a b c s t x y = gain a b c s t ↔
      x = optimizerX a b c s t ∧ y = optimizerY a b c s t := by
  constructor
  · intro heq
    have hgap := gain_sub_score_eq_schur_squares (s := s) (t := t)
      (ne_of_gt ha) (ne_of_gt hd) x y
    have hxNonneg := mul_nonneg ha.le (sq_nonneg (x + (c * y - s) / a))
    have hyNonneg := mul_nonneg (div_pos hd ha).le
      (sq_nonneg (y - optimizerY a b c s t))
    have hxProd : a * (x + (c * y - s) / a) ^ 2 = 0 := by linarith
    have hyProd : (det a b c / a) * (y - optimizerY a b c s t) ^ 2 = 0 := by
      linarith
    have hxSq := (mul_eq_zero.mp hxProd).resolve_left (ne_of_gt ha)
    have hySq := (mul_eq_zero.mp hyProd).resolve_left (ne_of_gt (div_pos hd ha))
    have hy : y = optimizerY a b c s t := by nlinarith only [hySq]
    have hlin : x + (c * y - s) / a = 0 := by nlinarith only [hxSq]
    have hxMul : a * x + c * y = s := by
      field_simp [ne_of_gt ha] at hlin
      linarith only [hlin]
    have hnormal := optimizer_normal_first (s := s) (t := t) (ne_of_gt hd)
    rw [hy] at hxMul
    have hxzero : a * (x - optimizerX a b c s t) = 0 := by
      nlinarith only [hxMul, hnormal]
    have hx : x = optimizerX a b c s t :=
      sub_eq_zero.mp ((mul_eq_zero.mp hxzero).resolve_left (ne_of_gt ha))
    exact ⟨hx, hy⟩
  · rintro ⟨rfl, rfl⟩
    exact score_optimizer_eq_gain (ne_of_gt hd)

/-- The pivot after residualizing channel two against channel one. -/
theorem schur_eq_det_div {a b c : ℝ} (ha : a ≠ 0) :
    b - c ^ 2 / a = det a b c / a := by
  unfold det
  field_simp [ha]

theorem schur_pos {a b c : ℝ}
    (ha : 0 < a) (hd : 0 < det a b c) :
    0 < b - c ^ 2 / a := by
  rw [schur_eq_det_div (ne_of_gt ha)]
  exact div_pos hd ha

/-- Exact residualized form: conditional signal squared over conditional norm. -/
theorem gain_eq_first_add_schur {a b c s t : ℝ}
    (ha : a ≠ 0) (hd : det a b c ≠ 0) :
    gain a b c s t = s ^ 2 / a + (t - c * s / a) ^ 2 / (b - c ^ 2 / a) := by
  rw [schur_eq_det_div ha]
  unfold gain
  field_simp [ha, hd]
  simp only [det]
  ring

/-- A channel with zero raw correlation can still give control-variate gain. -/
theorem gain_zero_second_correlation {a b c s : ℝ}
    (ha : a ≠ 0) (hd : det a b c ≠ 0) :
    gain a b c s 0 = s ^ 2 / a + (c * s) ^ 2 / (a * det a b c) := by
  simpa using (gain_eq_first_add_conditional (s := s) (t := 0) ha hd)

/-- Concrete two-channel Cauchy premise for inverse-free gain certificates. -/
theorem pairing_sq_le_gain_mul_gram {a b c s t : ℝ}
    (hd : 0 < det a b c) (x y : ℝ) :
    (s * x + t * y) ^ 2 ≤
      (a * x ^ 2 + 2 * c * x * y + b * y ^ 2) * gain a b c s t := by
  have h := gain_mul_gram_sub_pairing_sq (s := s) (t := t) (ne_of_gt hd) x y
  have hnonneg := div_nonneg
    (sq_nonneg (((a * t - c * s) * x - (b * s - c * t) * y))) hd.le
  nlinarith only [h, hnonneg]

/-- The actual correlation direction gives an exact signed-overlap certificate,
including the defect lost by replacing exact gain with an inverse-free bound. -/
theorem normalized_actualDirection_defect {ρ s t : ℝ}
    (hρ : 1 - ρ ^ 2 ≠ 0) :
    gain 1 1 ρ s t * (s ^ 2 + t ^ 2 + 2 * ρ * s * t) -
        (s ^ 2 + t ^ 2) ^ 2 =
      ρ ^ 2 * (s ^ 2 - t ^ 2) ^ 2 / (1 - ρ ^ 2) := by
  unfold gain det
  simp only [one_mul]
  field_simp [hρ]
  ring

theorem normalized_det_pos {ρ : ℝ} (hρ : |ρ| < 1) :
    0 < det 1 1 ρ := by
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hρ
  have hp := mul_pos (sub_pos.mpr hhi) (show 0 < 1 + ρ by linarith)
  unfold det
  nlinarith only [hp]

theorem normalized_gain_eq_first_iff {ρ s t : ℝ} (hρ : |ρ| < 1) :
    gain 1 1 ρ s t = s ^ 2 ↔ t = ρ * s := by
  simpa using (gain_eq_first_iff (a := 1) (b := 1) (c := ρ) (s := s) (t := t)
    (by norm_num) (ne_of_gt (normalized_det_pos hρ)))

end RiemannResearch.RH.CombinedGain.TwoChannel
