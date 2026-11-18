/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Scalar exponents for the Ingham moment endpoints

These are scalar identities and inequalities, not Gabriel's analytic theorem.
They describe the consequence of combining an L^(4/3) left moment with height
power one and logarithmic power two, and an L^2 right moment with height power
zero and logarithmic power three. The latter endpoint is now supplied by
ActualInghamRightMoment when the cutoff and outer height are comparable.

Source for the interpolation weights and reciprocal exponents:
Chourasiya--Simonic, arXiv:2507.15184v2, equations (20)--(21), Corollary 6.
https://arxiv.org/html/2507.15184v2
The exponents here are for the weaker, unconditionally proved right endpoint;
no interpolated moment or zero-density provider is asserted.
-/

namespace RiemannResearch.Analysis.InghamInterpolation
open Set

/-- Exact Gabriel weight algebra for the proved two-log and three-log endpoints. -/
theorem gabriel_exponents_exact {β σ : ℝ} (hβ : 1 < β)
    (hσ : σ ∈ Icc (1 / 2 : ℝ) 1) :
    let wL := (β - σ) / (β - 1 / 2)
    let wR := (σ - 1 / 2) / (β - 1 / 2)
    let c := (3 / 4 : ℝ) * wL + (1 / 2 : ℝ) * wR
    wL + wR = 1 ∧
    c = (3 * β - σ - 1) / (4 * (β - 1 / 2)) ∧
    ((3 / 4 : ℝ) * wL) / c = 3 * (β - σ) / (3 * β - σ - 1) ∧
    ((3 / 2 : ℝ) * wL + (3 / 2 : ℝ) * wR) / c =
      6 * (β - 1 / 2) / (3 * β - σ - 1) := by
  have hd : β - 1 / 2 ≠ 0 := by linarith
  have hd2 : β * 2 - 1 ≠ 0 := by linarith
  have he : 3 * β - σ - 1 ≠ 0 := by linarith [hσ.2]
  dsimp only
  have hc : (3 / 4 : ℝ) * ((β - σ) / (β - 1 / 2)) +
      (1 / 2 : ℝ) * ((σ - 1 / 2) / (β - 1 / 2)) =
      (3 * β - σ - 1) / (4 * (β - 1 / 2)) := by field_simp; ring
  have hw : (β - σ) / (β - 1 / 2) + (σ - 1 / 2) / (β - 1 / 2) = 1 := by
    rw [← add_div]
    apply (div_eq_one_iff_eq hd).mpr
    ring
  refine ⟨hw, hc, ?_, ?_⟩
  · rw [hc]
    field_simp [hd, hd2, he]
    <;> ring
  · rw [← mul_add, hw, hc, div_div_eq_mul_div]
    ring

/-- Exact excess in the height exponent from placing the right line at 1+eta. -/
theorem moving_height_exponent_correction {η σ : ℝ} (hη : 0 ≤ η)
    (hσ : σ ∈ Icc (1 / 2 : ℝ) 1) :
    3 * (1 + η - σ) / (2 + 3 * η - σ) - 3 * (1 - σ) / (2 - σ) =
      3 * η * (2 * σ - 1) / ((2 + 3 * η - σ) * (2 - σ)) := by
  have hd : 2 + 3 * η - σ ≠ 0 := by linarith [hσ.2]
  have he : 2 - σ ≠ 0 := by linarith [hσ.2]
  field_simp
  ring

theorem moving_height_exponent_le {η σ : ℝ} (hη : 0 ≤ η)
    (hσ : σ ∈ Icc (1 / 2 : ℝ) 1) :
    3 * (1 + η - σ) / (2 + 3 * η - σ) ≤
      3 * (1 - σ) / (2 - σ) + 3 * η := by
  have hd : 1 ≤ 2 + 3 * η - σ := by linarith [hσ.2]
  have he : 1 ≤ 2 - σ := by linarith [hσ.2]
  have hp : 1 ≤ (2 + 3 * η - σ) * (2 - σ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr he)]
  have hh : 3 * η * (2 * σ - 1) / ((2 + 3 * η - σ) * (2 - σ)) ≤ 3 * η := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hnum : 3 * η * (2 * σ - 1) ≤ 3 * η := by nlinarith [hσ.2]
    exact hnum.trans (by nlinarith)
  linarith [moving_height_exponent_correction hη hσ]

/-- The moving right line does not worsen the limiting logarithmic exponent. -/
theorem moving_log_exponent_le {η σ : ℝ} (hη : 0 ≤ η)
    (hσ : σ ∈ Icc (1 / 2 : ℝ) 1) :
    3 * (1 + 2 * η) / (2 + 3 * η - σ) ≤ 3 / (2 - σ) := by
  have hd : 0 < 2 + 3 * η - σ := by linarith [hσ.2]
  have he : 0 < 2 - σ := by linarith [hσ.2]
  apply (div_le_div_iff₀ hd he).mpr
  nlinarith [mul_nonneg hη (show 0 ≤ σ - 1 / 2 by linarith [hσ.1])]

/-- One additional logarithm from the counting-line gap still gives at most four.
This sharper logarithmic exponent still requires analytic interpolation on this route. -/
theorem limiting_density_log_exponent_le_four {σ : ℝ}
    (hσ : σ ∈ Icc (1 / 2 : ℝ) 1) :
    1 + 3 / (2 - σ) ≤ 4 := by
  have hd : 0 < 2 - σ := by linarith [hσ.2]
  have hh : 3 / (2 - σ) ≤ 3 := (div_le_iff₀ hd).mpr (by linarith [hσ.2])
  linarith

end RiemannResearch.Analysis.InghamInterpolation
