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
# A determinant comparison retaining the horizontal displacement

Source: independently derived continuation of the user's Gaussian harmonic
analysis report. This finite algebra does not assume RH or a lower zero
height. The infinite xi Hadamard-product assembly is not asserted here.
-/

noncomputable section
namespace RiemannResearch.Analysis.DeterminantHorizontalDefect

def ordinateFactor (x y : ℝ) : ℝ := ((x ^ 2 + y) / y) ^ 2
def fullFactor (x d y : ℝ) : ℝ :=
  (((x - d) ^ 2 + y) * ((x + d) ^ 2 + y)) / (y + d ^ 2) ^ 2
def defectNumerator (x d y : ℝ) : ℝ :=
  x ^ 2 * d ^ 2 * (2 * y * (3 * y + x ^ 2) + d ^ 2 * (2 * y + x ^ 2))

/-- All terms are retained before any sign estimate. -/
theorem cross_multiplied_defect (x d y : ℝ) :
    (x ^ 2 + y) ^ 2 * (y + d ^ 2) ^ 2 -
      y ^ 2 * (((x - d) ^ 2 + y) * ((x + d) ^ 2 + y)) =
        defectNumerator x d y := by
  unfold defectNumerator
  ring

theorem exact_factor_defect (x d : ℝ) {y : ℝ} (hy : 0 < y) :
    ordinateFactor x y - fullFactor x d y =
      defectNumerator x d y / (y ^ 2 * (y + d ^ 2) ^ 2) := by
  have hy' : y ≠ 0 := hy.ne'
  have hd : y + d ^ 2 ≠ 0 := ne_of_gt (by positivity)
  unfold ordinateFactor fullFactor
  rw [div_pow]
  field_simp
  unfold defectNumerator
  ring

theorem defectNumerator_nonneg (x d : ℝ) {y : ℝ} (hy : 0 < y) :
    0 ≤ defectNumerator x d y := by
  unfold defectNumerator
  positivity

theorem factor_le (x d : ℝ) {y : ℝ} (hy : 0 < y) :
    fullFactor x d y ≤ ordinateFactor x y := by
  have h := div_nonneg (defectNumerator_nonneg x d hy)
    (show 0 ≤ y ^ 2 * (y + d ^ 2) ^ 2 by positivity)
  rw [← exact_factor_defect x d hy] at h
  linarith

theorem factor_eq_iff {x d y : ℝ} (hx : x ≠ 0) (hy : 0 < y) :
    fullFactor x d y = ordinateFactor x y ↔ d = 0 := by
  have hn : 0 < 2 * y * (3 * y + x ^ 2) + d ^ 2 * (2 * y + x ^ 2) := by
    positivity
  have hd : y ^ 2 * (y + d ^ 2) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have he := exact_factor_defect x d hy
  constructor
  · intro h
    rw [← h, sub_self] at he
    have hz : defectNumerator x d y = 0 := by
      have hzero := congrArg (fun r : ℝ => r * (y ^ 2 * (y + d ^ 2) ^ 2)) he.symm
      simpa [hd] using hzero
    unfold defectNumerator at hz
    rcases mul_eq_zero.mp hz with hq | hq
    · rcases mul_eq_zero.mp hq with hxx | hdd
      · exact False.elim (hx ((sq_eq_zero_iff).mp hxx))
      · exact (sq_eq_zero_iff).mp hdd
    · exact False.elim (hn.ne' hq)
  · intro h
    subst d
    unfold fullFactor ordinateFactor
    ring

theorem fullFactor_pos (x d : ℝ) {y : ℝ} (hy : 0 < y) :
    0 < fullFactor x d y := by
  unfold fullFactor
  positivity

/-- The exact remainder governing the maximum of the determinant ratio. -/
theorem maximum_ratio_square (x d y : ℝ) :
    (4 * y + d ^ 2) * (((x - d) ^ 2 + y) * ((x + d) ^ 2 + y)) -
      4 * y * (x ^ 2 + y) ^ 2 = d ^ 2 * (x ^ 2 - 3 * y - d ^ 2) ^ 2 := by
  ring

theorem maximum_ratio_comparison (x d y : ℝ) :
    4 * y * (x ^ 2 + y) ^ 2 ≤
      (4 * y + d ^ 2) * (((x - d) ^ 2 + y) * ((x + d) ^ 2 + y)) := by
  have hs : 0 ≤ d ^ 2 * (x ^ 2 - 3 * y - d ^ 2) ^ 2 := by positivity
  rw [← maximum_ratio_square x d y] at hs
  linarith

end RiemannResearch.Analysis.DeterminantHorizontalDefect
