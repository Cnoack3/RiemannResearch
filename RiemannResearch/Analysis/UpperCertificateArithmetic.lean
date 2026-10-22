import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact arithmetic bridges for periodic upper certificates

The first lemma converts a denominator-cleared polynomial inequality into
the weighted square inequality used by the residue certificates. The second
records the common denominator of the three-term residue-weight upper bound.
-/

namespace RiemannResearch.Analysis

theorem upper_certificate_of_cross_mul
    (A B E C D H : ℝ) (hB : 0 < B) (hD : 0 < D) (hH : 0 < H)
    (h : H * A * E ^ 2 ≤ C * D ^ 2 * B) :
    (A / B) * (E / D) ^ 2 ≤ C / H := by
  rw [div_pow, div_mul_div_comm]
  apply (div_le_div_iff₀ (mul_pos hB (pow_pos hD 2)) hH).2
  nlinarith only [h]

theorem residue_upper_common_denominator
    (r M : ℝ) (hr : 0 < r) (hM : 0 < M) :
    1 / (r * (r + 1)) +
        1 / ((r + M) * (r + M + 1)) +
        1 / (M * (r + M + 1)) =
      (M * (r + M) * (r + M + 1) +
          r * (r + 1) * (r + 2 * M)) /
        (M * r * (r + 1) * (r + M) * (r + M + 1)) := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hM0 : M ≠ 0 := ne_of_gt hM
  have hr1 : r + 1 ≠ 0 := ne_of_gt (by linarith)
  have hrM : r + M ≠ 0 := ne_of_gt (add_pos hr hM)
  have hrM1 : r + M + 1 ≠ 0 := ne_of_gt (by linarith)
  field_simp [hr0, hM0, hr1, hrM, hrM1] <;> ring

end RiemannResearch.Analysis
