import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Arithmetic bridges for exact weighted dual lower certificates

The signed dual expression is retained through exact common-denominator
identities; only the final integer cross-multiplication certificate is assumed.
-/

namespace RiemannResearch.Analysis

theorem lower_certificate_of_cross_mul
    (A B N C D H : ℝ) (hA : 0 < A) (hB : 0 < B) (hD : 0 < D) (hH : 0 < H)
    (h : C * D ^ 2 * A ≤ H * (2 * N * D * A - N ^ 2 * B)) :
    C / H ≤ 2 * (N / D) - (N / D) ^ 2 / (A / B) := by
  have he : 2 * (N / D) - (N / D) ^ 2 / (A / B) =
      (2 * N * D * A - N ^ 2 * B) / (D ^ 2 * A) := by
    field_simp [ne_of_gt hA, ne_of_gt hB, ne_of_gt hD] <;> ring
  rw [he]
  apply (div_le_div_iff₀ hH (mul_pos (pow_pos hD 2) hA)).2
  nlinarith only [h]

theorem residue_lower_common_denominator
    (r M : ℝ) (hr : 0 < r) (hM : 0 < M) :
    1 / (r * (r + 1)) + 1 / ((r + M) * (r + M + 1)) =
      (r * (r + 1) + (r + M) * (r + M + 1)) /
        (r * (r + 1) * ((r + M) * (r + M + 1))) := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hr1 : r + 1 ≠ 0 := ne_of_gt (by linarith)
  have hrM : r + M ≠ 0 := ne_of_gt (add_pos hr hM)
  have hrM1 : r + M + 1 ≠ 0 := ne_of_gt (by linarith)
  field_simp [hr0, hr1, hrM, hrM1] <;> ring

end RiemannResearch.Analysis
