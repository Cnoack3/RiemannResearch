/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Signed logarithmic bounds for a quadratic zero detector

The reverse triangle inequality and the elementary real logarithm inequality
retain the signed contribution of 1-e^2. This is the pointwise strategy used
for the right side in Chourasiya--Simonic, arXiv:2507.15184v2, Lemma 7:
https://arxiv.org/html/2507.15184v2. The constants below are proved here and
are not an import of the source's numerical C5 estimate.
-/

noncomputable section

namespace Real

theorem neg_log_one_sub_le_div_of_lt_one {r : ℝ} (hr : r < 1) :
    -log (1 - r) ≤ r / (1 - r) := by
  have hp : 0 < 1 - r := by linarith
  calc -log (1 - r) ≤ -(1 - (1 - r)⁻¹) := neg_le_neg (one_sub_inv_le_log_of_pos hp)
    _ = r / (1 - r) := by field_simp [hp.ne']; ring

end Real

namespace Complex

theorem one_sub_sq_ne_zero_and_neg_log_norm_le_of_sq_le {e : ℂ} {r : ℝ}
    (hr : r < 1) (he : ‖e‖ ^ 2 ≤ r) :
    1 - e ^ 2 ≠ 0 ∧ -Real.log ‖1 - e ^ 2‖ ≤ -Real.log (1 - r) := by
  have hp : 0 < 1 - r := by linarith
  have hl0 : 1 - ‖e‖ ^ 2 ≤ ‖(1 : ℂ) - e ^ 2‖ := by
    have hh := norm_sub_norm_le (1 : ℂ) (e * e)
    have hnorm : ‖e * e‖ = ‖e‖ * ‖e‖ := Complex.norm_mul e e
    rw [norm_one, hnorm] at hh
    simpa only [pow_two] using hh
  have hl : 1 - r ≤ ‖(1 : ℂ) - e ^ 2‖ := by linarith
  refine ⟨norm_pos_iff.mp (hp.trans_le hl), ?_⟩
  exact neg_le_neg (Real.log_le_log hp hl)

end Complex
