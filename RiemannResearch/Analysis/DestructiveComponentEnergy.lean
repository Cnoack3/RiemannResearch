/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.LinearAlgebra.TwoChannelCancellation

/-!
# Quantitative cancellation of one component against its complement

Source: continuation of the two-seed exact-head energy research, 14 September
2026. These inequalities keep the full signed mixed inner product. They do
not assume orthogonality or an independently bounded arithmetic projection.
-/

namespace RiemannResearch.Analysis.DestructiveComponentEnergy

noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The mixed product's deviation from complete cancellation is exactly its
pairing with the full vector. -/
theorem mixed_deviation_exact (f u : E) :
    inner ℝ u (f - u) + ‖u‖ ^ 2 = inner ℝ u f := by
  rw [inner_sub_right, real_inner_self_eq_norm_sq]
  ring

/-- A small full vector forces cancellation relative to the component's own
energy, even if neither component is bounded. -/
theorem mixed_deviation_sq_le (f u : E) :
    (inner ℝ u (f - u) + ‖u‖ ^ 2) ^ 2 ≤ ‖u‖ ^ 2 * ‖f‖ ^ 2 := by
  rw [mixed_deviation_exact]
  have h := norm_inner_le_norm (𝕜 := ℝ) u f
  rw [Real.norm_eq_abs] at h
  have hs := mul_self_le_mul_self (abs_nonneg (inner ℝ u f)) h
  simpa only [← pow_two, sq_abs, mul_pow] using hs

/-- The same estimate after division by the actual component energy. -/
theorem normalized_mixed_deviation_sq_le (f u : E) (hu : u ≠ 0) :
    (inner ℝ u (f - u) / ‖u‖ ^ 2 + 1) ^ 2 ≤ ‖f‖ ^ 2 / ‖u‖ ^ 2 := by
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hd : 0 < ‖u‖ ^ 2 := sq_pos_of_pos hn
  have h := mixed_deviation_sq_le f u
  have he : (inner ℝ u (f - u) / ‖u‖ ^ 2 + 1) ^ 2 =
      (inner ℝ u (f - u) + ‖u‖ ^ 2) ^ 2 / (‖u‖ ^ 2) ^ 2 := by
    field_simp [ne_of_gt hn]
  rw [he]
  apply (div_le_div_iff₀ (sq_pos_of_pos hd) hd).mpr
  nlinarith [mul_le_mul_of_nonneg_right h hd.le]

omit [InnerProductSpace ℝ E] in
/-- Reverse triangle inequality measures the matching component sizes. -/
theorem complement_norm_deviation_le (f u : E) :
    |‖f - u‖ - ‖u‖| ≤ ‖f‖ := by
  have h := abs_norm_sub_norm_le (f - u) (-u)
  simpa only [norm_neg, sub_neg_eq_add, sub_add_cancel] using h

/-- No mixed term is hidden in the exact full energy. -/
theorem full_energy_exact (f u : E) :
    ‖f‖ ^ 2 = ‖u‖ ^ 2 + ‖f - u‖ ^ 2 + 2 * inner ℝ u (f - u) := by
  have h := RiemannResearch.LinearAlgebra.TwoChannelCancellation.norm_add_sq u (f - u)
  have he : u + (f - u) = f := by abel
  rwa [he] at h

/-- An angle separated from perfect opposition gives a coercive lower bound
for the complete energy; both component squares remain. -/
theorem full_energy_lower_of_angle (f u : E) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hangle : -(ρ * (‖u‖ * ‖f - u‖)) ≤ inner ℝ u (f - u)) :
    (1 - ρ) * (‖u‖ ^ 2 + ‖f - u‖ ^ 2) ≤ ‖f‖ ^ 2 := by
  have he := full_energy_exact f u
  have hd := mul_nonneg hρ (sq_nonneg (‖u‖ - ‖f - u‖))
  nlinarith

end
end RiemannResearch.Analysis.DestructiveComponentEnergy
