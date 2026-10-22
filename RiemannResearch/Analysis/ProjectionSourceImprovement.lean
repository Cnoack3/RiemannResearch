/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ProjectionCompressionDefect

/-!
# Signed source improvement under optimal refitting

Source: independently derived continuation of Christian Noack's two-seed
arithmetic improvement problem, 15 September 2026. The RH consumer uses P
for the current finite legal span and T for coordinates beyond a cutoff.
The arithmetic providers of source correlation and tail concentration are
separate obligations. These results retain every signed cross term and allow
arbitrary refitting of the old coefficients.
-/

namespace RiemannResearch.Analysis.ProjectionSourceImprovement

open RiemannResearch.Analysis.ProjectionCompression
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (P : Submodule ℝ H) [P.HasOrthogonalProjection]

/-- The actual residual of a Hilbert-space projection. -/
def residual (b : H) : H := b - P.starProjection b

theorem residual_inner (b z : H) :
    inner ℝ (residual P b) (residual P z) = inner ℝ (residual P b) z := by
  unfold residual
  rw [defect_inner, inner_sub_left]

private theorem norm_sub_sq (x y : H) :
    ‖x - y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * inner ℝ x y := by
  have h := RiemannResearch.LinearAlgebra.TwoChannelCancellation.norm_add_sq x (-y)
  simpa only [← sub_eq_add_neg, norm_neg, inner_neg_right, mul_neg] using h

/-- Exact gain from an actual new column after refitting all old coefficients. -/
theorem refit_gain_exact (b z : H) (a : ℝ) :
    ‖residual P b‖ ^ 2 - ‖b -
        (P.starProjection b + a • residual P z)‖ ^ 2 =
      2 * a * inner ℝ (residual P b) z - a ^ 2 * ‖residual P z‖ ^ 2 := by
  have he : b - (P.starProjection b + a • residual P z) =
      residual P b - a • residual P z := by
    unfold residual
    abel
  rw [he, norm_sub_sq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    real_inner_smul_right, residual_inner P]
  ring

/-- Nonzero source correlation forces a nonzero innovation. -/
theorem residual_ne_zero_of_inner_ne_zero (b z : H)
    (hc : inner ℝ (residual P b) z ≠ 0) : residual P z ≠ 0 := by
  intro hz
  have h := residual_inner P b z
  rw [hz, inner_zero_right] at h
  exact hc h.symm

/-- The optimal scalar yields its exact nonnegative Rayleigh gain. -/
theorem optimal_refit_gain (b z : H) (hz : residual P z ≠ 0) :
    ‖residual P b‖ ^ 2 - ‖b -
        (P.starProjection b +
          (inner ℝ (residual P b) z / ‖residual P z‖ ^ 2) • residual P z)‖ ^ 2 =
      (inner ℝ (residual P b) z) ^ 2 / ‖residual P z‖ ^ 2 := by
  rw [refit_gain_exact]
  have hn : ‖residual P z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  field_simp
  ring

/-- A nonzero arithmetic correlation gives strict finite improvement. -/
theorem exists_strict_refit (b z : H) (hc : inner ℝ (residual P b) z ≠ 0) :
    ∃ a : ℝ, ‖b - (P.starProjection b + a • residual P z)‖ ^ 2 <
      ‖residual P b‖ ^ 2 := by
  have hz := residual_ne_zero_of_inner_ne_zero P b z hc
  have hn : 0 < ‖residual P z‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hz)
  have hg := optimal_refit_gain P b z hz
  refine ⟨inner ℝ (residual P b) z / ‖residual P z‖ ^ 2, ?_⟩
  have hp := div_pos (sq_pos_of_ne_zero hc) hn
  linarith

/-- The refitted vector belongs to every enlarged subspace containing the new column. -/
theorem refit_mem (W : Submodule ℝ H) (hPW : P ≤ W) (b z : H)
    (hz : z ∈ W) (a : ℝ) : P.starProjection b + a • residual P z ∈ W := by
  exact W.add_mem (hPW (Submodule.starProjection_apply_mem P b))
    (W.smul_mem a (W.sub_mem hz (hPW (Submodule.starProjection_apply_mem P z))))

/-- Every other choice of old coefficients adds an orthogonal nonnegative error. -/
theorem refit_pythagoras (b p z : H) (hp : p ∈ P) :
    ‖b - (p + z)‖ ^ 2 =
      ‖residual P b - residual P z‖ ^ 2 +
        ‖P.starProjection b - p - P.starProjection z‖ ^ 2 := by
  have hv : P.starProjection b - p - P.starProjection z ∈ P :=
    P.sub_mem (P.sub_mem (Submodule.starProjection_apply_mem P b) hp)
      (Submodule.starProjection_apply_mem P z)
  have hb := Submodule.starProjection_inner_eq_zero b
    (P.starProjection b - p - P.starProjection z) hv
  have hz := Submodule.starProjection_inner_eq_zero z
    (P.starProjection b - p - P.starProjection z) hv
  have ho : inner ℝ (residual P b - residual P z)
      (P.starProjection b - p - P.starProjection z) = 0 := by
    rw [inner_sub_left]
    exact sub_eq_zero.mpr (hb.trans hz.symm)
  have he : b - (p + z) = (residual P b - residual P z) +
      (P.starProjection b - p - P.starProjection z) := by
    unfold residual
    abel
  rw [he, RiemannResearch.LinearAlgebra.TwoChannelCancellation.norm_add_sq, ho]
  ring

/-- Uniform bound for every block confined to a tail, including optimal old refitting. -/
theorem gain_le_tail_bound (T : Submodule ℝ H) [T.HasOrthogonalProjection]
    (b p z : H) (hp : p ∈ P) (hz : z ∈ T) {a : ℝ} (ha : a < 1)
    (hangle : ‖P.starProjection z‖ ^ 2 ≤ a * ‖z‖ ^ 2) :
    ‖residual P b‖ ^ 2 - ‖b - (p + z)‖ ^ 2 ≤
      ‖T.starProjection (residual P b)‖ ^ 2 / (1 - a) := by
  have ht := Submodule.starProjection_inner_eq_zero (residual P b) z hz
  rw [inner_sub_left] at ht
  have hc := norm_inner_le_norm (𝕜 := ℝ) (T.starProjection (residual P b)) z
  rw [Real.norm_eq_abs] at hc
  have hi : inner ℝ (residual P b) z ≤
      ‖T.starProjection (residual P b)‖ * ‖z‖ := by
    have h := (abs_le.mp hc).2
    linarith
  have hq := projection_pythagoras P z
  have he := norm_sub_sq (residual P b) (residual P z)
  rw [residual_inner P] at he
  have hpy := refit_pythagoras P b p z hp
  have hpos : 0 < 1 - a := sub_pos.mpr ha
  apply (le_div_iff₀ hpos).mpr
  have hs := sq_nonneg (‖T.starProjection (residual P b)‖ - (1 - a) * ‖z‖)
  have hbase : ‖residual P b‖ ^ 2 - ‖b - (p + z)‖ ^ 2 ≤
      2 * ‖T.starProjection (residual P b)‖ * ‖z‖ - (1 - a) * ‖z‖ ^ 2 := by
    change ‖z‖ ^ 2 = ‖P.starProjection z‖ ^ 2 + ‖residual P z‖ ^ 2 at hq
    nlinarith [sq_nonneg ‖P.starProjection b - p - P.starProjection z‖]
  have hm := mul_le_mul_of_nonneg_right hbase (le_of_lt hpos)
  nlinarith

/-- Periodic tail concentration yields a uniform relative upper bound on all improvements. -/
theorem gain_le_relative_tail_bound (T : Submodule ℝ H) [T.HasOrthogonalProjection]
    (b p z : H) (hp : p ∈ P) (hz : z ∈ T) {a : ℝ} (ha : a < 1)
    (hangle : ‖P.starProjection z‖ ^ 2 ≤ a * ‖z‖ ^ 2)
    (hsource : ‖T.starProjection (residual P b)‖ ^ 2 ≤ a * ‖residual P b‖ ^ 2) :
    ‖residual P b‖ ^ 2 - ‖b - (p + z)‖ ^ 2 ≤
      a / (1 - a) * ‖residual P b‖ ^ 2 := by
  have h := gain_le_tail_bound P T b p z hp hz ha hangle
  calc
    _ ≤ ‖T.starProjection (residual P b)‖ ^ 2 / (1 - a) := h
    _ ≤ (a * ‖residual P b‖ ^ 2) / (1 - a) :=
      div_le_div_of_nonneg_right hsource (le_of_lt (sub_pos.mpr ha))
    _ = _ := by ring

end
end RiemannResearch.Analysis.ProjectionSourceImprovement
