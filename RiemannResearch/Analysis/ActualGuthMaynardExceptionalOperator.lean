/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualGuthMaynardFixedStrip
import RiemannResearch.Analysis.ActualZeroBadTailDensity

/-!
# Far-strip correction in the actual zero phase operator

The centered operator estimate uses the full d/(2N) factor in
`badCorrection_norm_le_badWeightedSum`. Applying the fixed-strip
Guth–Maynard input gives a power saving for this part whenever the
dimension is at most `T^b` and `b < 16/45`. The other copies are
outside the scope of this estimate.
-/

noncomputable section
open Filter Set Zeta23
namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open ActualZeroOrdinate

private theorem badCosh_quarter_le_exp {T x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    badWeightedSum T (1 / 4) (fun t => Real.cosh (x * t) - 1) ≤
      (1 / 2 : ℝ) * badWeightedSum T (1 / 4) (fun t => Real.exp (y * t)) := by
  classical
  unfold badWeightedSum FiniteStrictTail.badSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hdisp : 0 ≤ copyDisplacement T i := abs_nonneg _
  by_cases ht : 1 / 4 < copyDisplacement T i
  · simp only [if_pos ht]
    have hc := Real.cosh_sub_one_le_half_exp _ (mul_nonneg hx hdisp)
    have h := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hxy hdisp)
    linarith only [hc, h]
  · simp only [if_neg ht, mul_zero, le_refl]

/-- A single constant handles every dimension in the indicated range.
All corrections use the original copy normalization. -/
theorem badCorrection_quarter_of_guthMaynard (hG : GuthMaynardDensityHypothesis)
    {b ε : ℝ} (hb₀ : 0 ≤ b) (hb : b ≤ 20 / 9) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ d : ℕ, 1 ≤ d → (d : ℝ) ≤ T ^ b →
      ‖badCorrection T d (1 / 4)‖ ≤ C * T ^ (-4 / 9 + 5 * b / 4 + ε) := by
  obtain ⟨C, hC, he⟩ := normalized_badExp_quarter_of_guthMaynard hG hb₀ hb hε
  refine ⟨C / 4, by positivity, ?_⟩
  filter_upwards [he, eventually_ge_atTop (2 : ℝ)] with T hT hT₂
  intro d hd hdT
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd₀ : (0 : ℝ) < d := by linarith
  have hT₀ : 0 < T := by linarith
  have hlog : Real.log d ≤ b * Real.log T := by
    have h := Real.log_le_log hd₀ hdT
    rw [Real.rpow_def_of_pos hT₀, Real.log_exp] at h
    simpa only [mul_comm] using h
  have hw := badCosh_quarter_le_exp (T := T) (Real.log_nonneg hd') hlog
  have hN₀ : 0 ≤ (Ncount 0 T : ℝ) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hw
    (show 0 ≤ (d : ℝ) / (2 * (Ncount 0 T : ℝ)) by positivity)
  calc
    _ ≤ _ := (badCorrection_norm_le_badWeightedSum T d hd (1 / 4)).trans hscaled
    _ = ((d : ℝ) / 4) * (badWeightedSum T (1 / 4) (fun t => Real.exp (b * Real.log T * t)) /
        (Ncount 0 T : ℝ)) := by
      simp only [div_eq_mul_inv, mul_inv]; ring
    _ ≤ ((d : ℝ) / 4) * (C * T ^ (-4 / 9 + b / 4 + ε)) :=
      mul_le_mul_of_nonneg_left hT (by positivity)
    _ ≤ (T ^ b / 4) * (C * T ^ (-4 / 9 + b / 4 + ε)) :=
      mul_le_mul_of_nonneg_right (by linarith only [hdT]) (by positivity)
    _ = C / 4 * (T ^ b * T ^ (-4 / 9 + b / 4 + ε)) := by ring
    _ = C / 4 * T ^ (-4 / 9 + 5 * b / 4 + ε) := by
      rw [← Real.rpow_add hT₀, show b + (-4 / 9 + b / 4 + ε) = -4 / 9 + 5 * b / 4 + ε by ring]

/-- Every dimension up to T^b has a vanishing quarter-strip correction
with a fixed positive power margin throughout the open range b < 16/45. -/
theorem badCorrection_quarter_power_saving (hG : GuthMaynardDensityHypothesis)
    {b : ℝ} (hb₀ : 0 ≤ b) (hb : b < 16 / 45) :
    ∀ η : ℝ, 0 < η → η < 4 / 9 - 5 * b / 4 →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ d : ℕ, 1 ≤ d → (d : ℝ) ≤ T ^ b →
        ‖badCorrection T d (1 / 4)‖ ≤ C * T ^ (-η) := by
  intro η _hη hmargin
  let ε := 4 / 9 - 5 * b / 4 - η
  have hε : 0 < ε := sub_pos.mpr hmargin
  have h := badCorrection_quarter_of_guthMaynard hG hb₀ (by linarith only [hb]) hε
  have hexp : -4 / 9 + 5 * b / 4 + ε = -η := by dsimp [ε]; ring
  simpa only [hexp] using h

end RiemannResearch.Analysis.ActualZeroPhaseMoments
