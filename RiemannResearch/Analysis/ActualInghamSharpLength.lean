/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualInghamComplementaryDiagonal
import RiemannResearch.Analysis.ActualInghamSharpEndpoint

/-!
# A single log with an additive interval-length term for the actual right edge

For a fixed positive moving-line parameter the signed mean-value theorem and
the complementary-divisor estimate on the diagonal save the logarithm on the
interval length. This strengthens the translated one-log bound uniformly in
the cutoff and both endpoints.
-/

noncomputable section
open MeasureTheory Complex
open scoped BigOperators
namespace RiemannResearch.Analysis.InghamMollifier

theorem exists_actual_moving_right_error_moment_add_log {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {X : ℕ}, 2 ≤ X → ∀ {H T : ℝ}, H ≤ T →
      (∫ t in H..T, ‖riemannZeta (((1 + δ / Real.log X : ℝ) : ℂ) + I*t) *
        mollifier X (((1 + δ / Real.log X : ℝ) : ℂ) + I*t) - 1‖ ^ 2) ≤
        C * ((T - H) / X + Real.log X) := by
  obtain ⟨D,hD,hdiag⟩ := exists_lcm_diagonal_le_of_two_le
  obtain ⟨B,hB,hform⟩ := exists_moving_lcm_form_bound (b := 2*δ) (by positivity)
  have htwo : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  let K := 52*B*((Real.log 2)⁻¹+(2*δ)⁻¹)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨D+K, by positivity, ?_⟩
  intro X hX H T hHT
  have hx2 : (2:ℝ) ≤ X := by exact_mod_cast hX
  have hx0 : (0:ℝ) < X := by linarith
  let ℓ := Real.log (X:ℝ)
  have hl : Real.log 2 ≤ ℓ := Real.log_le_log (by norm_num) hx2
  have hl0 : 0 < ℓ := htwo.trans_le hl
  let β := 1 + δ/ℓ
  let p := 1 + 2*δ/ℓ
  have hβ : 1 < β := by dsimp [β]; linarith [div_pos hδ hl0]
  have hp : 1 < p := by dsimp [p]; linarith [div_pos (mul_pos two_pos hδ) hl0]
  have he : 2*β-1 = p := by dsimp [β,p]; ring
  have hh := (abs_le.mp (abs_actual_right_error_moment_sub_lcm_diagonal_le hβ
    (by omega : 1 ≤ X) hHT)).2
  rw [he] at hh
  have hd := hdiag (by omega : 1 ≤ X) (by linarith : (2:ℝ) ≤ 2*β)
  have hz : ‖riemannZeta (p:ℂ)‖ ≤ 1 + ℓ/(2*δ) := by
    have hv := norm_riemannZeta_le_integral_test (show 1 < (p:ℂ).re from hp)
    simp only [Complex.ofReal_re] at hv
    convert hv using 1
    dsimp [p]
    field_simp
    ring
  have hone : 1 ≤ ℓ * (Real.log 2)⁻¹ := by
    simpa only [div_eq_mul_inv] using (one_le_div htwo).mpr hl
  have hr : 1 + ℓ/(2*δ) ≤ ((Real.log 2)⁻¹ + (2*δ)⁻¹)*ℓ := by
    rw [div_eq_mul_inv]
    linarith
  have hw : 52*(‖riemannZeta (p:ℂ)‖*truncatedMobiusLCMForm X p - 1) ≤ K*ℓ := by
    calc
      _ ≤ 52*(‖riemannZeta (p:ℂ)‖*B) := by
        have h := mul_le_mul_of_nonneg_left (hform X hX) (norm_nonneg (riemannZeta (p:ℂ)))
        change ‖riemannZeta (p:ℂ)‖ * truncatedMobiusLCMForm X p ≤ _ at h
        linarith
      _ ≤ 52*((((Real.log 2)⁻¹ + (2*δ)⁻¹)*ℓ)*B) := by
        have h := mul_le_mul_of_nonneg_right (hz.trans hr) hB.le
        linarith
      _ = _ := by dsimp [K]; ring
  have hdiag' := mul_le_mul_of_nonneg_left hd (sub_nonneg.mpr hHT)
  have hnon : 0 ≤ (T-H)/(X:ℝ) := div_nonneg (sub_nonneg.mpr hHT) hx0.le
  calc
    _ ≤ (T-H)*(D/X) + K*ℓ := by linarith
    _ = D*((T-H)/X) + K*ℓ := by ring
    _ ≤ (D+K)*((T-H)/X + ℓ) := by
      nlinarith [mul_nonneg hD.le hl0.le, mul_nonneg hK.le hnon]

/--
info: 'RiemannResearch.Analysis.InghamMollifier.exists_actual_moving_right_error_moment_add_log' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_actual_moving_right_error_moment_add_log

end RiemannResearch.Analysis.InghamMollifier
