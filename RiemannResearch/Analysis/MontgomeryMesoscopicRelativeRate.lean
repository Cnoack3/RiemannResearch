/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MontgomeryMesoscopicUnitSlope

/-! # Quantitative transfer of the mesoscopic main term -/

noncomputable section
open Filter Set
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryHorizontalBessel
open MontgomeryHorizontalTransfer MontgomeryFormFactor

theorem raw_relative_abs_le_of_defect {T α M H E : ℝ} (hT : 1 < T) (hM : 0 < M)
    (hS : |sharpFormFactor T α/M-1| ≤ H) (hD : horizontalDefect T α/M ≤ E) :
    |formFactor T α/M-1| ≤ H+E+2*Real.sqrt (1+H)*Real.sqrt E := by
  have hH : 0 ≤ H := (abs_nonneg _).trans hS
  have hd0 : 0 ≤ horizontalDefect T α/M := by
    unfold horizontalDefect defectIntegral
    apply div_nonneg _ hM.le
    exact div_nonneg (MeasureTheory.integral_nonneg (fun _ =>
      mul_nonneg (Real.exp_pos _).le (sq_nonneg _))) (by have := Real.log_pos hT; positivity)
  have hSQ : |Real.sqrt (formFactor T α/M)-Real.sqrt (sharpFormFactor T α/M)| ≤
      Real.sqrt (horizontalDefect T α/M) := by
    rw [Real.sqrt_div' _ hM.le, Real.sqrt_div' _ hM.le, Real.sqrt_div' _ hM.le,
      ← sub_div, abs_div, abs_of_nonneg (Real.sqrt_nonneg _), abs_sub_comm]
    exact div_le_div_of_nonneg_right (sqrt_horizontal_error T α) (Real.sqrt_nonneg _)
  have hdiff := WeightedSqrtTransfer.abs_sub_le_of_sqrt (div_nonneg (formFactor_nonneg hT α) hM.le)
    (div_nonneg (MontgomeryHorizontalPairing.sharpFormFactor_nonneg hT α) hM.le) hd0 hSQ
  have hsup : Real.sqrt (sharpFormFactor T α/M) ≤ Real.sqrt (1+H) :=
    Real.sqrt_le_sqrt (by linarith only [(abs_le.mp hS).2])
  have hc := mul_le_mul (mul_le_mul_of_nonneg_left hsup (by norm_num : (0:ℝ)≤2))
    (Real.sqrt_le_sqrt hD) (Real.sqrt_nonneg _) (by positivity)
  have hh := (abs_add_le (formFactor T α/M - sharpFormFactor T α/M)
    (sharpFormFactor T α/M-1)).trans (add_le_add hdiff hS)
  rw [sub_add_sub_cancel] at hh
  linarith only [hh,hD,hc]

theorem mesoscopicMain_eq_spike_add {T : ℝ} (hT : 1 < T) (u : ℝ) :
    mesoscopicMain T u = Real.exp (-2*u)*Real.log T+u/Real.log T := by
  have hL := Real.log_pos hT
  rw [show -2*u = -(u+u) by ring, Real.exp_neg, Real.exp_add]
  unfold mesoscopicMain
  field_simp [hL.ne', (Real.exp_pos u).ne']
  <;> ring

/-- Normalized quartic bound for a phase whose linear term is positive. -/
theorem normalized_quartic_phase_bound {L C u D M : ℝ} (hL : 0 < L) (hC : 0 ≤ C)
    (hu : 1 ≤ u) (hM : u/L ≤ M) (hD : D ≤ C*(1+u)^4/L^3) :
    D/M ≤ 16*C*(u^3/L^2) := by
  have hU : 0 < u := zero_lt_one.trans_le hu
  have hp : (1+u)^4 ≤ (2*u)^4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
  have hD' := hD.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp hC) (pow_nonneg hL.le _))
  apply (div_le_iff₀ ((div_pos hU hL).trans_le hM)).mpr
  calc
    _ ≤ C*(2*u)^4/L^3 := hD'
    _ = 16*C*(u^3/L^2)*(u/L) := by field_simp [hL.ne']; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hM (by positivity)

/-- Finite two-term error for the raw ratio on the range u³ ≤ L². -/
theorem raw_mesoscopic_relative_rate {a : ℝ} (ha : 0 < a) (hQ : ReflectedQuarticDefectEstimate a)
    (hthird : PositiveCutoffThirdSignalSource) (hprime : QuadraticPrimeSignalMeanSquareSource) :
    ∃ K B : ℝ, 0 ≤ K ∧ 0 ≤ B ∧ ∀ᶠ T : ℝ in atTop, ∀ u : ℝ, 1 ≤ u →
      u ≤ Real.log T/2 → u ≤ a*Real.log T/4 → u^3 ≤ (Real.log T)^2 →
      |formFactor T (u/Real.log T) / mesoscopicMain T u-1| ≤ K/u+B*(u*Real.sqrt u/Real.log T) := by
  obtain ⟨K,hK,hk⟩ := sharp_mesoscopic_relative_bound hthird hprime
  obtain ⟨C,hC,hq⟩ := hQ
  let B := 16*C+2*Real.sqrt (1+K)*Real.sqrt (16*C)
  refine ⟨K,B,hK,by dsimp [B]; positivity,?_⟩
  filter_upwards [hk,hq,eventually_gt_atTop (1:ℝ)] with T hTsh hTq hT
  intro u hu hub hua hcub
  let L := Real.log T
  let M := mesoscopicMain T u
  let z := u*Real.sqrt u/L
  let α := u/L
  have hL : 0 < L := Real.log_pos hT
  have hU : 0 < u := zero_lt_one.trans_le hu
  have hM : u/L ≤ M := div_le_div_of_nonneg_right
    (le_add_of_nonneg_left (div_nonneg (sq_nonneg _) (sq_nonneg _))) hL.le
  have hM0 : 0 < M := (div_pos hU hL).trans_le hM
  have harg : α*L = u := div_mul_cancel₀ _ hL.ne'
  have hband : |α*L| ≤ a*L/4 := by rw [harg,abs_of_pos hU]; exact hua
  have hD := hTq α hband
  change horizontalDefect T α ≤ C*(1+|α*L|)^4/L^3 at hD
  rw [harg,abs_of_pos hU] at hD
  have hE := normalized_quartic_phase_bound hL hC hu hM hD
  have hZ : 0 ≤ z := div_nonneg (mul_nonneg hU.le (Real.sqrt_nonneg _)) hL.le
  have hz2 : z^2 = u^3/L^2 := by
    dsimp only [z]
    rw [div_pow,mul_pow,Real.sq_sqrt hU.le]
    ring
  have hz1 : z^2 ≤ 1 := hz2.trans_le ((div_le_iff₀ (pow_pos hL 2)).mpr (by simpa using hcub))
  have hzle1 : z ≤ 1 := by nlinarith only [hz1, sq_nonneg (z-1)]
  have hz : z^2 ≤ z := by nlinarith only [mul_nonneg hZ (sub_nonneg.mpr hzle1)]
  have hE' : horizontalDefect T α/M ≤ (16*C)*z^2 := by simpa only [hz2] using hE
  have hr := raw_relative_abs_le_of_defect hT hM0 (hTsh _ hu hub) hE'
  have hroot : Real.sqrt (16*C*z^2) = Real.sqrt (16*C)*z := by
    rw [Real.sqrt_mul (show 0≤16*C by positivity), Real.sqrt_sq hZ]
  have hsk : Real.sqrt (1+K/u) ≤ Real.sqrt (1+K) := Real.sqrt_le_sqrt
    (add_le_add (le_refl 1) ((div_le_iff₀ hU).mpr (le_mul_of_one_le_right hK hu)))
  rw [hroot] at hr
  have hp := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsk (by norm_num : (0:ℝ) ≤ 2))
    (mul_nonneg (Real.sqrt_nonneg (16*C)) hZ)
  have he := mul_le_mul_of_nonneg_left hz (show 0≤16*C by positivity)
  change |formFactor T α/M-1| ≤ K/u+B*z
  dsimp only [B]
  linarith only [hr,hp,he]

end RiemannResearch.Analysis.MontgomeryHorizontalBessel
