/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MontgomeryMesoscopicUnitSlope

/-! # The crossover where Montgomery's spike matches the linear term

At phase u = log L - (log log L)/2 + c with L = log T, the spike divided
by the linear term tends to exp(-2c). Both terms survive in the raw ratio. -/

noncomputable section
open Filter Set
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryHorizontalBessel
open MontgomeryFormFactor

def unitSlopeCrossoverPhase (c T : ℝ) : ℝ :=
  Real.log (Real.log T) - Real.log (Real.log (Real.log T))/2 + c

theorem unitSlopeCrossoverPhase_controls (c : ℝ) :
    let ell := fun T : ℝ => Real.log (Real.log T)
    let u := unitSlopeCrossoverPhase c
    Tendsto (fun T => u T/ell T) atTop (𝓝 1) ∧
    (∀ᶠ T : ℝ in atTop, 0 < ell T ∧ ell T/2 ≤ u T ∧ u T ≤ 2*ell T) ∧
    Tendsto u atTop atTop ∧ Tendsto (fun T => (u T)^3/(Real.log T)^2) atTop (𝓝 0) ∧
    (∀ᶠ T : ℝ in atTop, Real.exp (-2*c)/(u T/ell T) =
      (Real.log T)^2/(Real.exp (u T))^2/u T) := by
  let ell (T : ℝ) := Real.log (Real.log T)
  let u := unitSlopeCrossoverPhase c
  have hel : Tendsto ell atTop atTop := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hll : Tendsto (fun T => Real.log (ell T)/ell T) atTop (𝓝 0) := by
    simpa only [ell,Function.comp_def,pow_one] using
      (loglog_pow_div_log_tendsto_zero 1).comp Real.tendsto_log_atTop
  have hq : Tendsto (fun T => u T/ell T) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1:ℝ))).sub (hll.div_const 2)
    have h' := h.add (tendsto_const_nhds.div_atTop hel : Tendsto (fun T => c / ell T) atTop (𝓝 0))
    simp only [zero_div, sub_zero, add_zero] at h'
    apply h'.congr'
    filter_upwards [hel.eventually_gt_atTop 0] with T hT
    dsimp only [ell] at hT
    dsimp only [u,unitSlopeCrossoverPhase,ell]
    field_simp [hT.ne']
    <;> ring
  have hbox : ∀ᶠ T : ℝ in atTop, 0 < ell T ∧ ell T/2 ≤ u T ∧ u T ≤ 2*ell T := by
    have hlow : ∀ᶠ T : ℝ in atTop, (1/2:ℝ) ≤ u T / ell T :=
      (hq.eventually (Ioi_mem_nhds (by norm_num : (1/2:ℝ) < 1))).mono fun _ h => h.le
    have hhigh : ∀ᶠ T : ℝ in atTop, u T / ell T ≤ 2 := hq.eventually_le_const (by norm_num)
    filter_upwards [hel.eventually_gt_atTop 0,hlow,hhigh] with T hE hlo hhi
    exact ⟨hE, by linarith only [(le_div_iff₀ hE).mp hlo], (div_le_iff₀ hE).mp hhi⟩
  have hu : Tendsto u atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [hbox,hel.eventually_ge_atTop (2*b)] with T hboxT hET
    linarith only [hboxT.2.1,hET]
  have hsmall : Tendsto (fun T => (u T)^3/(Real.log T)^2) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ (show Tendsto (fun T => 8*((ell T)^3/Real.log T)) atTop (𝓝 0) by
      simpa only [ell,mul_zero] using (loglog_pow_div_log_tendsto_zero 3).const_mul 8)
    · filter_upwards [hu.eventually_gt_atTop 0] with T hU
      positivity
    · filter_upwards [hbox,hu.eventually_ge_atTop 0,Real.tendsto_log_atTop.eventually_ge_atTop 1]
        with T hE hU hL
      have hL0 : 0 < Real.log T := zero_lt_one.trans_le hL
      calc
        _ ≤ (2*ell T)^3/(Real.log T)^2 := div_le_div_of_nonneg_right
          (pow_le_pow_left₀ hU hE.2.2 3) (sq_nonneg _)
        _ ≤ (2*ell T)^3/Real.log T := div_le_div_of_nonneg_left
          (pow_nonneg (mul_nonneg (by norm_num) hE.1.le) _) hL0
          (by nlinarith only [mul_nonneg hL0.le (sub_nonneg.mpr hL)])
        _ = _ := by ring
  refine ⟨hq,hbox,hu,hsmall,?_⟩
  filter_upwards [hbox,hu.eventually_gt_atTop 0,eventually_gt_atTop (1:ℝ)] with T hE hU hT
  have he : (Real.exp (u T))^2 =
      (Real.log T)^2 / ell T * Real.exp (2*c) := by
    rw [← Real.exp_nat_mul]
    have hz : (2:ℝ)*u T = (ell T+ell T-Real.log (ell T)) + 2*c := by
      dsimp only [u,unitSlopeCrossoverPhase,ell]; ring
    norm_num only [Nat.cast_ofNat]
    rw [hz,Real.exp_add,Real.exp_sub,Real.exp_add,Real.exp_log hE.1,
      show Real.exp (ell T) = Real.log T by exact Real.exp_log (Real.log_pos hT)]
    ring
  change Real.exp (-2*c)/(u T/ell T) = (Real.log T)^2/(Real.exp (u T))^2/u T
  rw [he, show -2*c = -(2*c) by ring, Real.exp_neg]
  field_simp [hE.1.ne',hU.ne',(Real.log_pos hT).ne',(Real.exp_pos (2*c)).ne']
  <;> ring

theorem raw_unit_slope_crossover {a : ℝ} (ha : 0 < a)
    (hQ : ReflectedQuarticDefectEstimate a)
    (hthird : PositiveCutoffThirdSignalSource) (hprime : QuadraticPrimeSignalMeanSquareSource)
    (c : ℝ) :
    Tendsto (fun T => formFactor T (unitSlopeCrossoverPhase c T/Real.log T) /
      (unitSlopeCrossoverPhase c T/Real.log T)) atTop (𝓝 (Real.exp (-2*c)+1)) := by
  obtain ⟨hq,_,hu,hsmall,he⟩ := unitSlopeCrossoverPhase_controls c
  have h := (tendsto_const_nhds (x:=Real.exp (-2*c))).div hq (by norm_num)
  rw [div_one] at h
  exact raw_mesoscopic_spike_ratio ha hQ hthird hprime _ hu hsmall (h.congr' he)

end RiemannResearch.Analysis.MontgomeryHorizontalBessel
