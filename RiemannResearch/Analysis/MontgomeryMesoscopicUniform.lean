/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MontgomeryMesoscopicRelativeRate

/-! # Uniform spike and linear main term down to phase zero -/

noncomputable section
open Filter Set
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryHorizontalBessel
open MontgomeryHorizontalTransfer MontgomeryFormFactor

/-- Uniform relative complex bound retaining both terms, splitting at half
of log log T. -/
theorem sharp_mesoscopic_uniform_bound
    (hMT : CorrectedComplexFormFactorEstimate) (hthird : PositiveCutoffThirdSignalSource)
    (hprime : QuadraticPrimeSignalMeanSquareSource) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ᶠ T : ℝ in atTop, ∀ u ∈ Icc (0:ℝ) (Real.log T/2),
      |sharpFormFactor T (u/Real.log T) / mesoscopicMain T u-1| ≤
        2*C/Real.sqrt (Real.log T)+2*K/Real.log (Real.log T) := by
  obtain ⟨C,hC,hc⟩ := hMT
  obtain ⟨K,hK,hk⟩ := sharp_mesoscopic_relative_bound hthird hprime
  refine ⟨C,K,hC,hK,?_⟩
  filter_upwards [hc,hk,eventually_gt_atTop (1:ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 2] with T hMT' hkT hT hℓ
  intro u hu
  let L := Real.log T
  let ell := Real.log L
  let α := u/L
  let spike := Real.exp (-2*u)*L
  let M := mesoscopicMain T u
  have hL : 0 < L := Real.log_pos hT
  have hell : 0 < ell := (by norm_num : (0:ℝ)<2).trans_le hℓ
  have hα : 0 ≤ α := div_nonneg hu.1 hL.le
  have hsp : 0 < spike := mul_pos (Real.exp_pos _) hL
  have hM : M=spike+α := mesoscopicMain_eq_spike_add hT u
  have hM0 : 0 < M := by rw [hM]; exact add_pos_of_pos_of_nonneg hsp hα
  by_cases hlow : u ≤ ell/2
  · have harg : α*L=u := div_mul_cancel₀ _ hL.ne'
    have hb := hMT' α ⟨hα,(div_le_one hL).mpr (by linarith only [hu.2,hL.le])⟩
    change |sharpFormFactor T α-(Real.exp (-2*(α*L))*L+α)| ≤
      C*(Real.exp (-2*(α*L))*L+1)/Real.sqrt L at hb
    rw [harg] at hb
    have hsp1 : 1 ≤ spike := by
      have h := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
        (show -ell ≤ -2*u by linarith only [hlow])) hL.le
      simpa only [ell,Real.exp_neg,Real.exp_log hL,inv_mul_cancel₀ hL.ne'] using h
    have hn : spike+1 ≤ 2*M := by linarith only [hM,hα,hsp1]
    have hh : |sharpFormFactor T α-M| ≤ (2*C/Real.sqrt L)*M := by
      rw [hM]
      apply hb.trans
      calc
        _ ≤ C*(2*M)/Real.sqrt L := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hn hC) (Real.sqrt_nonneg _)
        _ = _ := by rw [hM]; ring
    have hrel : |sharpFormFactor T α/M-1| ≤ 2*C/Real.sqrt L := by
      rw [show sharpFormFactor T α/M-1 = (sharpFormFactor T α-M)/M by field_simp [hM0.ne'],
        abs_div,abs_of_pos hM0]
      exact (div_le_iff₀ hM0).mpr hh
    exact hrel.trans (le_add_of_nonneg_right (by positivity))
  · have hU : 0 < u := by linarith only [hlow,hell]
    have hell2 : 2 ≤ ell := hℓ
    have hU1 : 1 ≤ u := by linarith only [hlow,hell2]
    apply (hkT u hU1 hu.2).trans
    apply le_trans _ (le_add_of_nonneg_left (by positivity : 0 ≤ 2*C/Real.sqrt L))
    apply (div_le_div_iff₀ hU hell).mpr
    nlinarith only [mul_nonneg hK (show 0 ≤ 2*u-ell by linarith only [hlow])]

/-- Relative defect control is uniform at bounded phases and at growing
phases. The two summands make its zero-height contribution explicit. -/
theorem eventually_mesoscopic_defect_uniform {a : ℝ} (ha : 0 < a)
    (hQ : ReflectedQuarticDefectEstimate a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ a*Real.log T/4 →
      horizontalDefect T (u/Real.log T) / mesoscopicMain T u ≤
        16*C*(Real.exp 2/(Real.log T)^4+u^3/(Real.log T)^2) := by
  obtain ⟨C,hC,hq⟩ := hQ
  refine ⟨C,hC,?_⟩
  filter_upwards [hq,eventually_gt_atTop (1:ℝ)] with T hTQ hT
  intro u hu hb
  let L := Real.log T
  let M := mesoscopicMain T u
  let α := u/L
  have hL : 0 < L := Real.log_pos hT
  have hα : 0 ≤ α := div_nonneg hu hL.le
  have hM : M=Real.exp (-2*u)*L+α := mesoscopicMain_eq_spike_add hT u
  have hM0 : 0 < M := by rw [hM]; exact add_pos_of_pos_of_nonneg (mul_pos (Real.exp_pos _) hL) hα
  have harg : α*L=u := div_mul_cancel₀ _ hL.ne'
  have hband : |α*L| ≤ a*L/4 := by rw [harg,abs_of_nonneg hu]; exact hb
  have hD := hTQ α hband
  change horizontalDefect T α ≤ C*(1+|α*L|)^4/L^3 at hD
  rw [harg,abs_of_nonneg hu] at hD
  by_cases hhi : 1 ≤ u
  · have hax : u/L ≤ M := by rw [hM]; exact le_add_of_nonneg_left (mul_nonneg (Real.exp_pos _).le hL.le)
    apply (normalized_quartic_phase_bound hL hC hhi hax hD).trans
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by positivity)
  · have hpow : (1+u)^4 ≤ (2:ℝ)^4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
    have hh := hD.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC)
      (pow_nonneg hL.le _))
    have hsp : Real.exp (-2)*L ≤ M := by
      rw [hM]
      exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hL.le).trans
        (le_add_of_nonneg_right hα)
    have hcoef : 0 ≤ 16*C*(Real.exp 2/L^4) := by positivity
    have hsmall : horizontalDefect T α/M ≤ 16*C*(Real.exp 2/L^4) := by
      apply (div_le_iff₀ hM0).mpr
      calc
        _ ≤ C*(2:ℝ)^4/L^3 := hh
        _ = (16*C*(Real.exp 2/L^4))*(Real.exp (-2)*L) := by
          rw [Real.exp_neg]; field_simp [hL.ne',(Real.exp_pos 2).ne']; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hsp hcoef
    apply hsmall.trans
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by positivity)

/-- Uniform raw two-term asymptotic down to zero for every diverging
phase ceiling satisfying U³/L² → 0. -/
theorem uniform_raw_mesoscopic_profile {a : ℝ} (ha : 0 < a) (hQ : ReflectedQuarticDefectEstimate a)
    (hMT : CorrectedComplexFormFactorEstimate) (hthird : PositiveCutoffThirdSignalSource)
    (hprime : QuadraticPrimeSignalMeanSquareSource) (U : ℝ → ℝ) (hU : Tendsto U atTop atTop)
    (hsmall : Tendsto (fun T => (U T)^3/(Real.log T)^2) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop, ∀ u ∈ Icc (0:ℝ) (U T),
      |formFactor T (u/Real.log T) / mesoscopicMain T u-1| ≤ ε := by
  obtain ⟨C,K,hC,hK,hs⟩ := sharp_mesoscopic_uniform_bound hMT hthird hprime
  obtain ⟨B,hB,hd⟩ := eventually_mesoscopic_defect_uniform ha hQ
  let H (T : ℝ) := 2*C/Real.sqrt (Real.log T)+2*K/Real.log (Real.log T)
  let E (T : ℝ) := 16*B*(Real.exp 2/(Real.log T)^4+(U T)^3/(Real.log T)^2)
  have hH : Tendsto H atTop (𝓝 0) := by
    have h := ((Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop).const_div_atTop (2*C)).add
      ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).const_div_atTop (2*K))
    simpa only [H,Function.comp_def,zero_add] using h
  have hL4 : Tendsto (fun T : ℝ => (Real.log T)^4) atTop atTop :=
    (tendsto_pow_atTop_iff.mpr (by decide : (4:ℕ) ≠ 0)).comp Real.tendsto_log_atTop
  have hE : Tendsto E atTop (𝓝 0) := by
    have h := ((hL4.const_div_atTop (Real.exp 2)).add hsmall).const_mul (16*B)
    simpa only [E,zero_add,mul_zero] using h
  have h1 : Tendsto (fun T => 1+H T) atTop (𝓝 1) := by
    simpa only [add_zero] using ((tendsto_const_nhds (x:=(1:ℝ))).add hH)
  have hrS := (Real.continuous_sqrt.continuousAt (x:=1)).tendsto.comp h1
  have hrE := (Real.continuous_sqrt.continuousAt (x:=0)).tendsto.comp hE
  have hR := (hH.add hE).add ((hrS.const_mul 2).mul hrE)
  simp only [Function.comp_def,Real.sqrt_zero,Real.sqrt_one,add_zero,zero_add,mul_zero] at hR
  intro ε hε
  filter_upwards [hs,hd,hR.eventually_le_const hε,eventually_gt_atTop (1:ℝ),
    eventually_mesoscopic_band hU hsmall (show 0 < a/4 by positivity),
    eventually_mesoscopic_band hU hsmall (show (0:ℝ)<1/2 by norm_num)]
    with T hTS hTD hεT hT hba hbh
  intro u hu
  have hband1 : u ≤ Real.log T/2 := by linarith only [hu.2,hbh.2]
  have hband2 : u ≤ a*Real.log T/4 := by linarith only [hu.2,hba.2]
  have hM : 0 < mesoscopicMain T u := by
    rw [mesoscopicMain_eq_spike_add hT]
    exact add_pos_of_pos_of_nonneg (mul_pos (Real.exp_pos _) (Real.log_pos hT))
      (div_nonneg hu.1 (Real.log_pos hT).le)
  have hD := (hTD u hu.1 hband2).trans (show
      16*B*(Real.exp 2/(Real.log T)^4+u^3/(Real.log T)^2) ≤ E T by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add le_rfl
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hu.1 hu.2 _) (sq_nonneg _))
  exact (raw_relative_abs_le_of_defect hT hM (hTS u ⟨hu.1,hband1⟩) hD).trans hεT

/-- A bounded or fluctuating ceiling can be enlarged to a diverging ceiling
without changing the cubic smallness condition. -/
theorem uniform_raw_mesoscopic_profile_of_cube {a : ℝ} (ha : 0 < a)
    (hQ : ReflectedQuarticDefectEstimate a) (hMT : CorrectedComplexFormFactorEstimate)
    (hthird : PositiveCutoffThirdSignalSource) (hprime : QuadraticPrimeSignalMeanSquareSource)
    (U : ℝ → ℝ) (hsmall : Tendsto (fun T => (U T)^3/(Real.log T)^2) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop, ∀ u ∈ Icc (0:ℝ) (U T),
      |formFactor T (u/Real.log T) / mesoscopicMain T u-1| ≤ ε := by
  let ell (T : ℝ) := Real.log (Real.log T)
  let W (T : ℝ) := max (U T) (ell T)
  have hEll : Tendsto ell atTop atTop := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hW : Tendsto W atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact (hEll.eventually_ge_atTop b).mono fun T hT => hT.trans (le_max_right _ _)
  have hAbs := hsmall.abs
  simp only [abs_zero] at hAbs
  have hBound := hAbs.add (loglog_pow_div_log_tendsto_zero 3)
  simp only [Function.comp_def,zero_add] at hBound
  have hWcube : Tendsto (fun T => (W T)^3/(Real.log T)^2) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hBound
    · filter_upwards [hW.eventually_ge_atTop 0] with T hT
      positivity
    · filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,hEll.eventually_ge_atTop 0]
        with T hL hE
      have hL0 : 0 < Real.log T := zero_lt_one.trans_le hL
      by_cases hb : ell T ≤ U T
      · rw [show W T = U T by exact max_eq_left hb]
        exact (le_abs_self _).trans (le_add_of_nonneg_right
          (div_nonneg (pow_nonneg hE _) hL0.le))
      · rw [show W T = ell T by exact max_eq_right (le_of_not_ge hb)]
        have hl2 : Real.log T ≤ (Real.log T)^2 := by
          nlinarith only [mul_nonneg hL0.le (sub_nonneg.mpr hL)]
        exact (div_le_div_of_nonneg_left (pow_nonneg hE _) hL0 hl2).trans
          (le_add_of_nonneg_left (abs_nonneg _))
  intro ε hε
  filter_upwards [uniform_raw_mesoscopic_profile ha hQ hMT hthird hprime W hW hWcube ε hε]
    with T hT
  intro u hu
  exact hT u ⟨hu.1,hu.2.trans (le_max_left _ _)⟩

/-- The positive-phase result controls both Fourier signs by exact evenness
of the actual-ordinate statistic. -/
theorem uniform_raw_mesoscopic_symmetric {a : ℝ} (ha : 0 < a) (hQ : ReflectedQuarticDefectEstimate a)
    (hMT : CorrectedComplexFormFactorEstimate) (hthird : PositiveCutoffThirdSignalSource)
    (hprime : QuadraticPrimeSignalMeanSquareSource) (U : ℝ → ℝ)
    (hsmall : Tendsto (fun T => (U T)^3/(Real.log T)^2) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop, ∀ u : ℝ, |u| ≤ U T →
      |formFactor T (u/Real.log T) / mesoscopicMain T |u| - 1| ≤ ε := by
  intro ε hε
  filter_upwards [uniform_raw_mesoscopic_profile_of_cube ha hQ hMT hthird hprime U hsmall ε hε] with T hT
  intro u hu
  have he : formFactor T (u/Real.log T) = formFactor T (|u|/Real.log T) := by
    by_cases h : 0 ≤ u
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h), neg_div, formFactor_even]
  rw [he]
  exact hT |u| ⟨abs_nonneg _,hu⟩

end RiemannResearch.Analysis.MontgomeryHorizontalBessel
