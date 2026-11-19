/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MontgomeryMesoscopicCrossover
import RiemannResearch.Analysis.MontgomeryMesoscopicRelativeRate

/-! # The first logarithmic correction at the spike–slope crossover -/

noncomputable section
open Filter Set
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryHorizontalBessel
open MontgomeryFormFactor

private theorem centered_shift_algebra {E U D c : ℝ} (hu : U ≠ 0) (hd : D ≠ 0)
    (hz : U = E-D/2+c) : E/U*(1/2-c/D)=E/D*(E/U-1) := by
  field_simp [hu,hd]
  rw [hz]
  ring

private theorem combined_ratio_algebra {L U x : ℝ} (hl : L ≠ 0) (hu : U ≠ 0) (hx : x ≠ 0) :
    ((L^2/x^2+U)/L)/(U/L) = 1+L^2/x^2/U := by
  field_simp [hl,hu,hx]
  <;> ring

theorem raw_unit_slope_crossover_log_correction {a : ℝ} (ha : 0 < a)
    (hQ : ReflectedQuarticDefectEstimate a)
    (hthird : PositiveCutoffThirdSignalSource) (hprime : QuadraticPrimeSignalMeanSquareSource)
    (c : ℝ) :
    let ell := fun T : ℝ => Real.log (Real.log T)
    let u := unitSlopeCrossoverPhase c
    Tendsto (fun T => (ell T/Real.log (ell T)) *
      (formFactor T (u T/Real.log T)/(u T/Real.log T)-1-Real.exp (-2*c)))
      atTop (𝓝 (Real.exp (-2*c)/2)) := by
  let ell := fun T : ℝ => Real.log (Real.log T)
  let u := unitSlopeCrossoverPhase c
  let g := Real.exp (-2*c)
  let Z := fun T : ℝ => formFactor T (u T/Real.log T)
  let M := fun T : ℝ => mesoscopicMain T (u T)
  let α := fun T : ℝ => u T/Real.log T
  let k := fun T : ℝ => ell T/Real.log (ell T)
  change Tendsto (fun T => k T*(Z T/α T-1-g)) atTop (𝓝 (g/2))
  obtain ⟨hq,hbox,hu,hsmall,hsp⟩ := unitSlopeCrossoverPhase_controls c
  have hel : Tendsto ell atTop atTop := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hden : Tendsto (fun T => Real.log (ell T)) atTop atTop := Real.tendsto_log_atTop.comp hel
  have hq' : Tendsto (fun T => ell T/u T) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x:=(1:ℝ))).div hq (by norm_num)
    rw [div_one] at h
    apply h.congr'
    filter_upwards [hbox,hu.eventually_gt_atTop 0] with T hE hU
    change 1/(u T/ell T)=ell T/u T
    field_simp [hE.1.ne',hU.ne']
  have hshift : Tendsto (fun T => k T*(ell T/u T-1)) atTop (𝓝 (1/2)) := by
    have h := hq'.mul ((tendsto_const_nhds (x:=(1/2:ℝ))).sub (hden.const_div_atTop c))
    rw [sub_zero,one_mul] at h
    apply h.congr'
    filter_upwards [hden.eventually_gt_atTop 0,hu.eventually_gt_atTop 0] with T hD hU
    change ell T/u T*(1/2-c/Real.log (ell T))=k T*(ell T/u T-1)
    dsimp only [k]
    have hz : u T = ell T-Real.log (ell T)/2+c := rfl
    exact centered_shift_algebra (U:=u T) (D:=Real.log (ell T)) hU.ne' hD.ne' hz
  have hmain : ∀ᶠ T : ℝ in atTop, M T/α T = 1+g*(ell T/u T) := by
    filter_upwards [hsp,hbox,hu.eventually_gt_atTop 0,eventually_gt_atTop (1:ℝ)]
      with T hS hE hU hT
    have hL := Real.log_pos hT
    change mesoscopicMain T (u T)/(u T/Real.log T)=1+g*(ell T/u T)
    calc
      _ = 1+(Real.log T)^2/(Real.exp (u T))^2/u T := by
        exact combined_ratio_algebra (U:=u T) (x:=Real.exp (u T))
          hL.ne' hU.ne' (Real.exp_pos _).ne'
      _ = _ := by
        change g/(u T/ell T) = (Real.log T)^2/(Real.exp (u T))^2/u T at hS
        rw [← hS]
        field_simp [hU.ne',hE.1.ne']
  have hMr : Tendsto (fun T => M T/α T) atTop (𝓝 (1+g)) := by
    have h := (tendsto_const_nhds (x:=(1:ℝ))).add (hq'.const_mul g)
    rw [mul_one] at h
    exact h.congr' (hmain.mono fun _ hT => hT.symm)
  obtain ⟨K,B,hK,hB,hr⟩ := raw_mesoscopic_relative_rate ha hQ hthird hprime
  have hb1 := eventually_mesoscopic_band hu hsmall (show (0:ℝ)<1/2 by norm_num)
  have hba := eventually_mesoscopic_band hu hsmall (show 0<a/4 by positivity)
  have hcub := hsmall.eventually_le_const (by norm_num : (0:ℝ)<1)
  have hrate : Tendsto (fun T => k T*(Z T/M T-1)) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [sub_zero,Real.norm_eq_abs]
    have hc := (hden.const_div_atTop (2*K)).add ((loglog_pow_div_log_tendsto_zero 3).const_mul (4*B))
    simp only [mul_zero,add_zero] at hc
    apply squeeze_zero' (.of_forall fun _ => abs_nonneg _) _ hc
    filter_upwards [hr,hb1,hba,hcub,hbox,hden.eventually_ge_atTop 1,
      hu.eventually_ge_atTop 1,eventually_gt_atTop (1:ℝ)]
      with T hR hbT haT hcT hE hD hU hT
    change 0 < ell T ∧ ell T/2 ≤ u T ∧ u T ≤ 2*ell T at hE
    change 1 ≤ u T at hU
    have hL := Real.log_pos hT
    have hU0 : 0 < u T := zero_lt_one.trans_le hU
    have hD0 : 0 < Real.log (ell T) := zero_lt_one.trans_le hD
    have hZ := hR (u T) hU (by linarith only [hbT.2]) (by linarith only [haT.2])
      (by simpa only [one_mul] using (div_le_iff₀ (pow_pos hL 2)).mp hcT)
    have hKbound : k T*(K/u T) ≤ 2*K/Real.log (ell T) := by
      dsimp only [k]
      rw [show ell T/Real.log (ell T)*(K/u T) = (K*ell T/u T)/Real.log (ell T) by ring]
      apply div_le_div_of_nonneg_right _ hD0.le
      apply (div_le_iff₀ hU0).mpr
      calc
        _ ≤ K*(2*u T) := mul_le_mul_of_nonneg_left (by linarith only [hE.2.1]) hK
        _ = _ := by ring
    have hkE : k T ≤ ell T := (div_le_iff₀ hD0).mpr (le_mul_of_one_le_right hE.1.le hD)
    have hrU : Real.sqrt (u T) ≤ u T := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨hU0.le,?_⟩
      rw [sq]
      exact le_mul_of_one_le_right hU0.le hU
    have hprod : k T*(B*(u T*Real.sqrt (u T)/Real.log T)) ≤ 4*B*(ell T^3/Real.log T) := by
      have hp := mul_le_mul hE.2.2 (hrU.trans hE.2.2) (Real.sqrt_nonneg _) (by linarith only [hE.1])
      have hp' := mul_le_mul hkE (mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hp hL.le) hB) (by positivity) hE.1.le
      calc
        _ ≤ ell T*(B*((2*ell T)*(2*ell T)/Real.log T)) := hp'
        _ = _ := by ring
    change |k T*(Z T/M T-1)| ≤ 2*K/Real.log (ell T)+4*B*(ell T^3/Real.log T)
    rw [abs_mul,abs_of_nonneg (div_nonneg hE.1.le hD0.le)]
    apply (mul_le_mul_of_nonneg_left hZ (div_nonneg hE.1.le hD0.le)).trans
    rw [mul_add]
    exact add_le_add hKbound hprod
  have hfinal := (hrate.mul hMr).add (hshift.const_mul g)
  simp only [zero_mul,zero_add] at hfinal
  have hf : Tendsto (fun T => (k T*(Z T/M T-1))*(M T/α T)+g*(k T*(ell T/u T-1)))
      atTop (𝓝 (g/2)) := by
    simpa only [mul_one_div] using hfinal
  apply hf.congr'
  filter_upwards [hmain,hu.eventually_gt_atTop 0,eventually_gt_atTop (1:ℝ)] with T hMR hU hT
  have hL := Real.log_pos hT
  have hM0 : 0 < M T := by
    dsimp only [M,mesoscopicMain]
    exact div_pos (by positivity) hL
  have hA : 0 < α T := div_pos hU hL
  change (k T*(Z T/M T-1))*(M T/α T)+g*(k T*(ell T/u T-1)) = k T*(Z T/α T-1-g)
  have ha : (Z T/M T)*(M T/α T)=Z T/α T := by field_simp [hM0.ne',hA.ne']
  linear_combination k T*ha - k T*hMR

end RiemannResearch.Analysis.MontgomeryHorizontalBessel
