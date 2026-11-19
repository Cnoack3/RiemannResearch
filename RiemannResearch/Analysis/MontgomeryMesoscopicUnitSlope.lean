/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MontgomeryMesoscopicGramTransfer
import RiemannResearch.Analysis.MontgomeryBGSTBTransitionComponents

/-! # The unit slope of the raw mesoscopic form factor

BGSTB's positive-cutoff decomposition and the prime mean square control
the relative complex error. Fourth-order reflection transfers both the
spike and the linear term to the raw form factor. See BGSTB §3 (3.4),
https://arxiv.org/html/2501.14545v3#S3.E4. -/

noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryHorizontalBessel
open MontgomeryHorizontalTransfer MontgomeryFormFactor MontgomeryPrimeCrossIntegral

/-- Combined spike and linear main term in phase coordinates. -/
def mesoscopicMain (T u : ℝ) : ℝ := (Real.log T^2/(Real.exp u)^2+u)/Real.log T

/-- Relative two-term bound throughout the phase range 1 ≤ u ≤ (log T)/2.
The absolute errors in the third signal and the prime mean square are
divided by their common unnormalized scale. -/
theorem sharp_mesoscopic_relative_bound (hthird : PositiveCutoffThirdSignalSource)
    (hprime : QuadraticPrimeSignalMeanSquareSource) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ T : ℝ in atTop, ∀ u : ℝ, 1 ≤ u → u ≤ Real.log T/2 →
      |sharpFormFactor T (u/Real.log T) / mesoscopicMain T u - 1| ≤ K/u := by
  obtain ⟨D,hD,hd⟩ := hthird
  obtain ⟨J,hJ,hp⟩ := hprime
  let X := 4/Real.log 2 * ∑' n : ℕ, mangoldtThreeHalves n
  let H := 4+2*J
  let K := D*(4+Real.sqrt (2*H)) + 3 + 2*J + 2*X
  have hX : 0 ≤ X := by
    exact mul_nonneg (by positivity) (tsum_nonneg fun n =>
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hH : 0 ≤ H := by dsimp [H]; positivity
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  filter_upwards [hd,hp,eventually_ge_atTop (2:ℝ)] with T h3 h2 hT
  intro u hu hub
  let L := Real.log T
  let x := Real.exp u
  let S := L^2/x^2+u
  let G := T*S/u
  let E := T/x^2+x
  have hT0 : 0 < T := by linarith
  have hT1 : 1 < T := by linarith
  have hL : 0 < L := Real.log_pos hT1
  have hU : 0 < u := zero_lt_one.trans_le hu
  have hxp : 0 < x := Real.exp_pos _
  have hxu : Real.log x = u := Real.log_exp u
  have hx2 : 2 ≤ x := (by linarith : 2 ≤ 1+u).trans (by simpa only [add_comm] using Real.add_one_le_exp u)
  have hux : u ≤ x := by linarith only [Real.add_one_le_exp u]
  have hxs : x^2 ≤ T := by
    dsimp only [x]
    rw [← Real.exp_nat_mul, ← Real.exp_log hT0]
    apply Real.exp_le_exp.mpr
    change (2:ℝ)*u ≤ Real.log T
    linarith
  have hxt : x ≤ T := (show x ≤ x^2 by nlinarith only [hx2,sq_nonneg (x-1)]).trans hxs
  have hUS : u ≤ S := le_add_of_nonneg_left (div_nonneg (sq_nonneg L) (sq_nonneg x))
  have hS : 0 < S := hU.trans_le hUS
  have hG : 0 < G := div_pos (mul_pos hT0 hS) hU
  have hTg : T ≤ G := (le_div_iff₀ hU).mpr (mul_le_mul_of_nonneg_left hUS hT0.le)
  have hTS : T*S = G*u := (div_mul_cancel₀ _ hU.ne').symm
  have hLu : L*u ≤ L^2 := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left (by dsimp only [L]; linarith) hL.le
  have hC1 : L*u/x^2 ≤ S := (div_le_div_of_nonneg_right hLu (sq_nonneg x)).trans
    (le_add_of_nonneg_right hU.le)
  have hA1 : |logSignalEnergy T x-T*L^2/x^2| ≤ 3*G := by
    apply (MontgomeryLogMeanSquare.log_mean_square_error_le hT x).trans
    have hh := mul_le_mul_of_nonneg_left hC1 (show 0 ≤ 3*T by positivity)
    change 3*T*Real.log T/x^2 ≤ 3*(T*S/u)
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hU).mpr
    convert hh using 1 <;> ring
  have hA2 : |primeSignalEnergy T x-T*u| ≤ (2*J)*G := by
    rw [← hxu]
    apply (h2 x ⟨hx2,hxt⟩).trans
    have hh := mul_le_mul_of_nonneg_left (add_le_add hTg (hxs.trans hTg)) hJ
    linarith only [hh]
  have hMsum : logSignalEnergy T x+primeSignalEnergy T x ≤ H*G*u := by
    have herr := add_le_add (abs_le.mp hA1).2 (abs_le.mp hA2).2
    have hg1 := le_mul_of_one_le_right hG.le hu
    have hrem := mul_le_mul_of_nonneg_left hg1 (show 0≤3+2*J by positivity)
    have he : T*L^2/x^2+T*u=G*u := by rw [← hTS]; dsimp [S]; ring
    dsimp only [H]
    nlinarith only [herr,hrem,he]
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hE : E ≤ 2*G/u := by
    have hu2 : u ≤ x^2 := hux.trans (by nlinarith only [hx2,sq_nonneg (x-1)])
    have hux' : x*u ≤ T := (mul_le_mul_of_nonneg_left hux hxp.le).trans
      (by simpa only [pow_two] using hxs)
    have hdiv : T/x^2 ≤ T/u := div_le_div_of_nonneg_left hT0.le hU hu2
    have hxdiv : x ≤ T/u := (le_div_iff₀ hU).mpr hux'
    have htt := div_le_div_of_nonneg_right hTg hU.le
    calc
      _ ≤ G/u+G/u := add_le_add (hdiv.trans htt) (hxdiv.trans htt)
      _ = _ := by ring
  have hEc : E ≤ 2*G := hE.trans ((div_le_iff₀ hU).mpr
    (le_mul_of_one_le_right (by positivity) hu))
  have hsqr : Real.sqrt ((logSignalEnergy T x+primeSignalEnergy T x)*E) ≤
      Real.sqrt (2*H)*G := by
    calc
      _ ≤ Real.sqrt ((2*H)*G^2) := Real.sqrt_le_sqrt
        ((mul_le_mul hMsum hE hE0 (by positivity)).trans_eq (by field_simp [hU.ne']))
      _ = _ := by rw [Real.sqrt_mul (show 0 ≤ 2*H by positivity), Real.sqrt_sq hG.le]
  have hsqrtT : Real.sqrt T ≤ T := by
    nlinarith only [Real.sq_sqrt hT0.le, Real.sqrt_nonneg T, hT, sq_nonneg (Real.sqrt T-1)]
  have hthird' : |thirdSignalResidual T x| ≤ D*(4+Real.sqrt (2*H))*G := by
    apply (h3 x ⟨by linarith,hxt⟩).trans
    have hh := mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (add_le_add (hsqrtT.trans hTg) (hxt.trans hTg)) hEc) hsqr) hD
    convert hh using 1 <;> ring
  have hm : |2*(crossIntegral x T).re| ≤ 2*X*G := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
    apply (mul_le_mul_of_nonneg_left (primeCross_linear_bound hT hxp) (by norm_num : (0:ℝ) ≤ 2)).trans
    change 2*(X*T) ≤ 2*X*G
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left hTg (by positivity)
  have hsum : |2*Real.pi*(actualComplexPairSum T (Real.log x)).re-T*S| ≤ K*G := by
    have ha := (abs_add_le (thirdSignalResidual T x) (logSignalEnergy T x-T*L^2/x^2)).trans
      (add_le_add hthird' hA1)
    have hb := (abs_add_le _ (primeSignalEnergy T x-T*u)).trans (add_le_add ha hA2)
    have hc := (abs_add_le _ (2*(crossIntegral x T).re)).trans (add_le_add hb hm)
    calc
      _ = |thirdSignalResidual T x+(logSignalEnergy T x-T*L^2/x^2)+
          (primeSignalEnergy T x-T*u)+2*(crossIntegral x T).re| := by
            apply congrArg abs
            dsimp only [thirdSignalResidual,S]
            ring
      _ ≤ _ := hc
      _ = K*G := by dsimp only [K]; ring
  have hiden : sharpFormFactor T (u/Real.log T) / mesoscopicMain T u - 1 =
      (2*Real.pi*(actualComplexPairSum T (Real.log x)).re-T*S)/(T*S) := by
    rw [sharpFormFactor_eq_actualComplexPairSum, div_mul_cancel₀ _ hL.ne', hxu]
    change (actualComplexPairSum T u).re / (T*L/(2*Real.pi)) / (S/L) - 1 = _
    field_simp [hS.ne', hT0.ne', hL.ne', Real.pi_ne_zero]
    <;> ring
  rw [hiden, abs_div, abs_of_pos (mul_pos hT0 hS)]
  exact (div_le_div_of_nonneg_right hsum (mul_pos hT0 hS).le).trans_eq
    (by dsimp [G]; field_simp [hT0.ne',hS.ne',hU.ne'])

/-- The relative complex asymptotic needs the component estimates and their
half-logarithmic frequency range. -/
theorem sharp_mesoscopic_combined_asymptotic (hthird : PositiveCutoffThirdSignalSource)
    (hprime : QuadraticPrimeSignalMeanSquareSource) (u : ℝ → ℝ) (hu : Tendsto u atTop atTop)
    (hband : ∀ᶠ T : ℝ in atTop, u T ≤ Real.log T/2) :
    Tendsto (fun T => sharpFormFactor T (u T/Real.log T) / mesoscopicMain T (u T))
      atTop (𝓝 1) := by
  obtain ⟨K,_,hb⟩ := sharp_mesoscopic_relative_bound hthird hprime
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (.of_forall fun _ => norm_nonneg _) _ (hu.const_div_atTop K)
  filter_upwards [hb,hu.eventually_ge_atTop 1,hband] with T hT hU hbT
  rw [Real.norm_eq_abs]
  exact hT _ hU hbT

/-- The combined main term survives the reflected quartic comparison. -/
theorem raw_mesoscopic_combined_asymptotic {a : ℝ} (ha : 0 < a) (hQ : ReflectedQuarticDefectEstimate a)
    (hthird : PositiveCutoffThirdSignalSource) (hprime : QuadraticPrimeSignalMeanSquareSource)
    (u : ℝ → ℝ) (hu : Tendsto u atTop atTop)
    (hsmall : Tendsto (fun T => (u T)^3/(Real.log T)^2) atTop (𝓝 0)) :
    Tendsto (fun T => formFactor T (u T/Real.log T) / mesoscopicMain T (u T)) atTop (𝓝 1) := by
  have hsharp := sharp_mesoscopic_combined_asymptotic hthird hprime u hu
    ((eventually_mesoscopic_band hu hsmall (by norm_num : 0 < (1/2:ℝ))).mono
      (fun T h => by linarith only [h.2]))
  have hS : ∀ᶠ T : ℝ in atTop, u T/Real.log T ≤ mesoscopicMain T (u T) := by
    filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
    exact div_le_div_of_nonneg_right (le_add_of_nonneg_left (div_nonneg (sq_nonneg _) (sq_nonneg _))) (Real.log_pos hT).le
  apply raw_relative_asymptotic_of_defect _ _ _ hsharp
    (mesoscopic_defect_relative ha hQ u _ hu hsmall hS)
  filter_upwards [hS, hu.eventually_gt_atTop 0, eventually_gt_atTop (1:ℝ)] with T hT hU hT1
  exact (div_pos hU (Real.log_pos hT1)).trans_le hT

/-- A finite limit of the spike divided by the linear term contributes its
full coefficient to a combined asymptotic. -/
theorem raw_spike_ratio_of_combined {r : ℝ} {u : ℝ → ℝ} (hu : Tendsto u atTop atTop)
    (hraw : Tendsto (fun T => formFactor T (u T/Real.log T) / mesoscopicMain T (u T)) atTop (𝓝 1))
    (hspike : Tendsto (fun T => (Real.log T)^2/(Real.exp (u T))^2/(u T)) atTop (𝓝 r)) :
    Tendsto (fun T => formFactor T (u T/Real.log T) / (u T/Real.log T)) atTop (𝓝 (r+1)) := by
  have hratio : Tendsto (fun T => mesoscopicMain T (u T)/(u T/Real.log T)) atTop (𝓝 (r+1)) := by
    have h := hspike.add_const 1
    apply h.congr'
    filter_upwards [hu.eventually_gt_atTop 0, eventually_gt_atTop (1:ℝ)] with T hU hT
    dsimp only [mesoscopicMain]
    field_simp [hU.ne', (Real.log_pos hT).ne', (Real.exp_pos _).ne']
    <;> ring
  have h := hraw.mul hratio
  rw [one_mul] at h
  apply h.congr'
  filter_upwards [hu.eventually_gt_atTop 0, eventually_gt_atTop (1:ℝ)] with T hU hT
  have hmain : 0 < mesoscopicMain T (u T) := by
    unfold mesoscopicMain
    exact div_pos (by positivity) (Real.log_pos hT)
  field_simp [hmain.ne', hU.ne', (Real.log_pos hT).ne']

theorem raw_mesoscopic_spike_ratio {r a : ℝ} (ha : 0 < a) (hQ : ReflectedQuarticDefectEstimate a)
    (hthird : PositiveCutoffThirdSignalSource) (hprime : QuadraticPrimeSignalMeanSquareSource)
    (u : ℝ → ℝ) (hu : Tendsto u atTop atTop)
    (hsmall : Tendsto (fun T => (u T)^3/(Real.log T)^2) atTop (𝓝 0))
    (hspike : Tendsto (fun T => (Real.log T)^2/(Real.exp (u T))^2/(u T)) atTop (𝓝 r)) :
    Tendsto (fun T => formFactor T (u T/Real.log T) / (u T/Real.log T)) atTop (𝓝 (r+1)) :=
  raw_spike_ratio_of_combined hu (raw_mesoscopic_combined_asymptotic ha hQ hthird hprime u hu hsmall) hspike

/-- Unit slope throughout the spike-negligible mesoscopic range. -/
theorem raw_mesoscopic_unit_slope {a : ℝ} (ha : 0 < a) (hQ : ReflectedQuarticDefectEstimate a)
    (hthird : PositiveCutoffThirdSignalSource) (hprime : QuadraticPrimeSignalMeanSquareSource)
    (u : ℝ → ℝ) (hu : Tendsto u atTop atTop)
    (hsmall : Tendsto (fun T => (u T)^3/(Real.log T)^2) atTop (𝓝 0))
    (hspike : Tendsto (fun T => (Real.log T)^2/(Real.exp (u T))^2/(u T)) atTop (𝓝 0)) :
    Tendsto (fun T => formFactor T (u T/Real.log T) / (u T/Real.log T)) atTop (𝓝 1) := by
  simpa only [zero_add] using raw_mesoscopic_spike_ratio ha hQ hthird hprime u hu hsmall hspike

end RiemannResearch.Analysis.MontgomeryHorizontalBessel
