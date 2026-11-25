import RiemannResearch.Analysis.MontgomeryPrimeProbeSharpWidths
import RiemannResearch.Analysis.MontgomeryIntegratedGapDensity
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Cesàro width averages of the prime energy

The width convention is the one used in Goldston, Lee, Schettler and
Suriajaya, *Pair Correlation Conjecture for the zeros of the Riemann zeta-function I*,
§6 (https://arxiv.org/abs/2503.15449). Here the statistic is arithmetic:
its critical and supercritical slopes follow from the M17 prime log-spectrum
estimates and interval dominated convergence, without hypotheses on zeta zeros.
-/

noncomputable section
open Filter MeasureTheory Set intervalIntegral
open scoped Topology

namespace RiemannResearch.Analysis.MontgomeryPrimeTrace
open MontgomeryPositiveGap

/-- The arithmetic energy averaged twice over a forward window. -/
def primeProbeCesaroEnergy (T R : ℝ) : ℝ :=
  (2/R) * ∫ q in (0 : ℝ)..R, primeProbeEnergy T q

theorem continuous_primeProbeEnergy_width (T : ℝ) : Continuous (primeProbeEnergy T) := by
  unfold primeProbeEnergy
  apply continuous_primitive
  intro a b
  have hc : Continuous (primeFourierProbe T) := by unfold primeFourierProbe; fun_prop
  exact (hc.norm.pow 2).intervalIntegrable a b

theorem monotone_primeProbeEnergy_width (T : ℝ) : Monotone (primeProbeEnergy T) := by
  intro a b hab
  have hc : Continuous (primeFourierProbe T) := by unfold primeFourierProbe; fun_prop
  have hi (a b : ℝ) : IntervalIntegrable (fun x : ℝ => ‖primeFourierProbe T x‖ ^ 2) volume a b :=
    (hc.norm.pow 2).intervalIntegrable a b
  rw [primeProbeEnergy, primeProbeEnergy,
    ← intervalIntegral.integral_add_adjacent_intervals (hi 0 a) (hi a b)]
  exact le_add_of_nonneg_right (intervalIntegral.integral_nonneg hab fun _ _ => sq_nonneg _)

private theorem energy_nonneg (T : ℝ) {q : ℝ} (hq : 0 ≤ q) : 0 ≤ primeProbeEnergy T q :=
  intervalIntegral.integral_nonneg hq fun _ _ => sq_nonneg _

theorem primeProbeCesaroEnergy_rescale (T : ℝ) {R : ℝ} (hR : R ≠ 0) :
    primeProbeCesaroEnergy T R = 2 * ∫ x in (0 : ℝ)..1, primeProbeEnergy T (R*x) := by
  rw [primeProbeCesaroEnergy,intervalIntegral.integral_comp_mul_left _ hR,
    mul_zero, mul_one, smul_eq_mul, div_eq_mul_inv, mul_assoc]

private theorem energy_upper :
    ∃ K > (0 : ℝ), ∀ {T q : ℝ}, 1 < T → 2 ≤ Real.log T → 0 ≤ q →
      primeProbeEnergy T q ≤ 1/2+K*(1/Real.log T+q/(Real.log T)^2) := by
  obtain ⟨K,hK,h⟩ := primeProbeEnergyExcess_uniform
  refine ⟨K,hK,fun {T q} ht hL hq => ?_⟩
  have he := (le_abs_self (primeProbeEnergyExcess T q)).trans (h ht hL hq)
  unfold primeProbeEnergyExcess at he
  linarith [sineGapMass_lower hq]

/-- At every diverging width the prime probe is negligible relative to the width. -/
theorem primeProbeEnergy_div_width_tendsto {R : ℝ → ℝ} (hR : Tendsto R atTop atTop) :
    Tendsto (fun T => primeProbeEnergy T (R T)/R T) atTop (𝓝 0) := by
  obtain ⟨K,hK,h⟩ := energy_upper
  have hsmall : Tendsto (fun T : ℝ => (1/2+K)/(R T) + K/(Real.log T)^2) atTop (𝓝 0) := by
    simpa only [pow_two,add_zero] using (hR.const_div_atTop (1/2+K)).add
      ((Real.tendsto_log_atTop.atTop_mul_atTop₀ Real.tendsto_log_atTop).const_div_atTop K)
  apply squeeze_zero' _ _ hsmall
  · filter_upwards [hR.eventually_gt_atTop 0] with T hRT
    exact div_nonneg (energy_nonneg _ hRT.le) hRT.le
  · filter_upwards [hR.eventually_gt_atTop 0,eventually_gt_atTop (1:ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop 2] with T hRT hT hL
    have hlog : 0 < Real.log T := Real.log_pos hT
    have hlo : 1/Real.log T ≤ 1 := (div_le_one hlog).2 (by linarith)
    apply (div_le_iff₀ hRT).2
    calc
      _ ≤ 1/2+K*(1/Real.log T+R T/(Real.log T)^2) := h hT hL hRT.le
      _ ≤ 1/2+K*(1+R T/(Real.log T)^2) := by gcongr
      _ = ((1/2+K)/R T+K/(Real.log T)^2)*R T := by field_simp; ring

private theorem energy_finite_profile {R : ℝ → ℝ} {α : ℝ}
    (hR : Tendsto R atTop atTop)
    (hα : Tendsto (fun T : ℝ => R T/(Real.log T)^2) atTop (𝓝 α)) :
    Tendsto (fun T : ℝ => primeProbeEnergy T (R T)) atTop (𝓝 (1/2+α*primeProbeDiagonal)) := by
  have hr := (hR.eventually_gt_atTop 0).mono fun T h => h.le
  have hz : 0 ≤ α := ge_of_tendsto hα (hr.mono fun T h => div_nonneg h (sq_nonneg _))
  have hE : Tendsto (fun T => primeProbeEnergyExcess T (R T)) atTop (𝓝 (α*primeProbeDiagonal)) := by
    rcases hz.eq_or_lt with rfl | hpos
    · simpa using primeProbeEnergy_moving_sublog_sq hr hα
    · exact primeProbeEnergyExcess_critical hpos hα
  have hs := sineGapMass_sub_id_tendsto_neg_half.comp hR
  have ha := hE.sub hs
  rw [show α*primeProbeDiagonal-(-(1/2 : ℝ)) = 1/2+α*primeProbeDiagonal by ring] at ha
  apply ha.congr'
  filter_upwards with T
  change primeProbeEnergyExcess T (R T) - (sineGapMass (R T)-R T) = _
  unfold primeProbeEnergyExcess
  ring

private theorem profile_integral (b m : ℝ) :
    2 * (∫ x in (0 : ℝ)..1, b+x*m) = 2*b+m := by
  have h1 : IntervalIntegrable (fun _ : ℝ => b) volume 0 1 := intervalIntegrable_const
  have h2 : IntervalIntegrable (fun x : ℝ => x*m) volume 0 1 :=
    (continuous_id.mul_const m).intervalIntegrable _ _
  rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const,
    intervalIntegral.integral_mul_const, integral_id]
  simp only [sub_zero, smul_eq_mul, one_mul]
  ring

private theorem average_profile {f : ℝ → ℝ → ℝ} {b m : ℝ}
    (hc : ∀ T, Continuous (f T))
    (hn : ∀ᶠ T : ℝ in atTop, ∀ x : ℝ, 0 ≤ x → 0 ≤ f T x)
    (hm : ∀ᶠ T : ℝ in atTop, Monotone (f T))
    (hp : ∀ x : ℝ, 0 < x → x ≤ 1 →
      Tendsto (fun T : ℝ => f T x) atTop (𝓝 (b+x*m))) :
    Tendsto (fun T : ℝ => 2 * ∫ x in (0:ℝ)..1, f T x) atTop (𝓝 (2*b+m)) := by
  have hbound := (hp 1 zero_lt_one le_rfl).eventually
    (gt_mem_nhds (show b+1*m < b+1*m+1 by linarith))
  have hI : Tendsto (fun T => ∫ x in (0 : ℝ)..1, f T x) atTop
      (𝓝 (∫ x in (0 : ℝ)..1, b+x*m)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => b+1*m+1)
    · exact Eventually.of_forall fun T => (hc T).aestronglyMeasurable
    · filter_upwards [hn,hm,hbound] with T hnn hmon hb
      apply Eventually.of_forall
      intro x hx
      rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
      rw [Real.norm_eq_abs,abs_of_nonneg (hnn x hx.1.le)]
      exact (hmon hx.2).trans hb.le
    · exact intervalIntegrable_const
    · apply Eventually.of_forall
      intro x hx
      rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
      exact hp x hx.1 hx.2
  simpa only [profile_integral] using hI.const_mul 2

/-- For all finite scaled widths, including the origin, averaging retains
the M17 coefficient with the pair-correlation convention 2/R. -/
theorem primeProbeCesaroEnergy_critical {R : ℝ → ℝ} {α : ℝ} (hR : Tendsto R atTop atTop)
    (hα : Tendsto (fun T : ℝ => R T/(Real.log T)^2) atTop (𝓝 α)) :
    Tendsto (fun T : ℝ => primeProbeCesaroEnergy T (R T)) atTop (𝓝 (1+α*primeProbeDiagonal)) := by
  let f := fun (T x : ℝ) => primeProbeEnergy T (R T*x)
  have hc (T : ℝ) : Continuous (f T) :=
    (continuous_primeProbeEnergy_width T).comp (continuous_const.mul continuous_id)
  have hn := (hR.eventually_gt_atTop 0).mono fun T hT (x : ℝ) (hx : 0 ≤ x) =>
    energy_nonneg T (mul_nonneg hT.le hx)
  have hm : ∀ᶠ T : ℝ in atTop, Monotone (f T) := by
    filter_upwards [hR.eventually_gt_atTop 0] with T hT
    exact fun x y hxy => monotone_primeProbeEnergy_width T (mul_le_mul_of_nonneg_left hxy hT.le)
  have hp (x : ℝ) (hx : 0 < x) (_ : x ≤ 1) :
      Tendsto (fun T : ℝ => f T x) atTop (𝓝 (1/2+x*(α*primeProbeDiagonal))) := by
    have hRx : Tendsto (fun T => R T*x) atTop atTop := hR.atTop_mul_const hx
    have hax : Tendsto (fun T : ℝ => (R T*x)/(Real.log T)^2) atTop (𝓝 (α*x)) := by
      apply (hα.mul_const x).congr'
      filter_upwards with T
      ring
    simpa only [f,show α*x*primeProbeDiagonal=x*(α*primeProbeDiagonal) by ring]
      using energy_finite_profile hRx hax
  have h := average_profile hc hn hm hp
  rw [show 2*(1/2 : ℝ) = 1 by ring] at h
  apply h.congr'
  filter_upwards [hR.eventually_gt_atTop 0] with T ht
  exact (primeProbeCesaroEnergy_rescale T ht.ne').symm

/-- Averaging also preserves the leading diagonal in the supercritical range. -/
theorem primeProbeCesaroEnergy_supercritical {R : ℝ → ℝ}
    (hR : Tendsto R atTop atTop)
    (hs : Tendsto (fun T : ℝ => R T/(Real.log T)^2) atTop atTop) :
    Tendsto (fun T : ℝ => primeProbeCesaroEnergy T (R T)/(R T/(Real.log T)^2))
      atTop (𝓝 primeProbeDiagonal) := by
  let s := fun T : ℝ => R T/(Real.log T)^2
  let f := fun (T x : ℝ) => primeProbeEnergy T (R T*x)/s T
  have hc (T : ℝ) : Continuous (f T) :=
    ((continuous_primeProbeEnergy_width T).comp (continuous_const.mul continuous_id)).div_const _
  have hn : ∀ᶠ T : ℝ in atTop, ∀ x : ℝ, 0 ≤ x → 0 ≤ f T x := by
    filter_upwards [hR.eventually_gt_atTop 0,hs.eventually_gt_atTop 0] with T hT hsT
    exact fun x hx => div_nonneg (energy_nonneg _ (mul_nonneg hT.le hx)) hsT.le
  have hm : ∀ᶠ T : ℝ in atTop, Monotone (f T) := by
    filter_upwards [hR.eventually_gt_atTop 0,hs.eventually_gt_atTop 0] with T hT hsT
    exact fun x y hxy => div_le_div_of_nonneg_right
      (monotone_primeProbeEnergy_width T (mul_le_mul_of_nonneg_left hxy hT.le)) hsT.le
  have hL : Tendsto (fun T : ℝ => R T/Real.log T) atTop atTop := by
    apply (hs.atTop_mul_atTop₀ Real.tendsto_log_atTop).congr'
    filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
    field_simp [(Real.log_pos hT).ne']
  have hp (x : ℝ) (hx : 0 < x) (_ : x ≤ 1) :
      Tendsto (fun T : ℝ => f T x) atTop (𝓝 ((0:ℝ)+x*primeProbeDiagonal)) := by
    have hRx : Tendsto (fun T => R T*x) atTop atTop := hR.atTop_mul_const hx
    have hband : Tendsto (fun T : ℝ => R T*x/Real.log T) atTop atTop := by
      apply (hL.atTop_mul_const hx).congr'
      filter_upwards with T
      ring
    have hE := (primeProbeEnergyExcess_superlog _ hband).const_mul x
    have hmodel := (sineGapMass_sub_id_tendsto_neg_half.comp hRx).mul
      (tendsto_inv_atTop_zero.comp hs)
    have hv := hE.sub hmodel
    simp only [mul_zero,sub_zero] at hv
    rw [zero_add]
    apply hv.congr'
    filter_upwards [hR.eventually_gt_atTop 0,eventually_gt_atTop (1:ℝ)] with T ht hT
    change x*(primeProbeEnergyExcess T (R T*x)/(R T*x/(Real.log T)^2)) -
      ((sineGapMass (R T*x)-R T*x)*(R T/(Real.log T)^2)⁻¹) = f T x
    unfold primeProbeEnergyExcess
    dsimp only [f,s]
    field_simp [hx.ne',ht.ne',(Real.log_pos hT).ne']
    ring
  have h := average_profile hc hn hm hp
  simp only [mul_zero,zero_add] at h
  apply h.congr'
  filter_upwards [hR.eventually_gt_atTop 0] with T hT
  dsimp only [f,s]
  rw [primeProbeCesaroEnergy_rescale T hT.ne', intervalIntegral.integral_div]
  ring

/-- info: 'RiemannResearch.Analysis.MontgomeryPrimeTrace.primeProbeCesaroEnergy_critical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms primeProbeCesaroEnergy_critical

/-- info: 'RiemannResearch.Analysis.MontgomeryPrimeTrace.primeProbeCesaroEnergy_supercritical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms primeProbeCesaroEnergy_supercritical

end RiemannResearch.Analysis.MontgomeryPrimeTrace
