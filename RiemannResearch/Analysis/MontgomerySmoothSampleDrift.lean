import RiemannResearch.Analysis.MontgomeryClippedDensityTranslation
import RiemannResearch.Analysis.MontgomeryMacroscopicGapLaws
import RiemannResearch.Analysis.MontgomerySampledArgumentError

/-! # Quantitative smooth drift in microscopic and mesoscopic sampled rows

Translation of the cumulative count error brings a factor of the width into
the smooth-model comparison. The resulting relative estimate resolves the
logarithmic smooth drift down to a fixed positive unfolded width.
-/

noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate DyadicZeroWasserstein

private theorem scaled_countMain_eq_model {T : ℝ} (hT : 1 < T) (x : ℝ) :
    countMain (x*T)/unfoldedCutoff T = modelHeightCount (Real.log T) x := by
  have ht := zero_lt_one.trans hT
  have hp : 0 < 2*Real.pi := by positivity
  by_cases hx : x=0
  · simp [hx,countMain,modelHeightCount,heightCountSecondProfile]
  · unfold countMain unfoldedCutoff modelHeightCount heightCountSecondProfile
    rw [Real.log_div (mul_ne_zero hx ht.ne') hp.ne', Real.log_mul hx ht.ne']
    field_simp [ht.ne',(Real.log_pos hT).ne',Real.pi_ne_zero] <;> ring

/-- Exact transposition for the smooth elementary main term sampled at the
genuine zero occurrences. -/
theorem sampled_main_scaled_eq_backward_count {T c : ℝ} (hT : 1 < T) (hc : 0 ≤ c) :
    sampledHeightIncrement countMain T (c*unfoldedCutoff T)/unfoldedCutoff T =
      ∫ u in (0:ℝ)..1, modelHeightDensity (Real.log T) u *
        (scaledHeightCount T u-scaledHeightCount T (max 0 (u-c))) := by
  let D := unfoldedCutoff T
  let L := Real.log T
  let x := fun i : Copies T => copyOrdinate T i/T
  let y := fun i : Copies T => min 1 (x i+c)
  have ht := zero_lt_one.trans hT
  have hL := Real.log_pos hT
  have hphy : c*D/unfoldingScale T = c*T := by
    dsimp only [D,unfoldedCutoff,unfoldingScale]
    field_simp [Real.pi_ne_zero,hL.ne'] <;> ring
  rw [← clipped_height_row_sum_eq_backward_count hT hc (modelHeightDensity_intervalIntegrable L 0 1)]
  unfold sampledHeightIncrement
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  change (countMain (min T (copyOrdinate T i+c*D/unfoldingScale T))-
      countMain (copyOrdinate T i))/D = ∫ u in (x i)..(y i), modelHeightDensity L u
  have hx : x i*T = copyOrdinate T i := div_mul_cancel₀ _ ht.ne'
  have hy : y i*T = min T (copyOrdinate T i+c*T) := by
    dsimp only [y]
    rw [min_mul_of_nonneg _ _ ht.le,one_mul,add_mul,hx]
  rw [hphy,← hy,←hx,sub_div,scaled_countMain_eq_model hT (y i),scaled_countMain_eq_model hT (x i),
    modelHeightCount_sub]

private theorem model_translation_le {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (hc₁ : c < 1) :
    (∫ u in (0:ℝ)..(1-c), |modelHeightDensity L u-modelHeightDensity L (u+c)|) ≤
      c*(1+|Real.log c|)/L := by
  let v := 1-c
  have hv : 0 < v := sub_pos.mpr hc₁
  have hId : (∫ u in (0:ℝ)..v, |modelHeightDensity L u-modelHeightDensity L (u+c)|) =
      ∫ u in (0:ℝ)..v, (Real.log (u+c)-Real.log u)/L := by
    apply intervalIntegral.integral_congr_Ioo_of_le hv.le
    intro u hu
    have hle := Real.log_le_log hu.1 (le_add_of_nonneg_right hc.le)
    have hsg : modelHeightDensity L u-modelHeightDensity L (u+c) ≤ 0 := by
      unfold modelHeightDensity logHeightDensity
      exact sub_nonpos.mpr (add_le_add le_rfl (div_le_div_of_nonneg_right (sub_le_sub_right hle _) hL.le))
    change |modelHeightDensity L u-modelHeightDensity L (u+c)| = (Real.log (u+c)-Real.log u)/L
    rw [abs_of_nonpos hsg]
    dsimp only [modelHeightDensity,logHeightDensity]
    ring
  have hi : IntervalIntegrable (fun u : ℝ => Real.log (u+c)) volume 0 v := by
    simpa only [sub_self,v] using (intervalIntegral.intervalIntegrable_log' (a:=c) (b:=1)).comp_add_right c
  rw [hId,intervalIntegral.integral_div,intervalIntegral.integral_sub hi intervalIntegral.intervalIntegrable_log',
    intervalIntegral.integral_comp_add_right,zero_add,show v+c=1 by dsimp [v]; ring,integral_log,integral_log,
    Real.log_one]
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hv)
  rw [Real.log_inv] at hl
  have hb : -v*Real.log v ≤ c := by
    have h := mul_le_mul_of_nonneg_left hl hv.le
    rw [mul_sub,mul_inv_cancel₀ hv.ne',mul_one] at h
    dsimp only [v] at h ⊢
    linarith only [h]
  have h₀ := mul_le_mul_of_nonneg_left (neg_abs_le (Real.log c)) hc.le
  apply div_le_div_of_nonneg_right _ hL.le
  dsimp only [v] at *
  nlinarith only [hb,h₀]

private theorem model_upper_strip_le {L c : ℝ} (hL : 1 ≤ L) (hc : 0 ≤ c) (hc₂ : c ≤ 1/2) :
    (∫ u in (1-c)..1, |modelHeightDensity L u|) ≤
      c*(1+|Real.log (1/2)|+|Real.log (2*Real.pi)|) := by
  let A := 1+|Real.log (1/2)|+|Real.log (2*Real.pi)|
  have hL₀ : 0 < L := zero_lt_one.trans_le hL
  have h := intervalIntegral.integral_mono_on (μ:=volume) (sub_le_self 1 hc)
    (f := fun u => |modelHeightDensity L u|) (modelHeightDensity_intervalIntegrable L (1-c) 1).abs
    (g := fun _ => A) intervalIntegrable_const (fun u hu => by
      have hu₀ : (1/2:ℝ) ≤ u := by linarith only [hc₂,hu.1]
      have hh := Real.log_le_log (by norm_num : (0:ℝ)<1/2) hu₀
      have hn := Real.log_nonpos ((by norm_num : (0:ℝ)≤1/2).trans hu₀) hu.2
      have hb : |Real.log u| ≤ |Real.log (1/2)| := by
        rw [abs_of_nonpos hn]
        linarith only [hh,neg_abs_le (Real.log (1/2))]
      apply (abs_add_le _ _).trans
      rw [abs_one,abs_div,abs_of_pos hL₀]
      have hd := (div_le_self (abs_nonneg (logHeightDensity u)) hL).trans
        ((abs_sub _ _).trans (add_le_add hb le_rfl))
      dsimp only [A]
      linarith only [hd])
  rw [intervalIntegral.integral_const,smul_eq_mul] at h
  dsimp only [A] at h
  exact h.trans_eq (by ring)

/-- A uniform cumulative estimate for actual heights gives an additional
width factor in the smooth sampled main-term error. -/
theorem smooth_sampled_model_translation_error_le {T c η : ℝ} (hT : 1 < T)
    (hL : 1 ≤ Real.log T) (hc : 0 < c) (hc₂ : c ≤ 1/2)
    (hF : ∀ u ∈ Icc (0:ℝ) 1, |scaledHeightCount T u - modelHeightCount (Real.log T) u| ≤ η) :
    |sampledHeightIncrement countMain T (c*unfoldedCutoff T)/(c*unfoldedCutoff T) -
      macroscopicGapDensityModel (Real.log T) c/c| ≤ η*
      ((1+|Real.log (1/2)|+|Real.log (2*Real.pi)|)+(1+|Real.log c|)/Real.log T) := by
  let L := Real.log T
  let D := unfoldedCutoff T
  let w := modelHeightDensity L
  let G := modelHeightCount L
  let F := scaledHeightCount T
  let E := fun u => F u-G u
  let d := fun u : ℝ => max 0 (u-c)
  have hc₁ : c < 1 := by linarith
  have hD : 0 < D := div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  have hGc : Continuous G := continuous_id.add (continuous_heightCountSecondProfile.div_const L)
  have hdc : Continuous d := continuous_const.max (continuous_id.sub continuous_const)
  have hFm := scaledHeightCount_mono hT
  have hE : Measurable E := hFm.measurable.sub hGc.measurable
  have hDmem {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) : d u ∈ Icc (0:ℝ) 1 :=
    ⟨le_max_left _ _,max_le zero_le_one ((sub_le_self _ hc.le).trans hu.2)⟩
  have hzE : E 0=0 := by
    have hn := cumulative_copy_steps (s:=0) (T:=T) (zero_le_one.trans hT.le)
    have hn' (i : Copies T) : ¬copyOrdinate T i ≤ 0 := not_le.mpr (mem_cutoff.mp i.1.property).2.1
    simp only [hn',ite_false,Finset.sum_const_zero] at hn
    simp only [E,F,G,scaledHeightCount,modelHeightCount,heightCountSecondProfile,zero_mul,hn,
      zero_div,add_zero,sub_zero]
  have hη : 0 ≤ η := (abs_nonneg _).trans (hF 0 ⟨le_rfl,zero_le_one⟩)
  have hw := modelHeightDensity_intervalIntegrable L 0 1
  have hFb (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) : |F u| ≤ F 1 := by
    rw [abs_of_nonneg (show 0 ≤ F u from div_nonneg (Nat.cast_nonneg _) hD.le)]
    exact hFm hu.2
  have hFi : IntervalIntegrable (fun u => w u*(F u-F (d u))) volume 0 1 := by
    simpa only [mul_sub,Function.comp_apply] using
      (intervalIntegrable_bounded_height_multiplier zero_le_one hw hFm.measurable hFb).sub
        (intervalIntegrable_bounded_height_multiplier zero_le_one hw (hFm.measurable.comp hdc.measurable)
          (fun u hu => hFb _ (hDmem hu)))
  have hGi : IntervalIntegrable (fun u => w u*(G u - G (d u))) volume 0 1 :=
    hw.mul_continuousOn (hGc.sub (hGc.comp hdc)).continuousOn
  have hEq : sampledHeightIncrement countMain T (c*D)/D - macroscopicGapDensityModel L c =
      ∫ u in (0:ℝ)..1, w u*(E u-E (d u)) := by
    rw [sampled_main_scaled_eq_backward_count hT hc.le,macroscopicGapDensityModel,
      ←intervalIntegral.integral_sub hFi hGi]
    apply intervalIntegral.integral_congr
    intro u _
    change w u*(F u-F (d u))-w u*(G u-G (d u))=w u*((F u-G u)-(F (d u)-G (d u)))
    ring
  have hbound := backward_clipped_error_translation_le ⟨hc.le,hc₁.le⟩ hw hE hzE hF
  have hi := model_translation_le (Real.log_pos hT) hc hc₁
  have hu := model_upper_strip_le hL hc.le hc₂
  have hcomb := hbound.trans (mul_le_mul_of_nonneg_left (add_le_add hi hu) hη)
  change |sampledHeightIncrement countMain T (c*D)/(c*D) - macroscopicGapDensityModel L c/c| ≤ _
  rw [show sampledHeightIncrement countMain T (c*D)/(c*D) =
    (sampledHeightIncrement countMain T (c*D)/D)/c by ring,← sub_div,hEq,abs_div,abs_of_pos hc]
  apply (div_le_div_of_nonneg_right hcomb hc.le).trans_eq
  field_simp [hc.ne',(Real.log_pos hT).ne'] <;> ring

/-- The normalized smooth sampled main term differs by O(1/T) from the
normalized quadratic density model down to polynomially small fractions
of the cutoff. The bound holds simultaneously across those fractions. -/
theorem eventually_smooth_sampled_model_error {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ c : ℝ, 0 < c → c ≤ 1/2 →
      |Real.log c| ≤ A*Real.log T →
      |sampledHeightIncrement countMain T (c*unfoldedCutoff T)/(c*unfoldedCutoff T) -
        macroscopicGapDensityModel (Real.log T) c/c| ≤ C/T := by
  obtain ⟨K,hK,hF⟩ := eventually_scaledHeightCount_second_profile
  let B := 1+|Real.log (1/2)|+|Real.log (2*Real.pi)|
  refine ⟨K*(B+(1+A)),by dsimp only [B]; positivity,?_⟩
  filter_upwards [hF,eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with T hf hT hL c hc hc₂ hcl
  have h := smooth_sampled_model_translation_error_le hT hL hc hc₂ hf
  apply h.trans
  have hl : (1+|Real.log c|)/Real.log T ≤ 1+A :=
    (div_le_iff₀ (Real.log_pos hT)).mpr (by nlinarith only [hL,hcl])
  exact (mul_le_mul_of_nonneg_left (add_le_add le_rfl hl)
    (div_nonneg hK (zero_le_one.trans hT.le))).trans_eq (by dsimp only [B]; ring)

private theorem eventually_submacroscopic_log_bounds {r : ℝ} {R : ℝ → ℝ} (hr : 0 < r)
    (hR : ∀ᶠ T : ℝ in atTop, r ≤ R T)
    (hs : Tendsto (fun T : ℝ => R T/unfoldedCutoff T) atTop (𝓝 0)) :
    ∀ᶠ T : ℝ in atTop, 0 < R T/unfoldedCutoff T ∧
      R T/unfoldedCutoff T ≤ 1/2 ∧ |Real.log (R T/unfoldedCutoff T)| ≤ 3*Real.log T := by
  filter_upwards [hR,hs.eventually_lt_const (by norm_num : (0:ℝ)<1/2),
    eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop
      (|Real.log r|+|Real.log (2*Real.pi)|)] with T hRr hhalf hT hbig
  have ht := zero_lt_one.trans hT
  have hL := Real.log_pos hT
  have hp : 0 < 2*Real.pi := by positivity
  have hD : 0 < unfoldedCutoff T := div_pos (mul_pos ht hL) hp
  have hc := div_pos (hr.trans_le hRr) hD
  refine ⟨hc,hhalf.le,?_⟩
  have hn := Real.log_nonpos hc.le (hhalf.le.trans (by norm_num))
  rw [abs_of_nonpos hn,Real.log_div (hr.trans_le hRr).ne' hD.ne']
  unfold unfoldedCutoff
  rw [Real.log_div (mul_pos ht hL).ne' hp.ne',Real.log_mul ht.ne' hL.ne']
  linarith only [hbig,Real.log_le_log hr hRr,neg_abs_le (Real.log r),
    neg_abs_le (Real.log (2*Real.pi)),Real.log_le_sub_one_of_pos hL]

/-- At every positive unfolded width bounded below and occupying a
vanishing fraction of the cutoff, the smooth sampled main term has an
unconditional logarithmic correction. This includes every fixed width. -/
theorem smooth_sampled_main_logarithmic_drift {r : ℝ} {R : ℝ → ℝ} (hr : 0 < r)
    (hR : ∀ᶠ T : ℝ in atTop, r ≤ R T)
    (hs : Tendsto (fun T : ℝ => R T/unfoldedCutoff T) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => Real.log T*(sampledHeightIncrement countMain T (R T)/R T -
      (1-R T/(2*unfoldedCutoff T)))) atTop (𝓝 (-2*(1+Real.log (2*Real.pi)))) := by
  let c := fun T => R T/unfoldedCutoff T
  have hb := eventually_submacroscopic_log_bounds hr hR hs
  obtain ⟨C,hC,he⟩ := eventually_smooth_sampled_model_error (by norm_num : (0:ℝ) ≤ 3)
  have hdiff : Tendsto (fun T : ℝ => Real.log T*(sampledHeightIncrement countMain T (R T)/R T -
      macroscopicGapDensityModel (Real.log T) (c T)/c T)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hzero := Real.log_div_self_tendsto_zero.const_mul C
    simp only [mul_zero] at hzero
    apply squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) _ hzero
    filter_upwards [hb,he,eventually_gt_atTop (1:ℝ)] with T hTc hTe hT
    have hL := Real.log_pos hT
    have hD : 0 < unfoldedCutoff T := div_pos (mul_pos (zero_lt_one.trans hT) hL) (by positivity)
    have he' := hTe (c T) hTc.1 hTc.2.1 hTc.2.2
    have hprod : c T*unfoldedCutoff T = R T := div_mul_cancel₀ _ hD.ne'
    rw [hprod] at he'
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos hL]
    exact (mul_le_mul_of_nonneg_left he' hL.le).trans_eq (by ring)
  have hd := hdiff.add (macroscopic_density_model_shrinking_drift (c:=c)
    (hb.mono fun _ h => h.1) hs)
  simp only [zero_add] at hd
  apply hd.congr'
  apply Eventually.of_forall
  intro T
  change Real.log T*(_-_) + Real.log T*(_-(1-c T/2)) = _
  dsimp only [c]
  ring

/-- Below logarithmic width, after retaining the exact signed argument
increment, the residual actual positive-gap statistic still has the
deterministic second-order drift. -/
theorem positiveGapMass_sub_sampledArgument_logarithmic_drift {r : ℝ} {R : ℝ → ℝ}
    (hr : 0 < r) (hR : ∀ᶠ T : ℝ in atTop, r ≤ R T)
    (hs : Tendsto (fun T : ℝ => R T/unfoldedCutoff T) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => Real.log T*((positiveGapMass T (R T)-sampledArgumentIncrement T (R T)) /
      R T-(1-R T/(2*unfoldedCutoff T)))) atTop (𝓝 (-2*(1+Real.log (2*Real.pi)))) := by
  obtain ⟨K,hK,hm⟩ := exists_sampled_argument_error_comparison
  have he : Tendsto (fun T : ℝ => Real.log T*((sampledRvMError T (R T) -
      sampledArgumentIncrement T (R T))/R T)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hu := (tendsto_inv_atTop_zero : Tendsto (fun T : ℝ => T⁻¹) atTop (𝓝 0)).const_mul (2*Real.pi*K)
    simp only [mul_zero] at hu
    apply squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) _ hu
    filter_upwards [hR,eventually_ge_atTop (3:ℝ)] with T hRt hT
    have ht : 1 < T := by linarith
    have hL := Real.log_pos ht
    have hRt' := hr.trans_le hRt
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos hL,abs_div,abs_of_pos hRt']
    apply (mul_le_mul_of_nonneg_left (hm T (R T) hT hRt') hL.le).trans_eq
    dsimp only [unfoldedCutoff]
    field_simp [hL.ne',Real.pi_ne_zero,(zero_lt_one.trans ht).ne'] <;> ring
  have hd := (smooth_sampled_main_logarithmic_drift hr hR hs).add he
  simp only [add_zero] at hd
  apply hd.congr'
  filter_upwards [hR,eventually_gt_atTop (1:ℝ)] with T hRt hT
  rw [positiveGapMass_eq_sampled_main_add_RvMError hT (hr.trans_le hRt)]
  ring

end RiemannResearch.Analysis.MontgomeryPositiveGap

namespace RiemannResearch.Analysis.MontgomeryPositiveGap

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.positiveGapMass_sub_sampledArgument_logarithmic_drift' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms positiveGapMass_sub_sampledArgument_logarithmic_drift

end RiemannResearch.Analysis.MontgomeryPositiveGap
