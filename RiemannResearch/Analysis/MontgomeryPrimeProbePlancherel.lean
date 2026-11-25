import RiemannResearch.Analysis.MontgomeryPrimeProbeEnergy
import RiemannResearch.Analysis.FourierL1L2Plancherel

/-! # Fourier energy of the Mertens remainder

Plancherel controls the error on a growing interval of unfolded widths.
-/

noncomputable section
namespace RiemannResearch.Analysis.MontgomeryPrimeTrace
open Filter MeasureTheory Set MontgomeryPositiveGap
open RiemannResearch.RH.Pareto.SpectralObstruction
open scoped Topology
open scoped FourierTransform ENNReal

private def unitBoxTransform (D : ℝ → ℝ) (u : ℝ) : ℂ :=
  ∫ v in (0 : ℝ)..1, (D v : ℂ) * Complex.exp (((2 * Real.pi * u : ℝ) : ℂ) *
    Complex.I * (v : ℂ))

private theorem unitBoxTransform_fourier (D : ℝ → ℝ) (u : ℝ) :
    unitBoxTransform D u =
      𝓕 ((Ioc (0 : ℝ) 1).indicator (fun v => (D v : ℂ))) (-u) := by
  rw [Real.fourier_real_eq_integral_exp_smul, unitBoxTransform,
    intervalIntegral.integral_of_le zero_le_one, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards with v
  by_cases hv : v ∈ Ioc (0 : ℝ) 1
  · simp only [indicator_of_mem hv, smul_eq_mul]
    rw [mul_comm (D v : ℂ)]
    congr 2
    push_cast
    ring
  · simp [hv]

/-- Square-integrating the Fourier transform of a bounded error on the unit
interval costs only its squared L-infinity bound, independently of bandwidth. -/
private theorem unitBoxTransform_energy_le (D : ℝ → ℝ) (hD : Measurable D) {E q : ℝ}
    (hE : ∀ v ∈ Icc (0 : ℝ) 1, |D v| ≤ E) (hq : 0 ≤ q) :
    (∫ u in (0 : ℝ)..q, ‖unitBoxTransform D u‖^2) ≤ E^2 := by
  let b := (Ioc (0 : ℝ) 1).indicator fun v => (D v : ℂ)
  let m := (Ioc (0 : ℝ) 1).indicator fun _ => E
  have hmeas : Measurable b :=
    (Complex.continuous_ofReal.measurable.comp hD).indicator measurableSet_Ioc
  have hdom (v : ℝ) : ‖b v‖ ≤ m v := by
    by_cases hv : v ∈ Ioc (0 : ℝ) 1
    · simpa [b, m, hv, Real.norm_eq_abs] using hE v ⟨hv.1.le, hv.2⟩
    · simp [b, m, hv]
  have hp (p : ENNReal) : MemLp b p := by
    have hm : MemLp m p := by apply memLp_indicator_const p measurableSet_Ioc; exact Or.inr (by simp)
    exact hm.mono' hmeas.aestronglyMeasurable (Eventually.of_forall hdom)
  have hi := memLp_one_iff_integrable.mp (hp 1)
  have h2 := hp 2
  have hf2 : MemLp (𝓕 b) 2 :=
    (Lp.memLp (𝓕 (h2.toLp b) : Lp ℂ 2 (volume : Measure ℝ))).ae_eq
      (RiemannResearch.Analysis.fourier_toLp_ae_eq_of_integrable hi h2)
  have hFi := (memLp_two_iff_integrable_sq_norm hf2.1).mp hf2
  have hB := (memLp_two_iff_integrable_sq_norm h2.1).mp h2
  have hE0 := (abs_nonneg _).trans (hE 0 ⟨le_rfl, zero_le_one⟩)
  have ye : (∫ v, ‖b v‖^2) ≤ E^2 := by
    let y := (Ioc (0 : ℝ) 1).indicator fun _ => E^2
    have hy : Integrable y := memLp_one_iff_integrable.mp (by
      apply memLp_indicator_const 1 measurableSet_Ioc; exact Or.inr (by simp))
    have hle (v : ℝ) : ‖b v‖^2 ≤ y v := by
      by_cases hv : v ∈ Ioc (0 : ℝ) 1
      · simp only [y, indicator_of_mem hv]
        apply (sq_le_sq₀ (norm_nonneg _) hE0).2
        simpa [m, hv] using hdom v
      · simp [b, y, hv]
    have h := integral_mono hB hy hle
    simpa [y, integral_indicator measurableSet_Ioc] using h
  simp_rw [unitBoxTransform_fourier]
  rw [intervalIntegral.integral_comp_neg (fun v : ℝ => ‖𝓕 b v‖^2), neg_zero,
    intervalIntegral.integral_of_le (neg_nonpos.mpr hq)]
  have htotal := RiemannResearch.Analysis.integral_norm_sq_fourier_of_integrable hi h2
  exact (setIntegral_le_integral hFi (Eventually.of_forall fun _ => sq_nonneg _)).trans
    (htotal.trans_le ye)

theorem primeProbe_l2_error {T q : ℝ} (hT : 1 < T) (hq : 0 ≤ q) :
    (∫ u in (0 : ℝ)..q, ‖primeFourierProbe T u - primeContinuumProbe u‖^2) ≤
      2 * ((Real.log 4 + 4) / Real.log T)^2 * (q + (2 * Real.pi * q)^2) := by
  let E := (Real.log 4 + 4) / Real.log T
  let D := fun v => primeLogCDF T v - v
  have hD : Measurable D := (measurable_primeLogCDF hT).sub measurable_id
  have hE (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) : |D v| ≤ E := primeLogCDF_error hT hv.1
  have hpl := unitBoxTransform_energy_le D hD hE hq
  have hpoint (u : ℝ) (hu : u ∈ Icc 0 q) :
      ‖primeFourierProbe T u - primeContinuumProbe u‖^2 ≤
        2 * E^2 + 2 * (2*Real.pi*q)^2 * ‖unitBoxTransform D u‖^2 := by
    rw [primeFourierProbe_sub_eq_cdf hT u]
    have hw : ‖((2 * Real.pi * u : ℝ) : ℂ) * Complex.I‖ = 2 * Real.pi * u := by
      simp [norm_mul, Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_nonneg hu.1]
    have hnorm : ‖Complex.exp (((2 * Real.pi * u : ℝ) : ℂ) * Complex.I)‖ = 1 := by
      simp [Complex.norm_exp]
    apply (pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2).trans
    rw [norm_mul, hnorm, mul_one, Complex.norm_real, Real.norm_eq_abs, norm_mul, hw]
    change (|D 1| + (2 * Real.pi * u) * ‖unitBoxTransform D u‖)^2 ≤ _
    have hlin : |D 1| + (2 * Real.pi * u) * ‖unitBoxTransform D u‖ ≤
        E + (2 * Real.pi * q) * ‖unitBoxTransform D u‖ := by
      apply add_le_add (hE 1 ⟨zero_le_one,le_rfl⟩)
      gcongr; exact hu.2
    apply (pow_le_pow_left₀ (add_nonneg (abs_nonneg _)
      (mul_nonneg (mul_nonneg (by positivity) hu.1) (norm_nonneg _))) hlin 2).trans
    nlinarith only [sq_nonneg (E - (2 * Real.pi * q) * ‖unitBoxTransform D u‖)]
  have hC : Continuous primeContinuumProbe := by
    simpa only [funext primeContinuumProbe_eq, Function.comp_def] using
      (continuous_logPhaseKernel.comp (show Continuous (fun u : ℝ => -(2 * Real.pi * u)) by fun_prop))
  have hP : Continuous (primeFourierProbe T) := by unfold primeFourierProbe; fun_prop
  let b := (Ioc (0 : ℝ) 1).indicator fun v => (D v : ℂ)
  have hb : Integrable b := by
    have hm : Integrable ((Ioc (0 : ℝ) 1).indicator fun _ => E) := by
      apply (integrable_indicator_iff measurableSet_Ioc).2
      exact integrableOn_const (by simp)
    apply hm.mono' (((Complex.continuous_ofReal.measurable.comp hD).indicator
      measurableSet_Ioc).aestronglyMeasurable)
    filter_upwards with v
    by_cases hv : v ∈ Ioc (0 : ℝ) 1
    · simpa [b, hv, Real.norm_eq_abs] using hE v ⟨hv.1.le, hv.2⟩
    · simp [b, hv]
  have hU : Continuous (unitBoxTransform D) := by
    rw [show unitBoxTransform D = fun u => 𝓕 b (-u) from funext (unitBoxTransform_fourier D)]
    exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hb).comp continuous_neg
  have hj : IntervalIntegrable (fun u : ℝ => ‖unitBoxTransform D u‖^2) volume 0 q :=
    (hU.norm.pow 2).intervalIntegrable 0 q
  have h := intervalIntegral.integral_mono_on (μ := volume)
    (f := fun u : ℝ => ‖primeFourierProbe T u - primeContinuumProbe u‖^2)
    (g := fun u : ℝ => 2 * E^2 + 2 * (2 * Real.pi * q)^2 * ‖unitBoxTransform D u‖^2)
    hq (((hP.sub hC).norm.pow 2).intervalIntegrable 0 q)
    ((continuous_const.add (continuous_const.mul (hU.norm.pow 2))).intervalIntegrable 0 q) hpoint
  rw [intervalIntegral.integral_add (f := fun _ : ℝ => 2 * E^2)
      (g := fun u : ℝ => 2 * (2 * Real.pi * q)^2 * ‖unitBoxTransform D u‖^2)
      intervalIntegrable_const (hj.const_mul _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul, sub_zero] at h
  apply h.trans
  calc
    _ ≤ q * (2 * E^2) + 2 * (2 * Real.pi * q)^2 * E^2 :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hpl (by positivity))
    _ = _ := by dsimp [E]; ring

/-- The signed energy error obeys the Cauchy--Schwarz bound with the Fourier
energy of the uniform logarithmic window bounded by one. -/
theorem primeProbeEnergy_plancherel_error {T q : ℝ} (hT : 1 < T) (hq : 0 ≤ q) :
    let V := 2 * ((Real.log 4 + 4) / Real.log T)^2 * (q + (2 * Real.pi * q)^2)
    |primeProbeEnergy T q - (q - sineGapMass q)| ≤ 2 * Real.sqrt V + V := by
  let V := 2 * ((Real.log 4 + 4) / Real.log T)^2 * (q + (2 * Real.pi * q)^2)
  let c := primeContinuumProbe
  let d := fun u => primeFourierProbe T u - c u
  have hc : Continuous c := by
    rw [show c = (fun u => logPhaseKernel (-(2 * Real.pi * u))) from funext primeContinuumProbe_eq]
    exact continuous_logPhaseKernel.comp (by fun_prop)
  have hp : Continuous (primeFourierProbe T) := by unfold primeFourierProbe; fun_prop
  have hd : Continuous d := hp.sub hc
  have hbare := unitBoxTransform_energy_le (fun _ => 1) measurable_const
    (E := 1) (fun _ _ => by norm_num) hq
  have hcbox (u : ℝ) : unitBoxTransform (fun _ => 1) u = c u := by
    simp [c, primeContinuumProbe, unitBoxTransform]
  have hcE : (∫ u in (0 : ℝ)..q, ‖c u‖^2) ≤ 1 := by simpa only [hcbox, one_pow] using hbare
  have hdE : (∫ u in (0 : ℝ)..q, ‖d u‖^2) ≤ V := primeProbe_l2_error hT hq
  let μ := volume.restrict (Ioc (0 : ℝ) q)
  have hp2 (f : ℝ → ℂ) (hf : Continuous f) : MemLp f 2 μ := by
    apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).2
    exact ((hf.norm.pow 2).intervalIntegrable 0 q).1
  have hholder := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (show MemLp c (ENNReal.ofReal (2 : ℝ)) μ by simpa using hp2 c hc)
    (show MemLp d (ENNReal.ofReal (2 : ℝ)) μ by simpa using hp2 d hd)
  have hcs : (∫ u in (0 : ℝ)..q, ‖c u‖ * ‖d u‖) ≤
      Real.sqrt (∫ u in (0 : ℝ)..q, ‖c u‖^2) *
        Real.sqrt (∫ u in (0 : ℝ)..q, ‖d u‖^2) := by
    simpa only [intervalIntegral.integral_of_le hq, Real.rpow_two, ← Real.sqrt_eq_rpow, μ] using hholder
  have hcs' : (∫ u in (0 : ℝ)..q, ‖c u‖ * ‖d u‖) ≤ Real.sqrt V := by
    apply hcs.trans
    calc
      _ ≤ Real.sqrt 1 * Real.sqrt V :=
        mul_le_mul (Real.sqrt_le_sqrt hcE) (Real.sqrt_le_sqrt hdE) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := by simp
  have hpoint (u : ℝ) :
      |‖primeFourierProbe T u‖^2 - Real.sinc (Real.pi*u)^2| ≤ 2 * (‖c u‖ * ‖d u‖) + ‖d u‖^2 := by
    rw [← sq_abs (Real.sinc _), ← norm_primeContinuumProbe_eq]
    change |‖primeFourierProbe T u‖^2-‖c u‖^2| ≤ _
    apply (abs_norm_sq_sub_le _ _).trans
    have hdiff : ‖primeFourierProbe T u‖ ≤ ‖c u‖ + ‖d u‖ := by
      linarith only [(abs_le.mp (abs_norm_sub_norm_le (primeFourierProbe T u) (c u))).2]
    calc
      _ ≤ ‖d u‖ * (2 * ‖c u‖ + ‖d u‖) :=
        mul_le_mul_of_nonneg_left (by linarith only [hdiff]) (norm_nonneg _)
      _ = _ := by ring
  have hi := (((hp.norm.pow 2).sub
    (show Continuous (fun u : ℝ => Real.sinc (Real.pi*u)^2) by fun_prop)).abs).intervalIntegrable (μ := volume) 0 q
  have hprod := (hc.norm.mul hd.norm).intervalIntegrable (μ := volume) 0 q
  have hsq := (hd.norm.pow 2).intervalIntegrable (μ := volume) 0 q
  have hij := intervalIntegral.integral_mono_on hq hi ((hprod.const_mul 2).add hsq) (fun u _ => hpoint u)
  rw [intervalIntegral.integral_add (hprod.const_mul 2) hsq, intervalIntegral.integral_const_mul] at hij
  apply (primeProbeEnergy_error_integral hq).trans
  exact hij.trans (add_le_add (mul_le_mul_of_nonneg_left hcs' (by norm_num)) hdE)

/-- The comparison continues to moving unfolded widths little-o of log T. -/
theorem primeProbeEnergy_moving_sublog (q : ℝ → ℝ) (hq : ∀ᶠ T in atTop, 0 ≤ q T)
    (hsub : Tendsto (fun T : ℝ => q T / Real.log T) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => primeProbeEnergy T (q T) - (q T - sineGapMass (q T))) atTop (𝓝 0) := by
  let C := Real.log 4 + 4
  let V := fun T : ℝ => 2 * (C / Real.log T)^2 * (q T + (2 * Real.pi * q T)^2)
  have hrec := Real.tendsto_log_atTop.const_div_atTop (1 : ℝ)
  have hV : Tendsto V atTop (𝓝 0) := by
    have h := ((hsub.mul hrec).add ((hsub.pow 2).const_mul (4 * Real.pi^2))).const_mul (2*C^2)
    have he (T : ℝ) : (2*C^2) * ((q T / Real.log T)*(1 / Real.log T) +
        4 * Real.pi^2 * (q T / Real.log T)^2) = V T := by dsimp [V]; ring
    simpa only [he, mul_zero, zero_mul, zero_add, zero_pow (by decide : 2≠0)] using h
  have hlim : Tendsto (fun T => 2 * Real.sqrt (V T) + V T) atTop (𝓝 0) := by
    simpa using ((Real.continuous_sqrt.continuousAt.tendsto.comp hV).const_mul 2).add hV
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_gt_atTop (1 : ℝ),hq] with T hT hw
  simpa only [Real.norm_eq_abs] using primeProbeEnergy_plancherel_error hT hw

/--
info: 'RiemannResearch.Analysis.MontgomeryPrimeTrace.primeProbeEnergy_moving_sublog' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms primeProbeEnergy_moving_sublog

end RiemannResearch.Analysis.MontgomeryPrimeTrace
