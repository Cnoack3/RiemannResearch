import RiemannResearch.Analysis.MontgomeryPrimeLogFourier
import RiemannResearch.Analysis.MontgomerySampledArgumentError
import RiemannResearch.Analysis.MontgomeryOrdinateIntervalUpper
import RiemannResearch.RH.ParetoResidueMicroscopicGram
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Square energy of the prescribed logarithmic prime probe

The sinc comparison uses the Mertens estimate. The equivalence samples
the right-continuous discrepancy at each actual zero occurrence.
Source: user-provided prime–zero comparison.
-/

noncomputable section
namespace RiemannResearch.Analysis.MontgomeryPrimeTrace
open Filter MeasureTheory Set MontgomeryPositiveGap
open RiemannResearch.RH.Pareto.SpectralObstruction
open scoped Topology

theorem primeContinuumProbe_eq (u : ℝ) :
    primeContinuumProbe u = logPhaseKernel (-(2 * Real.pi * u)) := by
  let w : ℝ := 2 * Real.pi * u
  change (∫ v : ℝ in (0 : ℝ)..1, Complex.exp (((w : ℂ) * Complex.I) * (v : ℂ))) =
    logPhaseKernel (-w)
  by_cases hw : w = 0
  · simp [hw]
  · have hz : (w : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr hw) Complex.I_ne_zero
    rw [integral_exp_mul_complex hz]
    simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, Complex.exp_zero]
    apply (div_eq_iff hz).2
    have hk := mul_logPhaseKernel (-w)
    simp only [Complex.ofReal_neg, neg_neg, neg_mul] at hk
    linear_combination hk

theorem norm_primeContinuumProbe_eq (u : ℝ) :
    ‖primeContinuumProbe u‖ = |Real.sinc (Real.pi * u)| := by
  rw [primeContinuumProbe_eq, norm_logPhaseKernel,
    show -(2 * Real.pi * u) / 2 = -(Real.pi * u) by ring, Real.sinc_neg]

theorem primeSineHoleMass_eq (q : ℝ) :
    (∫ u in (0 : ℝ)..q, Real.sinc (Real.pi * u) ^ 2) = q - sineGapMass q := by
  have hc : Continuous (fun u : ℝ => Real.sinc (Real.pi * u) ^ 2) := by fun_prop
  rw [sineGapMass, intervalIntegral.integral_sub intervalIntegrable_const
    (hc.intervalIntegrable 0 q), intervalIntegral.integral_const]
  simp [smul_eq_mul]

def primeProbeEnergy (T q : ℝ) : ℝ := ∫ u in (0 : ℝ)..q, ‖primeFourierProbe T u‖ ^ 2

private theorem continuous_primeProbeEnergyIntegrand (T : ℝ) :
    Continuous (fun u : ℝ => ‖primeFourierProbe T u‖ ^ 2) := by
  unfold primeFourierProbe
  fun_prop

theorem abs_norm_sq_sub_le (z w : ℂ) :
    |‖z‖ ^ 2 - ‖w‖ ^ 2| ≤ ‖z-w‖ * (‖z‖ + ‖w‖) := by
  rw [show ‖z‖ ^ 2 - ‖w‖ ^ 2 = (‖z‖ - ‖w‖) * (‖z‖ + ‖w‖) by ring,
    abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le _ _) (by positivity)

theorem primeProbeEnergy_error_integral {T q : ℝ} (hq : 0 ≤ q) :
    |primeProbeEnergy T q - (q - sineGapMass q)| ≤
      ∫ u in (0 : ℝ)..q, |‖primeFourierProbe T u‖ ^ 2 - Real.sinc (Real.pi * u) ^ 2| := by
  have hc : Continuous (fun u : ℝ => Real.sinc (Real.pi * u) ^ 2) := by fun_prop
  rw [primeProbeEnergy, ← primeSineHoleMass_eq,
    ← intervalIntegral.integral_sub ((continuous_primeProbeEnergyIntegrand T).intervalIntegrable 0 q)
      (hc.intervalIntegrable 0 q)]
  exact intervalIntegral.abs_integral_le_integral_abs hq

/-- The finite arithmetic comparison converges at an explicit rate for every width. -/
theorem primeProbeEnergy_error {T q : ℝ} (hT : 1 < T) (hq : 0 ≤ q) :
    |primeProbeEnergy T q - (q - sineGapMass q)| ≤
      ((Real.log 4 + 4) / Real.log T) * (2 + (Real.log 4 + 4) / Real.log T) *
        (q + Real.pi * q ^ 2) := by
  let e : ℝ := (Real.log 4 + 4) / Real.log T
  have he : 0 ≤ e := div_nonneg (by positivity) (Real.log_pos hT).le
  have hc : Continuous (fun u : ℝ => Real.sinc (Real.pi * u) ^ 2) := by fun_prop
  have hi := ((continuous_primeProbeEnergyIntegrand T).sub hc).abs.intervalIntegrable (μ := volume) 0 q
  have hj : Continuous (fun u : ℝ => (e * (2 + e)) * (1 + 2 * Real.pi * u)) := by fun_prop
  have hb (u : ℝ) (hu : u ∈ Icc 0 q) :
      |‖primeFourierProbe T u‖ ^ 2 - Real.sinc (Real.pi * u) ^ 2| ≤
        (e * (2 + e)) * (1 + 2 * Real.pi * u) := by
    have hu0 : 0 ≤ u := hu.1
    have hm : ‖primeContinuumProbe u‖ ^ 2 = Real.sinc (Real.pi * u) ^ 2 := by
      rw [norm_primeContinuumProbe_eq, sq_abs]
    rw [← hm]
    have hd := primeFourierProbe_error hT u
    rw [abs_of_nonneg hu.1] at hd
    have hs : ‖primeFourierProbe T u‖ + ‖primeContinuumProbe u‖ ≤ 2 + e := by
      rw [norm_primeContinuumProbe_eq]
      linarith only [norm_primeFourierProbe_le hT u, Real.abs_sinc_le_one (Real.pi * u)]
    calc
      _ ≤ _ := abs_norm_sq_sub_le _ _
      _ ≤ (e * (1 + 2 * Real.pi * u)) * (2 + e) :=
        mul_le_mul hd hs (by positivity) (mul_nonneg he (by positivity))
      _ = _ := by ring
  apply (primeProbeEnergy_error_integral hq).trans
  calc
    _ ≤ _ := intervalIntegral.integral_mono_on hq hi (hj.intervalIntegrable 0 q) hb
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add intervalIntegrable_const
          ((show Continuous (fun u : ℝ => 2 * Real.pi * u) by fun_prop).intervalIntegrable 0 q),
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
      dsimp [e]
      simp only [smul_eq_mul, sub_zero, mul_one, zero_pow (by decide : 2 ≠ 0)]
      ring

theorem primeProbeEnergy_tendsto {q : ℝ} (hq : 0 ≤ q) :
    Tendsto (fun T : ℝ => primeProbeEnergy T q) atTop (𝓝 (q - sineGapMass q)) := by
  have he := Real.tendsto_log_atTop.const_div_atTop (Real.log 4 + 4)
  have hz : Tendsto (fun T : ℝ => ((Real.log 4 + 4) / Real.log T) *
      (2 + (Real.log 4 + 4) / Real.log T) * (q + Real.pi * q ^ 2)) atTop (𝓝 0) := by
    simpa using (he.mul (tendsto_const_nhds.add he)).mul_const (q + Real.pi * q ^ 2)
  apply tendsto_sub_nhds_zero_iff.mp
  apply squeeze_zero_norm' _ hz
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  simpa only [Real.norm_eq_abs] using primeProbeEnergy_error hT hq

private theorem sinc_linear_weight_le (u : ℝ) :
    |Real.sinc (Real.pi * u)| * (1 + 2 * Real.pi * |u|) ≤ 3 := by
  have hsin : |Real.sinc (Real.pi * u)| * (Real.pi * |u|) ≤ 1 := by
    by_cases hx : Real.pi * u = 0
    · have hu : u = 0 := (mul_eq_zero.mp hx).resolve_left Real.pi_ne_zero
      simp [hu]
    · rw [show Real.pi * |u| = |Real.pi * u| by rw [abs_mul, abs_of_pos Real.pi_pos],
        Real.sinc_of_ne_zero hx, abs_div, div_mul_cancel₀ _ (abs_ne_zero.mpr hx)]
      exact Real.abs_sin_le_one _
  linarith only [Real.abs_sinc_le_one (Real.pi * u), hsin]

/-- This bound uses the decay of the comparison transform. It tends to zero
for moving widths q = o((log T)^(2/3)). -/
theorem primeProbeEnergy_decay_error {T q : ℝ} (hT : 1 < T) (hq : 0 ≤ q) :
    |primeProbeEnergy T q - (q - sineGapMass q)| ≤
      q * (6 * ((Real.log 4 + 4) / Real.log T) +
        (((Real.log 4 + 4) / Real.log T) * (1 + 2 * Real.pi * q)) ^ 2) := by
  let e : ℝ := (Real.log 4 + 4) / Real.log T
  have he : 0 ≤ e := div_nonneg (by positivity) (Real.log_pos hT).le
  let D : ℝ := e * (1 + 2 * Real.pi * q)
  have hc : Continuous (fun u : ℝ => Real.sinc (Real.pi * u) ^ 2) := by fun_prop
  have hi := ((continuous_primeProbeEnergyIntegrand T).sub hc).abs.intervalIntegrable (μ := volume) 0 q
  have hb (u : ℝ) (hu : u ∈ Icc 0 q) :
      |‖primeFourierProbe T u‖ ^ 2 - Real.sinc (Real.pi * u) ^ 2| ≤ 6 * e + D ^ 2 := by
    have hu0 : 0 ≤ u := hu.1
    let d : ℝ := e * (1 + 2 * Real.pi * u)
    have hd : ‖primeFourierProbe T u - primeContinuumProbe u‖ ≤ d := by
      simpa [d, e, abs_of_nonneg hu.1] using primeFourierProbe_error hT u
    have hd0 : 0 ≤ d := (norm_nonneg _).trans hd
    have hdD : d ≤ D := by
      dsimp only [d, D]
      exact mul_le_mul_of_nonneg_left (by gcongr; exact hu.2) he
    have hdn : ‖primeFourierProbe T u‖ ≤ ‖primeContinuumProbe u‖ + d := by
      linarith only [(abs_le.mp ((abs_norm_sub_norm_le _ _).trans hd)).2]
    have hprod : |Real.sinc (Real.pi * u)| * (1 + 2 * Real.pi * u) ≤ 3 := by
      simpa only [abs_of_nonneg hu.1] using sinc_linear_weight_le u
    have ham : d * ‖primeContinuumProbe u‖ ≤ 3 * e := by
      rw [norm_primeContinuumProbe_eq]
      calc
        _ = (|Real.sinc (Real.pi * u)| * (1 + 2 * Real.pi * u)) * e := by dsimp [d]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hprod he
    have hsquare : d ^ 2 ≤ D ^ 2 := (sq_le_sq₀ hd0 (hd0.trans hdD)).2 hdD
    rw [← sq_abs (Real.sinc (Real.pi * u)), ← norm_primeContinuumProbe_eq]
    apply (abs_norm_sq_sub_le _ _).trans
    calc
      _ ≤ d * (2 * ‖primeContinuumProbe u‖ + d) :=
        mul_le_mul hd (by linarith only [hdn]) (by positivity) hd0
      _ ≤ _ := by nlinarith only [ham, hsquare]
  apply (primeProbeEnergy_error_integral hq).trans
  have hh := intervalIntegral.integral_mono_on (μ := volume)
    (f := fun u : ℝ => |‖primeFourierProbe T u‖ ^ 2 - Real.sinc (Real.pi * u) ^ 2|)
    (g := fun _ : ℝ => 6 * e + D ^ 2) hq hi intervalIntegrable_const hb
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, Pi.sub_apply, D, e] using hh

/-- A single signed trace error at positive rational widths characterizes
the actual positive-gap law, with the arithmetic side completely discharged. -/
theorem positiveGapPCC_iff_primeProbeTrace :
    PositiveGapPCC ↔ ∀ q : ℚ, 0 < q → Tendsto (fun T : ℝ =>
      sampledArgumentIncrement T q + primeProbeEnergy T q) atTop (𝓝 0) := by
  rw [positiveGapPCC_iff_rationalSampledArgumentIncrement]
  constructor
  · intro h q hq
    have hb := primeProbeEnergy_tendsto (q := (q : ℝ)) (by exact_mod_cast hq.le)
    have hz := (h q hq).add hb
    rw [show (sineGapMass q - (q : ℝ)) + ((q : ℝ) - sineGapMass q) = 0 by ring] at hz
    exact hz
  · intro h q hq
    have hb := primeProbeEnergy_tendsto (q := (q : ℝ)) (by exact_mod_cast hq.le)
    simpa using (h q hq).sub hb

/-- Upper bounds on the ordinary physical interval tests, including the atom at zero,
imply the signed trace comparison at every positive rational width. -/
theorem primeProbeTrace_of_fullOrdinateIntervalUpper (h : FullOrdinateIntervalUpper)
    (q : ℚ) (hq : 0 < q) :
    Tendsto (fun T : ℝ => sampledArgumentIncrement T q + primeProbeEnergy T q)
      atTop (𝓝 0) :=
  positiveGapPCC_iff_primeProbeTrace.mp (positiveGapPCC_of_fullOrdinateIntervalUpper h) q hq

/--
info: 'RiemannResearch.Analysis.MontgomeryPrimeTrace.primeProbeTrace_of_fullOrdinateIntervalUpper' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms primeProbeTrace_of_fullOrdinateIntervalUpper

/--
info: 'RiemannResearch.Analysis.MontgomeryPrimeTrace.primeProbeEnergy_error' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms primeProbeEnergy_error

/--
info: 'RiemannResearch.Analysis.MontgomeryPrimeTrace.positiveGapPCC_iff_primeProbeTrace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms positiveGapPCC_iff_primeProbeTrace

end RiemannResearch.Analysis.MontgomeryPrimeTrace
