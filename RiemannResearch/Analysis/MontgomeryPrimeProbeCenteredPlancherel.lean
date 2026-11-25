import RiemannResearch.Analysis.MontgomeryCenteredMertens
import RiemannResearch.Analysis.MontgomeryPrimeProbePlancherel
import RiemannResearch.Analysis.MontgomeryMovingPrimeProbeTrace

/-! # Prime-probe energy for widths below the three-halves power of the logarithm

Source: user-provided centered-Mertens argument. All constants in the bounds
are independent of the bandwidth and height.
-/

noncomputable section
namespace RiemannResearch.Analysis.MontgomeryPrimeTrace
open Filter MeasureTheory Set MontgomeryPositiveGap
open scoped Topology

/-- Physical energy of the logarithmic Mertens remainder on the whole half-line. -/
def logMertensSquareMass : ℝ := ∫ y in Ioi (0 : ℝ), logMertensRemainder y ^ 2

/-- Scaling the centered discrepancy gives an exact truncated physical energy. -/
theorem centered_primeLogCDF_sq_integral {T : ℝ} (hT : 1 < T) :
    let L := Real.log T
    (∫ v in (0 : ℝ)..1, (primeLogCDF T v - v - mertensCenter / L)^2) =
      (∫ y in (0 : ℝ)..L, logMertensRemainder y ^ 2) / L^3 := by
  let L := Real.log T
  have hL : 0 < L := Real.log_pos hT
  change (∫ v in (0 : ℝ)..1, (primeLogCDF T v - v - mertensCenter / L)^2) = _
  calc
    _ = ∫ v in (0 : ℝ)..1, (logMertensRemainder (L * v))^2 / L^2 := by
      apply intervalIntegral.integral_congr
      intro v _
      change (primeLogCDF T v - v - mertensCenter / L)^2 =
        logMertensRemainder (L * v)^2 / L^2
      rw [primeLogCDF_sub_eq_centered hT v]
      change ((mertensCenter + logMertensRemainder (L * v)) / L - mertensCenter / L)^2 = _
      field_simp [hL.ne'] <;> ring
    _ = (∫ y in (0 : ℝ)..L, logMertensRemainder y^2) / L^3 := by
      rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_mul_left
        (fun x => logMertensRemainder x ^ 2) hL.ne', mul_zero, mul_one, smul_eq_mul]
      field_simp [hL.ne'] <;> ring

private theorem centered_primeLogCDF_sq_le {T : ℝ} (hT : 1 < T) :
    (∫ v in (0 : ℝ)..1, (primeLogCDF T v - v - mertensCenter / Real.log T)^2) ≤
      logMertensSquareMass / (Real.log T)^3 := by
  rw [centered_primeLogCDF_sq_integral hT, intervalIntegral.integral_of_le (Real.log_pos hT).le]
  apply div_le_div_of_nonneg_right _ (pow_nonneg (Real.log_pos hT).le 3)
  apply setIntegral_mono_set integrableOn_logMertensRemainder_sq
    (Eventually.of_forall fun _ => sq_nonneg _)
  exact Eventually.of_forall fun _ hx => hx.1

/-- The frequency-independent contribution from both endpoints. -/
def primeProbeEndpointConstant : ℝ := Real.log 4 + 4 + 2 * |mertensCenter|

/-- Unconditional integrated squared Fourier error, with constants uniform in q and T. -/
theorem primeProbe_l2_error_centered {T q : ℝ} (hT : 1 < T) (hq : 0 ≤ q) :
    let L := Real.log T
    (∫ u in (0 : ℝ)..q, ‖primeFourierProbe T u - primeContinuumProbe u‖^2) ≤
      (2 * primeProbeEndpointConstant^2) * (q / L^2) +
        (8 * Real.pi^2 * logMertensSquareMass) * (q^2 / L^3) := by
  let L := Real.log T
  let a := mertensCenter / L
  have hL : 0 < L := Real.log_pos hT
  have ha : |a| = |mertensCenter| / L := by rw [abs_div, abs_of_pos hL]
  have hb : |a| + |primeLogCDF T 1 - 1 - a| ≤ primeProbeEndpointConstant / L := by
    calc
      _ ≤ |a| + (|primeLogCDF T 1 - 1| + |a|) := by
        apply add_le_add le_rfl
        simpa only [Real.norm_eq_abs] using norm_sub_le (primeLogCDF T 1 - 1) a
      _ ≤ |a| + ((Real.log 4 + 4) / L + |a|) := by
        gcongr
        exact primeLogCDF_error hT zero_le_one
      _ = _ := by rw [ha]; unfold primeProbeEndpointConstant; ring
  have h := primeProbe_l2_error_shift hT hq a
  have hs := centered_primeLogCDF_sq_le hT
  calc
    _ ≤ _ := h
    _ ≤ 2 * q * (primeProbeEndpointConstant / L)^2 +
          2 * (2 * Real.pi * q)^2 * (logMertensSquareMass / L^3) :=
      add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb 2)
          (by positivity))
        (mul_le_mul_of_nonneg_left hs (by positivity))
    _ = _ := by
      change 2 * q * (primeProbeEndpointConstant / L)^2 +
        2 * (2 * Real.pi * q)^2 * (logMertensSquareMass / L^3) = _
      change _ = (2 * primeProbeEndpointConstant^2) * (q / L^2) +
        (8 * Real.pi^2 * logMertensSquareMass) * (q^2 / L^3)
      field_simp [hL.ne'] <;> ring

/-- The width may vary with height, with q = o(log T * sqrt(log T)). -/
theorem primeProbeEnergy_moving_sublog_three_halves (q : ℝ → ℝ)
    (hq : ∀ᶠ T in atTop, 0 ≤ q T)
    (hsub : Tendsto (fun T : ℝ => q T / (Real.log T * Real.sqrt (Real.log T))) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => primeProbeEnergy T (q T) - (q T - sineGapMass (q T))) atTop (𝓝 0) := by
  let L := Real.log
  let V := fun T : ℝ => (2 * primeProbeEndpointConstant^2) * (q T / L T ^ 2) +
    (8 * Real.pi^2 * logMertensSquareMass) * (q T ^ 2 / L T ^ 3)
  have hrec := (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop).const_div_atTop (1 : ℝ)
  have hV : Tendsto V atTop (𝓝 0) := by
    have hlim := ((hsub.mul hrec).const_mul (2 * primeProbeEndpointConstant^2)).add
      ((hsub.pow 2).const_mul (8 * Real.pi^2 * logMertensSquareMass))
    apply Tendsto.congr' _ (by simpa using hlim)
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    have hp : 0 < L T := Real.log_pos hT
    have hs := Real.sq_sqrt hp.le
    have hs₁ : (L T * Real.sqrt (L T)) * Real.sqrt (L T) = L T ^ 2 := by
      calc
        _ = L T * (Real.sqrt (L T))^2 := by ring
        _ = L T^2 := by rw [hs]; ring
    have hs₂ : (L T * Real.sqrt (L T))^2 = L T^3 := by rw [mul_pow, hs]; ring
    change 2 * primeProbeEndpointConstant ^ 2 *
        ((q T / (L T * Real.sqrt (L T))) * (Real.sqrt (L T))⁻¹) +
      (8 * Real.pi ^ 2 * logMertensSquareMass) * (q T / (L T * Real.sqrt (L T))) ^ 2 = V T
    dsimp only [V]
    rw [← div_eq_mul_inv, div_div, hs₁, div_pow, hs₂]
  have hlim : Tendsto (fun T => 2 * Real.sqrt (V T) + V T) atTop (𝓝 0) := by
    simpa using ((Real.continuous_sqrt.continuousAt.tendsto.comp hV).const_mul 2).add hV
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_gt_atTop (1 : ℝ), hq] with T hT hw
  simpa only [Real.norm_eq_abs] using primeProbeEnergy_error_of_l2 hw (primeProbe_l2_error_centered hT hw)

/-- In particular, each fixed positive multiple of log T is permitted. -/
theorem primeProbeEnergy_moving_const_mul_log {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun T : ℝ => primeProbeEnergy T (c * Real.log T) -
      (c * Real.log T - sineGapMass (c * Real.log T))) atTop (𝓝 0) := by
  apply primeProbeEnergy_moving_sublog_three_halves
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    exact mul_nonneg hc (Real.log_pos hT).le
  · apply Tendsto.congr' _ ((Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop).const_div_atTop c)
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    dsimp
    field_simp [(Real.log_pos hT).ne', (Real.sqrt_pos.2 (Real.log_pos hT)).ne']

/-- The signed comparison at a diverging sub-three-halves width has one
remaining term, the sampled actual-zero argument increment. -/
theorem movingPrimeProbeTrace_sublog_three_halves_iff {q : ℝ → ℝ}
    (hq : Tendsto q atTop atTop)
    (hsub : Tendsto (fun T : ℝ => q T / (Real.log T * Real.sqrt (Real.log T))) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => sampledArgumentIncrement T (q T) + primeProbeEnergy T (q T))
        atTop (𝓝 0) ↔
      Tendsto (fun T : ℝ => sampledArgumentIncrement T (q T)) atTop (𝓝 (-(1 / 2 : ℝ))) :=
  movingPrimeProbeTrace_iff_sampled_neg_half hq
    (primeProbeEnergy_moving_sublog_three_halves q (hq.eventually_ge_atTop 0) hsub)

#print axioms centered_primeLogCDF_sq_integral
#print axioms primeProbe_l2_error_centered
#print axioms primeProbeEnergy_moving_sublog_three_halves

end RiemannResearch.Analysis.MontgomeryPrimeTrace
