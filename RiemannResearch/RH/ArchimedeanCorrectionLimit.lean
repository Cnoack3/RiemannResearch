import RiemannResearch.RH.PrimeCompensationLimits

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Actual gamma and higher-power correction limits

The inverse-square error estimates use the actual finite moments proved in
`PrimeCompensationLimits`. No prime-sector sign, Weil nullity, or limit of
arithmetic discrepancy is assumed.
-/

open MeasureTheory Set Filter
open scoped Topology
namespace RiemannResearch.RH.PrimeCompensationLimits

/-- The finite archimedean displacement correction. Its integrability is proved
below from the quadratic profile displacement bound. -/
noncomputable def gammaDisplacementCorrection (c : ℝ → ℝ) (R : ℝ) : ℝ :=
  2 * ∫ t in Ioi 0, displacementKernel t * (1 - c (t / R))

/-- The actual gamma correction is integrable and bounded by its second moment. -/
theorem gammaDisplacementCorrection_bound (c : ℝ → ℝ) (hc : Continuous c)
    (R B : ℝ) (hB : 0 ≤ B)
    (hdisp : ∀ t : ℝ, 0 < t → |1 - c (t / R)| ≤ B * (t / R) ^ 2) :
    IntegrableOn (fun t => displacementKernel t * (1 - c (t / R))) (Ioi 0) ∧
    |gammaDisplacementCorrection c R| ≤
      (2 * B / R ^ 2) * ∫ t in Ioi 0, displacementKernel t * t ^ 2 := by
  let M : ℝ → ℝ := fun t => displacementKernel t * t ^ 2
  let f : ℝ → ℝ := fun t => displacementKernel t * (1 - c (t / R))
  have hm : Measurable f := by
    unfold f displacementKernel
    fun_prop
  have hiM : IntegrableOn M (Ioi 0) := integrable_displacementKernel_secondMoment
  have hdom (t : ℝ) (ht : 0 < t) : ‖f t‖ ≤ (B / R ^ 2) * M t := by
    simp only [f, M, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (displacementKernel_nonneg ht)]
    calc
      _ ≤ displacementKernel t * (B * (t / R) ^ 2) :=
        mul_le_mul_of_nonneg_left (hdisp t ht) (displacementKernel_nonneg ht)
      _ = _ := by ring
  have hif : IntegrableOn f (Ioi 0) := by
    apply (hiM.const_mul (B / R ^ 2)).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hdom t ht
  refine ⟨hif, ?_⟩
  have hb : |∫ t in Ioi 0, f t| ≤ (B / R ^ 2) * ∫ t in Ioi 0, M t := by
    calc
      _ ≤ ∫ t in Ioi 0, ‖f t‖ := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm f
      _ ≤ ∫ t in Ioi 0, (B / R ^ 2) * M t := by
        apply integral_mono_ae hif.norm (hiM.const_mul _)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hdom t ht
      _ = _ := integral_const_mul _ _
  unfold gammaDisplacementCorrection
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hh := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [f, M, mul_assoc, mul_div_assoc] using hh

/-- The full gamma displacement correction vanishes as the window grows,
for any profile family with one uniform quadratic displacement constant. -/
theorem gammaDisplacementCorrection_tendsto_zero
    (c : ℝ → ℝ → ℝ) (hc : ∀ R, Continuous (c R)) (B : ℝ) (hB : 0 ≤ B)
    (hdisp : ∀ R : ℝ, 0 < R → ∀ t : ℝ, 0 < t →
      |1 - c R (t / R)| ≤ B * (t / R) ^ 2) :
    Tendsto (fun R => gammaDisplacementCorrection (c R) R) atTop (𝓝 0) := by
  let M := ∫ t in Ioi 0, displacementKernel t * t ^ 2
  have hlim : Tendsto (fun R : ℝ => (2 * B / R ^ 2) * M) atTop (𝓝 0) := by
    have h := ((tendsto_inv_atTop_zero.pow 2).const_mul (2 * B)).mul_const M
    simpa only [inv_pow, zero_pow (by decide : (2 : ℕ) ≠ 0),
      mul_zero, zero_mul, div_eq_mul_inv] using h
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  simpa only [Real.norm_eq_abs, M] using
    (gammaDisplacementCorrection_bound (c R) (hc R) R B hB (hdisp R hR)).2

/-- The correction from every higher prime power also vanishes, with the
actual convergent arithmetic second moment as dominating constant. -/
theorem higherPrimePowerCorrection_tendsto_zero
    (c : ℝ → ℝ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hdisp : ∀ R : ℝ, 0 < R → ∀ t : ℝ,
      |1 - c R (t / R)| ≤ B * (t / R) ^ 2) :
    Tendsto (fun R => higherPrimePowerCorrection (c R) R) atTop (𝓝 0) := by
  let M := ∑' pj : ℕ × ℕ,
    higherPrimePowerWeight pj.1 pj.2 * higherPrimePowerDisplacement pj.1 pj.2 ^ 2
  have hlim : Tendsto (fun R : ℝ => (2 * B / R ^ 2) * M) atTop (𝓝 0) := by
    have h := ((tendsto_inv_atTop_zero.pow 2).const_mul (2 * B)).mul_const M
    simpa only [inv_pow, zero_pow (by decide : (2 : ℕ) ≠ 0),
      mul_zero, zero_mul, div_eq_mul_inv] using h
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  simpa only [Real.norm_eq_abs, M] using
    (higherPrimePowerCorrection_bound (c R) R B hB (hdisp R hR)).2

end RiemannResearch.RH.PrimeCompensationLimits
