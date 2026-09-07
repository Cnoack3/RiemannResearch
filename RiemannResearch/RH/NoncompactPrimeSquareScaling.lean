import RiemannResearch.RH.NoncompactPrimeSquareLimit

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Scaled noncompact square main term and uniform variation remainder

These identities pass to the actual full half-line integrals. The explicit
calculus inputs are C¹ regularity, profile/derivative integrability, and the
x-coordinate decay used to prove absolute convergence of the arithmetic
series. Uniform bounds for the varying full-return family remain a separate
provider obligation.
-/

open MeasureTheory Set Filter
open scoped Topology
namespace RiemannResearch.RH

private theorem tendsto_squareProfile_endpoint {R : ℝ} (hR : 0 < R) :
    Tendsto (fun N : ℕ => 2 * Real.log N / R) atTop atTop := by
  have hl := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  refine tendsto_atTop.2 ?_
  intro b
  filter_upwards [hl.eventually (eventually_ge_atTop (R * b / 2))] with N hN
  change R * b / 2 ≤ Real.log (N : ℝ) at hN
  apply (le_div_iff₀ hR).mpr
  nlinarith

private theorem tendsto_setIntegral_Ioc_nat' {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioi 1)) :
    Tendsto (fun N : ℕ => ∫ x in Ioc 1 (N : ℝ), f x) atTop
      (𝓝 (∫ x in Ioi 1, f x)) := by
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  apply (intervalIntegral_tendsto_integral_Ioi 1 hf hnat).congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  exact intervalIntegral.integral_of_le hN1

/-- The full main integral has its exact R/2 scaling. Both improper-integral
limit passages are justified by the stated integrability conditions. -/
theorem primeSquare_main_integral_scale_noncompact
    (c : ℝ → ℝ) (hc : Continuous c) {R : ℝ} (hR : 0 < R)
    (hci : IntegrableOn c (Ioi 0))
    (hgi : IntegrableOn (fun x => c (2 * Real.log x / R) / x) (Ioi 1)) :
    (∫ x in Ioi 1, c (2 * Real.log x / R) / x) =
      R / 2 * ∫ s in Ioi 0, c s := by
  have hleft := tendsto_setIntegral_Ioc_nat' hgi
  have hright := (intervalIntegral_tendsto_integral_Ioi 0 hci
    (tendsto_squareProfile_endpoint hR)).const_mul (R / 2)
  have heq :
      (fun N : ℕ => R / 2 * ∫ s in (0 : ℝ)..(2 * Real.log N / R), c s) =ᶠ[atTop]
      (fun N : ℕ => ∫ x in Ioc 1 (N : ℝ), c (2 * Real.log x / R) / x) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
    exact (primeSquare_main_integral_scale c hc hR.ne' hN1).symm
  exact tendsto_nhds_unique hleft (hright.congr' heq)

/-- Total variation is preserved on the full noncompact half-line. -/
theorem primeSquareProfile_variation_noncompact
    (c : ℝ → ℝ) (hc : Differentiable ℝ c) (hc' : Continuous (deriv c))
    {R : ℝ} (hR : 0 < R)
    (hci : IntegrableOn (deriv c) (Ioi 0))
    (hgi : IntegrableOn (deriv (fun x => c (2 * Real.log x / R))) (Ioi 1)) :
    (∫ x in Ioi 1, |deriv (fun y => c (2 * Real.log y / R)) x|) =
      ∫ s in Ioi 0, |deriv c s| := by
  have hleft := tendsto_setIntegral_Ioc_nat' hgi.abs
  have hright := intervalIntegral_tendsto_integral_Ioi 0 hci.abs
    (tendsto_squareProfile_endpoint hR)
  have heq :
      (fun N : ℕ => ∫ s in (0 : ℝ)..(2 * Real.log N / R), |deriv c s|) =ᶠ[atTop]
      (fun N : ℕ => ∫ x in Ioc 1 (N : ℝ),
        |deriv (fun y => c (2 * Real.log y / R)) x|) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
    have hscale := primeSquare_main_integral_scale (fun s => |deriv c s|)
      hc'.abs hR.ne' hN1
    have he :
        (∫ x in Ioc 1 (N : ℝ), |deriv (fun y => c (2 * Real.log y / R)) x|) =
        (2 / R) * ∫ x in Ioc 1 (N : ℝ), |deriv c (2 * Real.log x / R)| / x := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      rw [(hasDerivAt_primeSquareProfile c hc R (by linarith [hx.1])).deriv,
        abs_div, abs_mul, abs_of_pos (div_pos (by norm_num) hR),
        abs_of_pos (by linarith [hx.1] : 0 < x)]
      ring
    rw [he, hscale]
    field_simp
  exact tendsto_nhds_unique hleft (hright.congr' heq)

/-- Exact full square-sector identity with the linear main term and the complete
signed discrepancy integral. Absolute convergence is derived from decay. -/
theorem primeSquareSector_exact_noncompact_scaled
    (c : ℝ → ℝ) (hc : Differentiable ℝ c) (hc' : Continuous (deriv c))
    (hci : IntegrableOn c (Ioi 0))
    {R : ℝ} (hR : 0 < R) (A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hdecay : ∀ x : ℝ, 1 ≤ x → |c (2 * Real.log x / R)| ≤ A / x ^ 2)
    (hderiv : ∀ x : ℝ, 1 ≤ x →
      |deriv (fun y => c (2 * Real.log y / R)) x| ≤ D / x ^ 2) :
    primeSquareSector c R = -R * (∫ s in Ioi 0, c s) +
      (4 / R) * ∫ x in Ioi 1,
        deriv c (2 * Real.log x / R) * primeSquareDiscrepancy x / x := by
  obtain ⟨hi, hd, he⟩ := integrable_noncompact_primeSquare_terms
    c hc R A D hA hD hdecay hderiv
  rw [primeSquareSector_exact_noncompact_remainder c hc hc' R A D hA hD hdecay hderiv,
    primeSquare_main_integral_scale_noncompact c hc.continuous hR hci hi]
  have heq :
      (∫ x in Ioi 1, deriv (fun y => c (2 * Real.log y / R)) x *
        primeSquareDiscrepancy x) =
      (2 / R) * ∫ x in Ioi 1,
        deriv c (2 * Real.log x / R) * primeSquareDiscrepancy x / x := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [(hasDerivAt_primeSquareProfile c hc R (by change 1 < x at hx; linarith)).deriv]
    ring
  rw [heq]
  ring

/-- A single actual Mertens constant controls every admissible noncompact
profile by its full variation. This is the precise uniform square error
interface, with the linear main term retained. -/
theorem exists_noncompact_primeSquare_scaled_remainder_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (c : ℝ → ℝ), Differentiable ℝ c →
      Continuous (deriv c) → IntegrableOn c (Ioi 0) →
      IntegrableOn (deriv c) (Ioi 0) → ∀ R A D : ℝ, 0 < R → 0 ≤ A → 0 ≤ D →
      (∀ x : ℝ, 1 ≤ x → |c (2 * Real.log x / R)| ≤ A / x ^ 2) →
      (∀ x : ℝ, 1 ≤ x →
        |deriv (fun y => c (2 * Real.log y / R)) x| ≤ D / x ^ 2) →
      |primeSquareSector c R + R * (∫ s in Ioi 0, c s)| ≤
        2 * B * ∫ s in Ioi 0, |deriv c s| := by
  obtain ⟨B, hB0, hB⟩ := exists_noncompact_primeSquare_remainder_bound
  refine ⟨B, hB0, ?_⟩
  intro c hc hc' hci hcdi R A D hR hA hD hdecay hderiv
  obtain ⟨hi, hd, he⟩ := integrable_noncompact_primeSquare_terms
    c hc R A D hA hD hdecay hderiv
  have h := hB c hc hc' R A D hA hD hdecay hderiv
  rw [primeSquare_main_integral_scale_noncompact c hc.continuous hR hci hi,
    primeSquareProfile_variation_noncompact c hc hc' hR hcdi hd] at h
  convert h using 1 <;> congr 2 <;> ring

end RiemannResearch.RH
