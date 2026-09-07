import RiemannResearch.Analysis.SuperexponentialDecay
import RiemannResearch.RH.NoncompactPrimeSquareScaling

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Concrete superexponential providers for the noncompact square formula

The profile and its derivative have explicit decay, from which this file
derives the integrability and inverse-square hypotheses of the exact Abel
limit. The formula now applies to any actual C¹ superexponential correlation;
constructing the arithmetic-return correlation remains a separate task.
-/

open MeasureTheory Set Filter
open RiemannResearch.Analysis
namespace RiemannResearch.RH

open scoped Topology

/-- A continuous real superexponential function is integrable. -/
theorem integrable_real_of_superexponential {c : ℝ → ℝ}
    (hc : Continuous c) (hs : SuperexponentialDecay c) : Integrable c := by
  obtain ⟨A, hA, hbound⟩ := hs 1 (by norm_num)
  apply (integrable_exp_neg_abs.const_mul A).mono' hc.aestronglyMeasurable
  exact ae_of_all _ (fun x => by simpa only [neg_one_mul] using hbound x)

private theorem exp_log_squareProfile {R x : ℝ} (hR : R ≠ 0) (hx : 0 < x) :
    Real.exp (-R * (2 * Real.log x / R)) = (x ^ 2)⁻¹ := by
  have he : R * (2 * Real.log x / R) = Real.log x + Real.log x := by
    field_simp
    ring
  rw [show -R * (2 * Real.log x / R) = -(R * (2 * Real.log x / R)) by ring,
    Real.exp_neg, he, Real.exp_add, Real.exp_log hx]
  ring

private theorem exp_log_halfSquareProfile {R x : ℝ} (hR : R ≠ 0) (hx : 0 < x) :
    Real.exp (-(R / 2) * (2 * Real.log x / R)) = x⁻¹ := by
  have he : -(R / 2) * (2 * Real.log x / R) = -Real.log x := by
    field_simp
  rw [he, Real.exp_neg, Real.exp_log hx]

/-- Superexponential decay of c and c' supplies every convergence hypothesis
of the noncompact prime-square identity for each fixed positive R. -/
theorem exists_squareProfile_decay_of_superexponential
    (c : ℝ → ℝ) (hc : Differentiable ℝ c)
    (hs : SuperexponentialDecay c) (hs' : SuperexponentialDecay (deriv c))
    {R : ℝ} (hR : 0 < R) :
    ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧
      (∀ x : ℝ, 1 ≤ x → |c (2 * Real.log x / R)| ≤ A / x ^ 2) ∧
      (∀ x : ℝ, 1 ≤ x →
        |deriv (fun y => c (2 * Real.log y / R)) x| ≤ D / x ^ 2) := by
  obtain ⟨A, hA, hbound⟩ := hs R hR
  obtain ⟨D, hD, hbound'⟩ := hs' (R / 2) (by positivity)
  refine ⟨A, (2 / R) * D, hA.le, by positivity, ?_, ?_⟩
  · intro x hx
    have hx0 : 0 < x := by linarith
    have hs0 : 0 ≤ 2 * Real.log x / R :=
      div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hx)) hR.le
    have h := hbound (2 * Real.log x / R)
    rw [Real.norm_eq_abs, abs_of_nonneg hs0,
      exp_log_squareProfile hR.ne' hx0] at h
    simpa only [div_eq_mul_inv] using h
  · intro x hx
    have hx0 : 0 < x := by linarith
    have hs0 : 0 ≤ 2 * Real.log x / R :=
      div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hx)) hR.le
    have h := hbound' (2 * Real.log x / R)
    rw [Real.norm_eq_abs, abs_of_nonneg hs0,
      exp_log_halfSquareProfile hR.ne' hx0] at h
    rw [(hasDerivAt_primeSquareProfile c hc R hx0.ne').deriv,
      abs_div, abs_mul, abs_of_pos (div_pos (by norm_num) hR), abs_of_pos hx0]
    calc
      _ ≤ ((2 / R) * (D * x⁻¹)) / x := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left h (by positivity)) hx0.le
      _ = _ := by ring

/-- Exact full prime-square formula for an actual C¹ superexponential profile.
All series convergence and improper integral convergence follow from the
explicit decay hypotheses; none is separately assumed. -/
theorem primeSquareSector_exact_of_superexponential
    (c : ℝ → ℝ) (hc : Differentiable ℝ c) (hc' : Continuous (deriv c))
    (hs : SuperexponentialDecay c) (hs' : SuperexponentialDecay (deriv c))
    {R : ℝ} (hR : 0 < R) :
    primeSquareSector c R = -R * (∫ s in Ioi 0, c s) +
      (4 / R) * ∫ x in Ioi 1,
        deriv c (2 * Real.log x / R) * primeSquareDiscrepancy x / x := by
  obtain ⟨A, D, hA, hD, hdecay, hderiv⟩ :=
    exists_squareProfile_decay_of_superexponential c hc hs hs' hR
  exact primeSquareSector_exact_noncompact_scaled c hc hc'
    (integrable_real_of_superexponential hc.continuous hs).integrableOn
    hR A D hA hD hdecay hderiv

/-- The uniform Mertens variation estimate applies to every C¹
superexponential profile and every positive window size. -/
theorem exists_primeSquare_superexponential_variation_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ c : ℝ → ℝ, Differentiable ℝ c →
      Continuous (deriv c) → SuperexponentialDecay c → SuperexponentialDecay (deriv c) →
      ∀ R : ℝ, 0 < R →
      |primeSquareSector c R + R * (∫ s in Ioi 0, c s)| ≤
        2 * B * ∫ s in Ioi 0, |deriv c s| := by
  obtain ⟨B, hB0, hB⟩ := exists_noncompact_primeSquare_scaled_remainder_bound
  refine ⟨B, hB0, ?_⟩
  intro c hc hc' hs hs' R hR
  obtain ⟨A, D, hA, hD, hdecay, hderiv⟩ :=
    exists_squareProfile_decay_of_superexponential c hc hs hs' hR
  exact hB c hc hc' (integrable_real_of_superexponential hc.continuous hs).integrableOn
    (integrable_real_of_superexponential hc' hs').integrableOn
    R A D hR hA hD hdecay hderiv

/-- The actual prime-square series has its linear broad-window asymptotic
for each fixed C¹ superexponential profile. The asymptotic is a conclusion
of the proved arithmetic Mertens bound, not an input hypothesis. -/
theorem tendsto_primeSquareSector_div_of_superexponential
    (c : ℝ → ℝ) (hc : Differentiable ℝ c) (hc' : Continuous (deriv c))
    (hs : SuperexponentialDecay c) (hs' : SuperexponentialDecay (deriv c)) :
    Tendsto (fun R : ℝ => primeSquareSector c R / R) atTop
      (𝓝 (-(∫ s in Ioi 0, c s))) := by
  obtain ⟨B, hB0, hB⟩ := exists_primeSquare_superexponential_variation_bound
  let M : ℝ := ∫ s in Ioi 0, c s
  let K : ℝ := 2 * B * ∫ s in Ioi 0, |deriv c s|
  have hlim : Tendsto (fun R : ℝ => K / R) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_inv_atTop_zero.const_mul K
  have he : Tendsto (fun R : ℝ => (primeSquareSector c R + R * M) / R)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hR]
    exact div_le_div_of_nonneg_right (hB c hc hc' hs hs' R hR) hR.le
  have hresult := he.sub_const M
  apply (show Tendsto
    (fun R : ℝ => (primeSquareSector c R + R * M) / R - M) atTop
      (𝓝 (-M)) by simpa only [zero_sub] using hresult).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  field_simp
  ring

end RiemannResearch.RH
