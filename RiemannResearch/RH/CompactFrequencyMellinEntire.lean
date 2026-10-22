import RiemannResearch.RH.CompactFrequencyMellinRigidity
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Entire exponential-type bounds for compact-frequency Mellin mixtures

Source: user-provided compact-frequency rigidity argument, 2026-09-21,
Section 3. Compact frequency support provides an integrable dominating
function for the complex derivative and a global exponential bound.
All conclusions are proved from the actual compact-frequency data.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.SpectralObstruction

private theorem continuous_zeta_vertical (σ : ℝ) (hσ : σ < 1) :
    Continuous (fun t : ℝ => riemannZeta (verticalPoint σ t)) := by
  have hv : Continuous (verticalPoint σ) := by unfold verticalPoint; fun_prop
  apply continuous_iff_continuousAt.mpr
  intro t
  apply (differentiableAt_riemannZeta ?_).continuousAt.comp (hv.continuousAt)
  intro he
  have h := congrArg Complex.re he
  simp at h
  linarith

/-- The actual zeta-weighted complex density is integrable. -/
theorem zetaWeightedDensity_integrable (σ T : ℝ) (μ : Measure ℝ) (a : ℝ → ℂ)
    (hdata : CompactFrequencyData σ T μ a) :
    Integrable (zetaWeightedDensity σ a) μ := by
  obtain ⟨hσlo, hσ, hT, hμ, ha, hsupp⟩ := hdata
  have hc := continuous_zeta_vertical σ hσ
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc : IsCompact (Icc (-T) T)).exists_bound_of_continuousOn hc.continuousOn
  apply ha.bdd_mul hc.aestronglyMeasurable
  filter_upwards [hsupp] with t ht
  exact hC t (abs_le.mp ht)

/-- Uniform exponential bound for the Fourier kernel on bounded frequencies. -/
theorem fourierKernel_norm_le (T t : ℝ) (ht : |t| ≤ T) (z : ℂ) :
    ‖Complex.exp (-(t : ℂ) * Complex.I * z)‖ ≤ Real.exp (T * ‖z‖) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ ‖-(t : ℂ) * Complex.I * z‖ := Complex.re_le_norm _
    _ = |t| * ‖z‖ := by simp
    _ ≤ T * ‖z‖ := mul_le_mul_of_nonneg_right ht (norm_nonneg z)

/-- Every complex-frequency pairing of an integrable compact-frequency
complex density is an honest absolutely integrable function. -/
theorem densityFourier_integrable (T : ℝ) (μ : Measure ℝ) (b : ℝ → ℂ)
    (hb : Integrable b μ) (hsupp : ∀ᵐ t ∂μ, |t| ≤ T) (z : ℂ) :
    Integrable (fun t => b t * Complex.exp (-(t : ℂ) * Complex.I * z)) μ := by
  apply hb.mul_bdd
    ((show Continuous (fun t : ℝ => Complex.exp (-(t : ℂ) * Complex.I * z)) by
      fun_prop).aestronglyMeasurable)
  filter_upwards [hsupp] with t ht
  exact fourierKernel_norm_le T t ht z

/-- The compact-frequency Fourier integral is entire. -/
theorem densityFourier_differentiable (T : ℝ) (hT : 0 ≤ T)
    (μ : Measure ℝ) (b : ℝ → ℂ) (hb : Integrable b μ)
    (hsupp : ∀ᵐ t ∂μ, |t| ≤ T) : Differentiable ℂ (densityFourier μ b) := by
  intro z₀
  let F : ℂ → ℝ → ℂ :=
    fun z t => b t * Complex.exp (-(t : ℂ) * Complex.I * z)
  let F' : ℂ → ℝ → ℂ :=
    fun z t => (b t * Complex.exp (-(t : ℂ) * Complex.I * z)) * (-(t : ℂ) * Complex.I)
  let C : ℝ := Real.exp (T * (‖z₀‖ + 1))
  let bound : ℝ → ℝ := fun t => (‖b t‖ * C) * T
  have hFmeas (z : ℂ) : AEStronglyMeasurable (F z) μ :=
    hb.aestronglyMeasurable.mul
      ((show Continuous (fun t : ℝ => Complex.exp (-(t : ℂ) * Complex.I * z)) by
        fun_prop).aestronglyMeasurable)
  have hF'meas : AEStronglyMeasurable (F' z₀) μ :=
    (hFmeas z₀).mul ((show Continuous (fun t : ℝ => -(t : ℂ) * Complex.I) by
      fun_prop).aestronglyMeasurable)
  have hFint : Integrable (F z₀) μ := densityFourier_integrable T μ b hb hsupp z₀
  have hboundint : Integrable bound μ := (hb.norm.mul_const C).mul_const T
  have hderiv : ∀ᵐ t ∂μ, ∀ z ∈ ball z₀ 1, HasDerivAt (fun w => F w t) (F' z t) z := by
    filter_upwards [] with t
    intro z _
    have hlin : HasDerivAt (fun w : ℂ => (-(t : ℂ) * Complex.I) * w)
        (-(t : ℂ) * Complex.I) z := by
      simpa using (hasDerivAt_id z).const_mul (-(t : ℂ) * Complex.I)
    have he := (Complex.hasDerivAt_exp (-(t : ℂ) * Complex.I * z)).comp z hlin
    simpa [F, F', mul_assoc] using he.const_mul (b t)
  have hbound : ∀ᵐ t ∂μ, ∀ z ∈ ball z₀ 1, ‖F' z t‖ ≤ bound t := by
    filter_upwards [hsupp] with t ht
    intro z hz
    have hz' : ‖z - z₀‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hz
    have hznorm : ‖z‖ ≤ ‖z₀‖ + 1 := by
      have h := norm_add_le (z - z₀) z₀
      have he : z - z₀ + z₀ = z := by ring
      rw [he] at h
      linarith
    have he : ‖Complex.exp (-(t : ℂ) * Complex.I * z)‖ ≤ C :=
      (fourierKernel_norm_le T t ht z).trans
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hznorm hT))
    dsimp [F', bound]
    rw [norm_mul, norm_mul]
    have hn : ‖-(t : ℂ) * Complex.I‖ = |t| := by simp
    rw [hn]
    exact mul_le_mul (mul_le_mul_of_nonneg_left he (norm_nonneg _)) ht
      (abs_nonneg _) (mul_nonneg (norm_nonneg _) (Real.exp_nonneg _))
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := F) (F' := F') (bound := bound)
    (ball_mem_nhds z₀ (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall hFmeas) hFint hF'meas hbound hboundint hderiv
  exact h.2.differentiableAt

/-- Global exponential growth with the actual L1 mass as prefactor. -/
theorem densityFourier_norm_le_exp (T : ℝ) (μ : Measure ℝ) (b : ℝ → ℂ)
    (hb : Integrable b μ) (hsupp : ∀ᵐ t ∂μ, |t| ≤ T) (z : ℂ) :
    ‖densityFourier μ b z‖ ≤ (∫ t, ‖b t‖ ∂μ) * Real.exp (T * ‖z‖) := by
  unfold densityFourier
  calc
    _ ≤ ∫ t, ‖b t * Complex.exp (-(t : ℂ) * Complex.I * z)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t, ‖b t‖ * Real.exp (T * ‖z‖) ∂μ := by
      apply integral_mono_ae (densityFourier_integrable T μ b hb hsupp z).norm
        (hb.norm.mul_const _)
      filter_upwards [hsupp] with t ht
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (fourierKernel_norm_le T t ht z) (norm_nonneg _)
    _ = _ := integral_mul_const _ _

/-- The actual defect is entire and satisfies a global exponential-type
bound. No analytic regularity or growth provider is assumed. -/
theorem samplingDefect_entireExponentialType (σ T : ℝ)
    (μ : Measure ℝ) (a : ℝ → ℂ) (hdata : CompactFrequencyData σ T μ a) :
    EntireExponentialType (samplingDefect σ μ a) := by
  have hb := zetaWeightedDensity_integrable σ T μ a hdata
  obtain ⟨hσlo, hσ, hT, hμ, ha, hsupp⟩ := hdata
  let b := zetaWeightedDensity σ a
  let L : ℝ := ∫ t, ‖b t‖ ∂μ
  let B : ℂ := densityMass μ b
  have hL : 0 ≤ L := integral_nonneg (fun _ => norm_nonneg _)
  have hK : 0 ≤ T + |σ - 1| := add_nonneg hT (abs_nonneg _)
  refine ⟨?_, L + ‖B‖ + 1, T + |σ - 1|, by positivity, hK, ?_⟩
  · have hF := densityFourier_differentiable T hT μ b hb hsupp
    have hE : Differentiable ℂ (fun z : ℂ =>
        B * Complex.exp (((σ : ℂ) - 1) * z)) := by fun_prop
    exact hF.sub hE
  · intro z
    have hF := densityFourier_norm_le_exp T μ b hb hsupp z
    have he : ‖Complex.exp (((σ : ℂ) - 1) * z)‖ ≤
        Real.exp (|σ - 1| * ‖z‖) := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ ‖((σ : ℂ) - 1) * z‖ := Complex.re_le_norm _
        _ = |σ - 1| * ‖z‖ := by
          rw [norm_mul]
          norm_cast
        _ ≤ _ := le_rfl
    have hE1 : Real.exp (T * ‖z‖) ≤ Real.exp ((T + |σ - 1|) * ‖z‖) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (abs_nonneg _)) (norm_nonneg _)
    have hE2 : Real.exp (|σ - 1| * ‖z‖) ≤ Real.exp ((T + |σ - 1|) * ‖z‖) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hT) (norm_nonneg _)
    have hF' : ‖densityFourier μ b z‖ ≤ L * Real.exp ((T + |σ - 1|) * ‖z‖) :=
      hF.trans (mul_le_mul_of_nonneg_left hE1 hL)
    have he' : ‖B * Complex.exp (((σ : ℂ) - 1) * z)‖ ≤
        ‖B‖ * Real.exp ((T + |σ - 1|) * ‖z‖) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (he.trans hE2) (norm_nonneg _)
    have hs := norm_sub_le (densityFourier μ b z) (B * Complex.exp (((σ : ℂ) - 1) * z))
    change ‖densityFourier μ b z - B * Complex.exp (((σ : ℂ) - 1) * z)‖ ≤ _
    nlinarith [Real.exp_pos ((T + |σ - 1|) * ‖z‖)]

end RiemannResearch.RH.Pareto.SpectralObstruction
