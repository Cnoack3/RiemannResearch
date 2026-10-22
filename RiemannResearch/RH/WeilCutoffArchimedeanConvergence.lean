import RiemannResearch.Analysis.CompactCutoffVerticalDecay
import RiemannResearch.RH.WeilGammaLimits
import RiemannResearch.RH.WeilExplicitFormula.ExplicitFormula

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Actual pole and frequency-gamma convergence under compact cutoffs

The transform convention is reconciled at the integral level. Frequency
convergence uses a radius-independent quadratic majorant multiplied by the
actual gamma bracket; its integrability follows from the proved Gamma growth.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
open RiemannResearch.Analysis
open RiemannResearch.RH.SignedWeilCorrelation

namespace RiemannResearch.RH.WeilExplicitFormula

/-- Exact Fourier/Laplace sign convention, for every complex frequency. -/
theorem paperFT_eq_centeredTransform (k : ℝ → ℂ) (z : ℂ) :
    Zeta23.paperFT k z =
      BilateralLaplace.centeredTransform k ((1 / 2 : ℂ) - Complex.I * z) := by
  unfold Zeta23.paperFT BilateralLaplace.centeredTransform
    BilateralLaplace.transform BilateralLaplace.kernel
  apply integral_congr_ae
  filter_upwards with x
  congr 2
  ring

/-- Includes both pole evaluations z=±I/2, without separate estimates. -/
theorem tendsto_paperFT_compactCutoff {k : ℝ → ℂ}
    (hk : SmoothSuperexponentialDecay k) (z : ℂ) :
    Tendsto (fun N : ℕ => Zeta23.paperFT (compactCutoff N k) z) atTop
      (𝓝 (Zeta23.paperFT k z)) := by
  simp_rw [paperFT_eq_centeredTransform]
  exact tendsto_centeredTransform_compactCutoff hk _

theorem tendsto_paperFT_pole_pair_compactCutoff {k : ℝ → ℂ}
    (hk : SmoothSuperexponentialDecay k) :
    Tendsto (fun N : ℕ =>
      Zeta23.paperFT (compactCutoff N k) (Complex.I / 2) +
        Zeta23.paperFT (compactCutoff N k) (-Complex.I / 2)) atTop
      (𝓝 (Zeta23.paperFT k (Complex.I / 2) + Zeta23.paperFT k (-Complex.I / 2))) :=
  (tendsto_paperFT_compactCutoff hk _).add (tendsto_paperFT_compactCutoff hk _)

theorem continuous_paperFT_compactCutoff_real {k : ℝ → ℂ}
    (hk : SmoothSuperexponentialDecay k) (N : ℕ) :
    Continuous (fun r : ℝ => Zeta23.paperFT (compactCutoff N k) r) := by
  have hm : BilateralLaplace.HasExponentialMoments (compactCutoff N k) := by
    simpa only [iteratedDeriv_zero] using
      hasExponentialMoments_iteratedDeriv_compactCutoff hk N 0
  simp_rw [paperFT_eq_centeredTransform]
  exact (BilateralLaplace.differentiable_centeredTransform hm).continuous.comp (by fun_prop)

theorem norm_paperFT_compactCutoff_real_le {k : ℝ → ℂ}
    (hk : SmoothSuperexponentialDecay k) (N : ℕ) (r : ℝ) :
    ‖Zeta23.paperFT (compactCutoff N k) r‖ ≤ cutoffVerticalBound k 0 / (1 + r ^ 2) := by
  rw [paperFT_eq_centeredTransform]
  have h := norm_centeredTransform_compactCutoff_le hk (a := 0) le_rfl N
    ((1 / 2 : ℂ) - Complex.I * (r : ℂ)) (by simp)
  simpa [Complex.mul_re, Complex.mul_im, sq_abs] using h

private theorem gammaBracket_eq_increment (r : ℝ) :
    Zeta23.EF.gammaBracket r = digammaIncrement r +
      ((Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi) := by
  have harg : (1 / 4 : ℂ) + Complex.I * (r : ℂ) / 2 =
      (1 / 4 : ℂ) + Complex.I * (r / 2 : ℝ) := by push_cast; ring
  unfold Zeta23.EF.gammaBracket digammaIncrement
  rw [harg]
  ring

/-- Gamma-bracket integrability from actual quadratic decay, including its constant. -/
theorem integrable_mul_gammaBracket_of_decay (H : ℝ → ℂ)
    (hH : Continuous H) (hHi : Integrable H)
    (A : ℝ) (hA : 0 ≤ A) (hdec : ∀ r, ‖H r‖ ≤ A / (1 + r ^ 2)) :
    Integrable (fun r : ℝ => H r * (Zeta23.EF.gammaBracket r : ℂ)) := by
  have hi := (integrable_mul_digammaIncrement_of_decay H hH hHi A hA hdec).add
    (hHi.mul_const (((Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi : ℝ) : ℂ))
  apply hi.congr
  apply ae_of_all
  intro r
  simp only [Pi.add_apply, gammaBracket_eq_increment, Complex.ofReal_add, mul_add]

/-- The universal quadratic Gamma majorant is integrable on the whole line. -/
theorem integrable_gammaBracket_majorant (A : ℝ) (hA : 0 ≤ A) :
    Integrable (fun r : ℝ => (A / (1 + r ^ 2)) * |Zeta23.EF.gammaBracket r|) := by
  let H : ℝ → ℂ := fun r => (A / (1 + r ^ 2) : ℝ)
  have hd (r : ℝ) : 0 < 1 + r ^ 2 := by positivity
  have hH : Continuous H := by
    have hR : Continuous (fun r : ℝ => A / (1 + r ^ 2)) :=
      continuous_const.div₀ (continuous_const.add (continuous_id.pow 2))
        (fun r => (hd r).ne')
    exact Complex.ofRealCLM.continuous.comp hR
  have hHiR : Integrable (fun r : ℝ => A / (1 + r ^ 2)) := by
    simpa only [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul A
  have hHi : Integrable H := hHiR.ofReal
  have hnorm (r : ℝ) : ‖H r‖ = A / (1 + r ^ 2) := by
    simp only [H, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hA (hd r).le)]
  have hi := (integrable_mul_gammaBracket_of_decay H hH hHi A hA
    (fun r => (hnorm r).le)).norm
  apply hi.congr
  apply ae_of_all
  intro r
  change ‖H r * (Zeta23.EF.gammaBracket r : ℂ)‖ =
    (A / (1 + r ^ 2)) * |Zeta23.EF.gammaBracket r|
  rw [norm_mul, hnorm, Complex.norm_real, Real.norm_eq_abs]

/-- Convergence of the complete actual frequency-gamma integral. -/
theorem tendsto_integral_paperFT_gammaBracket_compactCutoff {k : ℝ → ℂ}
    (hk : SmoothSuperexponentialDecay k) :
    Tendsto (fun N : ℕ => ∫ r : ℝ,
      Zeta23.paperFT (compactCutoff N k) r * (Zeta23.EF.gammaBracket r : ℂ)) atTop
      (𝓝 (∫ r : ℝ, Zeta23.paperFT k r * (Zeta23.EF.gammaBracket r : ℂ))) := by
  let A := cutoffVerticalBound k 0
  have hA : 0 ≤ A := cutoffVerticalBound_nonneg k 0
  have hbase : Integrable (fun r : ℝ => A / (1 + r ^ 2)) := by
    simpa only [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul A
  have hHi (N : ℕ) : Integrable (fun r : ℝ => Zeta23.paperFT (compactCutoff N k) r) := by
    apply hbase.mono' (continuous_paperFT_compactCutoff_real hk N).aestronglyMeasurable
    exact ae_of_all _ (norm_paperFT_compactCutoff_real_le hk N)
  apply tendsto_integral_of_dominated_convergence
    (fun r : ℝ => (A / (1 + r ^ 2)) * |Zeta23.EF.gammaBracket r|)
  · intro N
    exact (integrable_mul_gammaBracket_of_decay _
      (continuous_paperFT_compactCutoff_real hk N) (hHi N) A hA
      (norm_paperFT_compactCutoff_real_le hk N)).aestronglyMeasurable
  · exact integrable_gammaBracket_majorant A hA
  · intro N
    apply ae_of_all
    intro r
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (norm_paperFT_compactCutoff_real_le hk N r)
      (abs_nonneg _)
  · apply ae_of_all
    intro r
    exact (tendsto_paperFT_compactCutoff hk r).mul_const _

/-- The normalization of the Weil formula is retained through the limit. -/
theorem tendsto_normalized_gamma_compactCutoff {k : ℝ → ℂ}
    (hk : SmoothSuperexponentialDecay k) :
    Tendsto (fun N : ℕ => (1 / (2 * Real.pi) : ℂ) *
      ∫ r : ℝ, Zeta23.paperFT (compactCutoff N k) r * (Zeta23.EF.gammaBracket r : ℂ))
      atTop (𝓝 ((1 / (2 * Real.pi) : ℂ) *
        ∫ r : ℝ, Zeta23.paperFT k r * (Zeta23.EF.gammaBracket r : ℂ))) :=
  (tendsto_integral_paperFT_gammaBracket_compactCutoff hk).const_mul _

end RiemannResearch.RH.WeilExplicitFormula
