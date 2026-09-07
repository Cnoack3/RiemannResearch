import RiemannResearch.RH.WeilArchimedeanNormalization
import RiemannResearch.Analysis.CrossCorrelationRegularity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Actual pole and gamma integrability for superexponential tests

Source: the user-provided Nyman--Weil note, section 2, and Suzuki's arithmetic
Weil functional, https://arxiv.org/html/2606.09096v1, section 1.1.

The signed gamma subtraction is retained. Its integrability follows from
the actual Lipschitz correlation and the evaluated regulator correction.
No explicit formula or zero-side identification is assumed or asserted.
-/

open MeasureTheory Set Filter

namespace RiemannResearch.RH.SignedWeilCorrelation

noncomputable section

theorem weilGammaKernel_eq_decay_quotient (t : ℝ) :
    weilGammaKernel t = Real.exp (-t / 2) / (1 - Real.exp (-2 * t)) := by
  have hn : Real.exp (t / 2) = Real.exp t * Real.exp (-t / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hd : Real.exp t - Real.exp (-t) =
      Real.exp t * (1 - Real.exp (-2 * t)) := by
    rw [mul_sub, mul_one, ← Real.exp_add]
    congr 1
    congr 1
    ring
  unfold weilGammaKernel
  rw [hn, hd]
  exact mul_div_mul_left _ _ (Real.exp_ne_zero t)

theorem weilGammaKernel_nonneg {t : ℝ} (ht : 0 < t) :
    0 ≤ weilGammaKernel t := by
  unfold weilGammaKernel
  apply div_nonneg (Real.exp_nonneg _)
  exact sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))

/-- One global integrable majorant handles both the singular origin and the
decaying infinite tail of the gamma kernel. -/
theorem weilGammaKernel_mul_self_le {t : ℝ} (ht : 0 < t) :
    weilGammaKernel t * t ≤ 4 * Real.exp (-t / 4) := by
  have hden : 0 < 1 - Real.exp (-2 * t) := by
    apply sub_pos.mpr
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hexp : 1 + t ≤ Real.exp (2 * t) := by
    have := Real.add_one_le_exp (2 * t)
    linarith
  have hinv : (1 + t) * Real.exp (-2 * t) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hexp (Real.exp_nonneg (-2 * t))
    have he : Real.exp (2 * t) * Real.exp (-2 * t) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      simp
    rwa [he] at h
  have hquot : t / (1 - Real.exp (-2 * t)) ≤ 1 + t := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have hpoly : 1 + t ≤ 4 * Real.exp (t / 4) := by
    have := Real.add_one_le_exp (t / 4)
    linarith
  rw [weilGammaKernel_eq_decay_quotient]
  calc
    Real.exp (-t / 2) / (1 - Real.exp (-2 * t)) * t =
        Real.exp (-t / 2) * (t / (1 - Real.exp (-2 * t))) := by ring
    _ ≤ Real.exp (-t / 2) * (1 + t) :=
      mul_le_mul_of_nonneg_left hquot (Real.exp_nonneg _)
    _ ≤ Real.exp (-t / 2) * (4 * Real.exp (t / 4)) :=
      mul_le_mul_of_nonneg_left hpoly (Real.exp_nonneg _)
    _ = 4 * Real.exp (-t / 4) := by
      rw [show Real.exp (-t / 2) * (4 * Real.exp (t / 4)) =
        4 * (Real.exp (-t / 2) * Real.exp (t / 4)) by ring, ← Real.exp_add]
      congr 2
      ring

theorem integrable_weilPoleKernel_mul_of_exp_decay (C : ℝ → ℝ) (hCc : Continuous C)
    (A : ℝ) (hA : 0 ≤ A)
    (hC : ∀ t, 0 ≤ t → |C t| ≤ A * Real.exp (-3 * t)) :
    Integrable (fun t => weilPoleKernel t * C t) positiveMeasure := by
  have hi : Integrable (fun t : ℝ => (2 * A) * Real.exp ((-2 : ℝ) * t))
      positiveMeasure :=
    (integrableOn_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0) 0).const_mul (2 * A)
  apply hi.mono'
  · have hc : Continuous (fun t => weilPoleKernel t * C t) := by
      unfold weilPoleKernel
      fun_prop
    exact hc.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht : 0 < t := ht
    have hP : 0 ≤ weilPoleKernel t := by unfold weilPoleKernel; positivity
    have hPb : weilPoleKernel t ≤ 2 * Real.exp t := by
      have h1 : Real.exp (t / 2) ≤ Real.exp t := Real.exp_le_exp.mpr (by linarith)
      have h2 : Real.exp (-t / 2) ≤ Real.exp t := Real.exp_le_exp.mpr (by linarith)
      unfold weilPoleKernel
      linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hP]
    calc
      weilPoleKernel t * |C t| ≤ (2 * Real.exp t) * (A * Real.exp (-3 * t)) :=
        mul_le_mul hPb (hC t ht.le) (abs_nonneg _) (by positivity)
      _ = (2 * A) * Real.exp (-2 * t) := by
        rw [show (2 * Real.exp t) * (A * Real.exp (-3 * t)) =
          (2 * A) * (Real.exp t * Real.exp (-3 * t)) by ring, ← Real.exp_add]
        congr 2
        ring

theorem integrable_weilGammaKernel_sub_zero (C : ℝ → ℝ) (hCc : Continuous C)
    (K : ℝ) (hK : 0 ≤ K) (hLip : ∀ t, 0 < t → |C t - C 0| ≤ K * t) :
    Integrable (fun t => weilGammaKernel t * (C t - C 0)) positiveMeasure := by
  have hi : Integrable (fun t : ℝ => (4 * K) * Real.exp ((-(1 / 4) : ℝ) * t))
      positiveMeasure :=
    (integrableOn_exp_mul_Ioi (by norm_num : (-(1 / 4) : ℝ) < 0) 0).const_mul (4 * K)
  apply hi.mono'
  · have hm : Measurable (fun t => weilGammaKernel t * (C t - C 0)) := by
      unfold weilGammaKernel
      fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht : 0 < t := ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (weilGammaKernel_nonneg ht)]
    calc
      weilGammaKernel t * |C t - C 0| ≤ weilGammaKernel t * (K * t) :=
        mul_le_mul_of_nonneg_left (hLip t ht) (weilGammaKernel_nonneg ht)
      _ = K * (weilGammaKernel t * t) := by ring
      _ ≤ K * (4 * Real.exp (-t / 4)) :=
        mul_le_mul_of_nonneg_left (weilGammaKernel_mul_self_le ht) hK
      _ = (4 * K) * Real.exp (-(1 / 4) * t) := by
        rw [show -t / 4 = -(1 / 4) * t by ring]
        ring

/-- The gamma integral with its original regulator is genuinely integrable. -/
theorem integrable_weilGammaKernel_regulated (C : ℝ → ℝ) (hCc : Continuous C)
    (K : ℝ) (hK : 0 ≤ K) (hLip : ∀ t, 0 < t → |C t - C 0| ≤ K * t) :
    Integrable (fun t => weilGammaKernel t * (C t - weilRegulator t * C 0))
      positiveMeasure := by
  have hreg : Integrable (fun t => weilGammaKernel t * (1 - weilRegulator t))
      positiveMeasure := by
    apply (integrable_archimedeanCorrection.const_mul (1 / 2 : ℝ)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [archimedeanCorrection_eq_kernel (show 0 < t from ht)]
    ring
  have hi := (integrable_weilGammaKernel_sub_zero C hCc K hK hLip).add
    (hreg.const_mul (C 0))
  apply hi.congr
  apply ae_of_all
  intro t
  dsimp only [Pi.add_apply]
  ring

open RiemannResearch.Analysis

/-- Both pole and gamma integrability obligations are discharged for actual
smooth superexponential test functions, including the subtraction at zero. -/
theorem admissible_realAutocorrelation {f : ℝ → ℂ}
    (hf : SuperexponentialDecay f) (hdf : SuperexponentialDecay (deriv f))
    (hfd : Differentiable ℝ f) :
    AdmissibleCorrelation (realAutocorrelation f) := by
  obtain ⟨K, hK⟩ := hf.exists_crossCorrelation_lipschitz hf hdf hfd hfd.continuous
  have hcorr (t : ℝ) : (crossCorrelation f f t).re = realAutocorrelation f t := by rfl
  have hCc : Continuous (realAutocorrelation f) := by
    exact Complex.continuous_re.comp hK.continuous
  obtain ⟨A, hA, hbound⟩ := hf.crossCorrelation hf hfd.continuous hfd.continuous 3
    (by norm_num)
  have hdec (t : ℝ) (ht : 0 ≤ t) :
      |realAutocorrelation f t| ≤ A * Real.exp (-3 * t) := by
    have hreal : |realAutocorrelation f t| ≤ ‖crossCorrelation f f t‖ :=
      Complex.abs_re_le_norm _
    exact hreal.trans (by simpa only [abs_of_nonneg ht] using hbound t)
  have hLip (t : ℝ) (ht : 0 < t) :
      |realAutocorrelation f t - realAutocorrelation f 0| ≤ (K : ℝ) * t := by
    have hreal : |realAutocorrelation f t - realAutocorrelation f 0| ≤
        ‖crossCorrelation f f t - crossCorrelation f f 0‖ := by
      simpa only [Complex.sub_re, hcorr] using
        Complex.abs_re_le_norm (crossCorrelation f f t - crossCorrelation f f 0)
    exact hreal.trans (by
      simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_pos ht] using hK.dist_le_mul t 0)
  exact ⟨integrable_weilPoleKernel_mul_of_exp_decay _ hCc A hA.le hdec,
    integrable_weilGammaKernel_regulated _ hCc K K.coe_nonneg hLip⟩

end
end RiemannResearch.RH.SignedWeilCorrelation
