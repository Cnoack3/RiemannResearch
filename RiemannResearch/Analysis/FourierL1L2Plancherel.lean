import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Ordinary-integral Plancherel on the real line

Connects Mathlib's Fourier transform on L2 to the ordinary Fourier integral
for L1 ∩ L2 functions, via its tempered-distribution identity and test-function
uniqueness. No square-integrability hypothesis on the transformed integral
is required.
-/

open MeasureTheory FourierTransform SchwartzMap
open scoped SchwartzMap
noncomputable section

namespace RiemannResearch.Analysis

/-- For two integrable complex functions the ordinary Fourier integral is symmetric
under the bilinear integral pairing. -/
theorem integral_fourier_mul_eq_of_integrable {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    (∫ x, 𝓕 f x * g x) = ∫ x, f x * 𝓕 g x := by
  simpa using! VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (ContinuousLinearMap.mul ℂ ℂ) (L := innerₗ ℝ)
    Real.continuous_fourierChar continuous_inner hf hg

/-- Agreement of the actual convergent Fourier integral with the unitary L2
Fourier transform. No prior square-integrability of the Fourier integral is assumed. -/
theorem fourier_toLp_ae_eq_of_integrable {f : ℝ → ℂ}
    (hf1 : Integrable f) (hf2 : MemLp f 2) :
    (fun x => (𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) x) =ᵐ[volume] 𝓕 f := by
  have hcont : Continuous (𝓕 f) := by
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf1
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ))).locallyIntegrable (by norm_num))
    hcont.locallyIntegrable
  intro g hg hc
  have hgc : HasCompactSupport (Complex.ofRealCLM ∘ g) := hc.comp_left rfl
  have hgs := Complex.ofRealCLM.contDiff.comp hg
  let φ : SchwartzMap ℝ ℂ := hgc.toSchwartzMap hgs
  have hdist : (∫ x, (𝓕 φ) x • f x) =
      ∫ x, φ x • (𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) x := by
    calc
      _ = ∫ x, (𝓕 φ) x • (hf2.toLp f) x := by
        apply integral_congr_ae
        filter_upwards [hf2.coeFn_toLp] with x hx
        rw [hx]
      _ = (𝓕 ((hf2.toLp f) : TemperedDistribution ℝ ℂ)) φ := by
        rw [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply]
      _ = _ := by
        rw [Lp.fourier_toTemperedDistribution_eq, Lp.toTemperedDistribution_apply]
  calc
    _ = ∫ x, φ x • (𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) x := by simp [φ]
    _ = ∫ x, (𝓕 φ) x • f x := hdist.symm
    _ = ∫ x, φ x • 𝓕 f x := by
      simpa only [SchwartzMap.fourier_coe, smul_eq_mul] using
        integral_fourier_mul_eq_of_integrable φ.integrable hf1
    _ = _ := by simp [φ]

private theorem lp_integral_norm_sq (u : Lp ℂ 2 (volume : Measure ℝ)) :
    (∫ x, ‖u x‖^2) = ‖u‖^2 := by
  have h := L2.inner_def (𝕜 := ℂ) u u
  simp only [inner_self_eq_norm_sq_to_K] at h
  norm_cast at h
  exact h.symm

/-- Full ordinary-integral Plancherel theorem for L1∩L2 functions on the real line. -/
theorem integral_norm_sq_fourier_of_integrable {f : ℝ → ℂ}
    (hf1 : Integrable f) (hf2 : MemLp f 2) :
    (∫ ξ, ‖𝓕 f ξ‖^2) = ∫ x, ‖f x‖^2 := by
  have he := fourier_toLp_ae_eq_of_integrable hf1 hf2
  calc
    _ = ∫ ξ, ‖(𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) ξ‖^2 := by
      apply integral_congr_ae
      filter_upwards [he] with ξ hξ
      rw [hξ]
    _ = ‖(𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ))‖^2 := lp_integral_norm_sq _
    _ = ‖(hf2.toLp f)‖^2 := by rw [Lp.norm_fourier_eq]
    _ = ∫ x, ‖(hf2.toLp f) x‖^2 := (lp_integral_norm_sq _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hf2.coeFn_toLp] with x hx
      rw [hx]

end RiemannResearch.Analysis
