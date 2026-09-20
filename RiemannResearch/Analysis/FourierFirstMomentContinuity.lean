import RiemannResearch.Analysis.FourierL1L2Plancherel
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.FunProp

/-!
# Frequency-domain first moments give continuous inverse transforms

Source: the standard one-dimensional Fourier--Sobolev continuity argument,
used in the user-provided Hilbert--Pólya discussion of September 20, 2026.
Instead of introducing a Sobolev space, the proof factors an L2 function
through `x + I`.  If `F` and `x * F` are in L2, then `(x + I) * F` and
`1 / (x + I)` are in L2, so Hölder gives `F ∈ L1`.  Its inverse Fourier
integral supplies a continuous representative.
-/

noncomputable section
open MeasureTheory FourierTransform SchwartzMap
open scoped SchwartzMap

namespace RiemannResearch.Analysis

private theorem frequency_add_I_ne_zero (t : ℝ) : (t : ℂ) + Complex.I ≠ 0 := by
  intro he
  have him := congrArg Complex.im he
  simpa using him

theorem reciprocal_frequency_memLp :
    MemLp (fun t : ℝ => ((t : ℂ) + Complex.I)⁻¹) 2 := by
  have hm : Measurable (fun t : ℝ => ((t : ℂ) + Complex.I)⁻¹) := by fun_prop
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  have he : (fun t : ℝ => ‖((t : ℂ) + Complex.I)⁻¹‖ ^ 2) =
      (fun t : ℝ => (1 + t ^ 2)⁻¹) := by
    funext t
    rw [norm_inv, inv_pow, Complex.sq_norm]
    simp [Complex.normSq_apply, pow_two, add_comm]
  rw [he]
  exact integrable_inv_one_add_sq

/-- A square-integrable function with square-integrable frequency product
is integrable. No pointwise regularity of the function is assumed. -/
theorem integrable_of_memLp_and_frequency_memLp {F : ℝ → ℂ}
    (hF : MemLp F 2) (hFreq : MemLp (fun t : ℝ => (t : ℂ) * F t) 2) :
    Integrable F := by
  have hsum : MemLp (fun t : ℝ => ((t : ℂ) + Complex.I) * F t) 2 := by
    have he : (fun t : ℝ => ((t : ℂ) + Complex.I) * F t) =
        (fun t : ℝ => (t : ℂ) * F t) + (fun t : ℝ => Complex.I * F t) := by
      funext t
      exact add_mul (t : ℂ) Complex.I (F t)
    rw [he]
    exact hFreq.add (hF.const_mul Complex.I)
  apply (hsum.integrable_mul reciprocal_frequency_memLp).congr
  exact Filter.Eventually.of_forall (fun t : ℝ => by
    dsimp only [Pi.mul_apply]
    field_simp [frequency_add_I_ne_zero t])

theorem integral_fourierInv_mul_eq_of_integrable {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    (∫ x, 𝓕⁻ f x * g x) = ∫ x, f x * 𝓕⁻ g x := by
  calc
    _ = ∫ x, 𝓕 f (-x) * g x := by simp_rw [Real.fourierInv_eq_fourier_neg]
    _ = ∫ x, 𝓕 f x * g (-x) := by
      simpa only [neg_neg] using
        integral_neg_eq_self (fun x : ℝ => 𝓕 f x * g (-x)) volume
    _ = ∫ x, f x * 𝓕 (fun y => g (-y)) x :=
      integral_fourier_mul_eq_of_integrable hf hg.comp_neg
    _ = _ := by rw [← Real.fourierInv_eq_fourier_comp_neg]

theorem continuous_fourierInv_of_integrable {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (𝓕⁻ f) := by
  rw [Real.fourierInv_eq_fourier_comp_neg]
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hf.comp_neg

/-- The ordinary inverse Fourier integral agrees a.e. with the unitary
inverse L2 Fourier transform.  This is the inverse counterpart of the
existing `fourier_toLp_ae_eq_of_integrable` theorem. -/
theorem fourierInv_toLp_ae_eq_of_integrable {f : ℝ → ℂ}
    (hf1 : Integrable f) (hf2 : MemLp f 2) :
    (fun x => (𝓕⁻ (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) x) =ᵐ[volume]
      𝓕⁻ f := by
  have hcont : Continuous (𝓕⁻ f) := continuous_fourierInv_of_integrable hf1
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕⁻ (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ))).locallyIntegrable
      (by norm_num))
    hcont.locallyIntegrable
  intro g hg hc
  have hgc : HasCompactSupport (Complex.ofRealCLM ∘ g) := hc.comp_left rfl
  have hgs := Complex.ofRealCLM.contDiff.comp hg
  let φ : SchwartzMap ℝ ℂ := hgc.toSchwartzMap hgs
  have hdist : (∫ x, (𝓕⁻ φ) x • f x) =
      ∫ x, φ x • (𝓕⁻ (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) x := by
    calc
      _ = ∫ x, (𝓕⁻ φ) x • (hf2.toLp f) x := by
        apply integral_congr_ae
        filter_upwards [hf2.coeFn_toLp] with x hx
        rw [hx]
      _ = (𝓕⁻ ((hf2.toLp f) : TemperedDistribution ℝ ℂ)) φ := by
        rw [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply]
      _ = _ := by
        rw [Lp.fourierInv_toTemperedDistribution_eq, Lp.toTemperedDistribution_apply]
  calc
    _ = ∫ x, φ x • (𝓕⁻ (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) x := by simp [φ]
    _ = ∫ x, (𝓕⁻ φ) x • f x := hdist.symm
    _ = ∫ x, φ x • 𝓕⁻ f x := by
      simpa only [SchwartzMap.fourierInv_coe, smul_eq_mul] using
        integral_fourierInv_mul_eq_of_integrable φ.integrable hf1
    _ = _ := by simp [φ]

/-- Finite frequency-domain first moment supplies a continuous representative
of an L2 function. This is a proved analytic bridge, not a provider hypothesis. -/
theorem exists_continuous_ae_eq_of_frequency_memLp
    (h : Lp ℂ 2 (volume : Measure ℝ))
    (hFreq : MemLp (fun t : ℝ =>
      (t : ℂ) * (𝓕 h : Lp ℂ 2 (volume : Measure ℝ)) t) 2) :
    ∃ g : ℝ → ℂ, Continuous g ∧ g =ᵐ[volume] h := by
  let F : Lp ℂ 2 (volume : Measure ℝ) := 𝓕 h
  have hF1 : Integrable (fun t => F t) :=
    integrable_of_memLp_and_frequency_memLp (Lp.memLp F) hFreq
  have hto : (Lp.memLp F).toLp (fun t => F t) = F := by
    apply Lp.ext
    exact (Lp.memLp F).coeFn_toLp
  have hInv := fourierInv_toLp_ae_eq_of_integrable hF1 (Lp.memLp F)
  rw [hto] at hInv
  change (fun x => (𝓕⁻ (𝓕 h) : Lp ℂ 2 (volume : Measure ℝ)) x) =ᵐ[volume]
    𝓕⁻ (fun t => F t) at hInv
  rw [fourierInv_fourier_eq] at hInv
  exact ⟨𝓕⁻ (fun t => F t), continuous_fourierInv_of_integrable hF1, hInv.symm⟩

end RiemannResearch.Analysis
