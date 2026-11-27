import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Cosine inversion at the zeta unfolding scale

Mathlib's Schwartz Fourier inversion, symmetrized at opposite arguments,
supplies the real weight and the inversion identity in the positive-gap
rounding bound. This works for every even real part of a complex Schwartz test.
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff

namespace RiemannResearch.Analysis.MontgomeryEvenFourierTests

/-- The real part of the Schwartz Fourier transform is an integrable weight. -/
theorem integrable_schwartz_weight (f : 𝓢(ℝ, ℂ)) :
    Integrable (fun v => ((𝓕 f) v).re) :=
  (𝓕 f).integrable.re

/-- Symmetric pointwise inversion discards the odd sine term. -/
theorem even_schwartz_cosine_inversion (f : 𝓢(ℝ, ℂ))
    (heven : ∀ x, (f (-x)).re = (f x).re) (x : ℝ) :
    (f x).re = ∫ v, ((𝓕 f) v).re * Real.cos (2 * Real.pi * (x * v)) := by
  let g : ℝ → ℂ := ⇑(𝓕 f : 𝓢(ℝ, ℂ))
  let P (y v : ℝ) := Real.fourierChar (y * v) • g v
  have hint (y : ℝ) : Integrable (P y) := by
    simpa [P, Real.inner_apply] using
      (Real.fourierIntegral_convergent_iff (-y)).mpr (𝓕 f).integrable
  have hinv (y : ℝ) : (f y).re = ∫ v, (P y v).re := by
    have ht : f y = (𝓕⁻ g : ℝ → ℂ) y := by
      exact (congrArg (fun s : 𝓢(ℝ, ℂ) => s y)
        (FourierTransform.fourierInv_fourier_eq f)).symm.trans
          (congrFun (SchwartzMap.fourierInv_coe (𝓕 f)) y)
    rw [ht, Real.fourierInv_eq]
    exact (integral_re (hint y)).symm
  have hpoint (v : ℝ) : (P x v).re + (P (-x) v).re =
      2 * (g v).re * Real.cos (2 * Real.pi * (x * v)) := by
    simp only [P, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, Complex.mul_re,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, neg_mul, mul_neg,
      Real.cos_neg, Real.sin_neg]
    ring
  have hsum : (f x).re + (f x).re =
      2 * ∫ v, (g v).re * Real.cos (2 * Real.pi * (x * v)) := by
    calc
      _ = (∫ v, (P x v).re) + ∫ v, (P (-x) v).re := by rw [← hinv, ← hinv, heven]
      _ = ∫ v, ((P x v).re + (P (-x) v).re) := (integral_add (hint x).re (hint (-x)).re).symm
      _ = ∫ v, 2 * ((g v).re * Real.cos (2 * Real.pi * (x * v))) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun v => (hpoint v).trans (mul_assoc _ _ _)
      _ = _ := integral_const_mul _ _
  change (f x).re = ∫ v, (g v).re * _
  linarith only [hsum]

/-- At the physical scale log(T)/(2π) the phase equals d log(T) v. -/
theorem unfolded_even_schwartz_inversion (f : 𝓢(ℝ, ℂ))
    (heven : ∀ x, (f (-x)).re = (f x).re) (T d : ℝ) :
    (f (Real.log T / (2 * Real.pi) * d)).re =
      ∫ v, ((𝓕 f) v).re * Real.cos (d * (Real.log T * v)) := by
  rw [even_schwartz_cosine_inversion f heven]
  apply integral_congr_ae
  filter_upwards with v
  congr 2
  field_simp [Real.pi_ne_zero]

/-- A genuine real-valued smooth compactly supported test gives the real part
of its ordinary Fourier transform as the weight at every unfolding height. -/
theorem compact_smooth_even_fourier_test (f : ℝ → ℝ) (hc : HasCompactSupport f)
    (hs : ContDiff ℝ ∞ f) (heven : ∀ x, f (-x) = f x) :
    let w := fun v : ℝ => (𝓕 (fun x => (f x : ℂ)) v).re
    Integrable w ∧ ∀ T d : ℝ, f (Real.log T / (2 * Real.pi) * d) =
      ∫ v, w v * Real.cos (d * (Real.log T * v)) := by
  let c : ℝ → ℂ := Complex.ofRealCLM ∘ f
  have hsupport : HasCompactSupport c := hc.comp_left rfl
  have hsmooth : ContDiff ℝ ∞ c := Complex.ofRealCLM.contDiff.comp hs
  let g := hsupport.toSchwartzMap hsmooth
  have hg (x : ℝ) : (g x).re = f x := rfl
  have hsym (x : ℝ) : (g (-x)).re = (g x).re := by simpa only [hg] using heven x
  exact ⟨integrable_schwartz_weight g, unfolded_even_schwartz_inversion g hsym⟩

end RiemannResearch.Analysis.MontgomeryEvenFourierTests
