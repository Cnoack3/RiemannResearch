import RiemannResearch.Analysis.FourierL1L2Plancherel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-! # A finite-difference bound on the frequency moment

At bandwidth `A`, a translation through `1 / (4 * A)` controls the whole
frequency interval by Jordan's sine inequality. For the strong-PNT application,
`f` is the centered logarithmic remainder cut off at `log T`.
-/

noncomputable section
namespace RiemannResearch.Analysis.MontgomeryPrimeTrace

open Filter MeasureTheory Set
open scoped FourierTransform RealInnerProductSpace ENNReal

private theorem fourier_sub_translate (f : ℝ → ℂ) (hf : Integrable f) (h u : ℝ) :
    𝓕 (fun x => f (x+h) - f x) u =
      ((Real.fourierChar (h*u) : ℂ) - 1) * 𝓕 f u := by
  let g : ℝ → ℂ := fun x => f (x+h)
  have hg : Integrable g := hf.comp_add_right h
  have he : 𝓕 (fun x => g x - f x) u = 𝓕 g u - 𝓕 f u := by
    simp only [Real.fourier_eq, smul_sub]
    exact integral_sub ((Real.fourierIntegral_convergent_iff u).mpr hg)
      ((Real.fourierIntegral_convergent_iff u).mpr hf)
  have ht := congrFun (VectorFourier.fourierIntegral_comp_add_right
    Real.fourierChar volume (innerₗ ℝ) f h) u
  change 𝓕 g u = Real.fourierChar (u*h) • 𝓕 f u at ht
  rw [mul_comm u h, Circle.smul_def, smul_eq_mul] at ht
  change 𝓕 (fun x => g x - f x) u = _
  rw [he, ht]
  ring

private theorem le_fourierChar_sub_one {A u : ℝ} (hA : 0 < A)
    (hu : u ∈ Icc 0 A) :
    u / A ≤ ‖(Real.fourierChar (1 / (4*A) * u) : ℂ) - 1‖ := by
  have hratio : u / A ≤ 1 := (div_le_one hA).2 hu.2
  have hs := Real.le_sin_mul (div_nonneg hu.1 hA.le) hratio
  have he : 2 * Real.pi * (1 / (4*A) * u) = Real.pi / 2 * (u / A) := by
    field_simp [hA.ne'] <;> ring
  apply hs.trans
  have him := Complex.abs_im_le_norm ((Real.fourierChar (1 / (4*A) * u) : ℂ) - 1)
  rw [Complex.sub_im, Complex.one_im, sub_zero, Real.fourierChar_apply,
    Complex.exp_ofReal_mul_I_im, he] at him
  rw [Real.fourierChar_apply, he]
  exact (le_abs_self _).trans him

/-- The truncated second Fourier moment costs at most `C*A/4` if the squared
translation difference at `1/(4A)` costs at most `C/(4A)`. -/
theorem fourier_frequencyMoment_le_of_translation {f : ℝ → ℂ} (hf : Integrable f)
    (hf₂ : MemLp f 2) {A C : ℝ} (hA : 0 < A)
    (htrans : (∫ x : ℝ, ‖f (x + 1/(4*A)) - f x‖ ^ 2) ≤ C / (4*A)) :
    (∫ u in (0 : ℝ)..A, u ^ 2 * ‖𝓕 f u‖ ^ 2) ≤ C*A/4 := by
  let h := 1/(4*A)
  let d := fun x : ℝ => f (x+h) - f x
  have hd : Integrable d := (hf.comp_add_right h).sub hf
  have hd₂ : MemLp d 2 := (hf₂.comp_measurePreserving
    (measurePreserving_add_right (volume : Measure ℝ) h)).sub hf₂
  have hF (g : ℝ → ℂ) (hg : Integrable g) : Continuous (𝓕 g) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hg
  have hF₂ : MemLp (𝓕 d) 2 :=
    (Lp.memLp (𝓕 (hd₂.toLp d) : Lp ℂ 2 (volume : Measure ℝ))).ae_eq
      (RiemannResearch.Analysis.fourier_toLp_ae_eq_of_integrable hd hd₂)
  have hFi := (memLp_two_iff_integrable_sq_norm hF₂.1).mp hF₂
  have hband : (∫ u in (0 : ℝ)..A, ‖𝓕 d u‖ ^ 2) ≤ C/(4*A) := by
    rw [intervalIntegral.integral_of_le hA.le]
    exact (setIntegral_le_integral hFi (Eventually.of_forall fun u => sq_nonneg _)).trans
      ((RiemannResearch.Analysis.integral_norm_sq_fourier_of_integrable hd hd₂).le.trans htrans)
  have hp (u : ℝ) (hu : u ∈ Icc 0 A) : u^2 * ‖𝓕 f u‖^2 ≤ A^2 * ‖𝓕 d u‖^2 := by
    have hh := (div_le_iff₀ hA).mp (le_fourierChar_sub_one hA hu)
    have hi := mul_le_mul_of_nonneg_right hh (norm_nonneg (𝓕 f u))
    have hsq := pow_le_pow_left₀ (mul_nonneg hu.1 (norm_nonneg _)) hi 2
    rw [show 𝓕 d u = ((Real.fourierChar (h*u) : ℂ) - 1) * 𝓕 f u from
      fourier_sub_translate f hf h u, norm_mul]
    dsimp [h]
    nlinarith only [hsq]
  have hm := intervalIntegral.integral_mono_on (μ := volume) hA.le
    (((continuous_id.pow 2).mul ((hF f hf).norm.pow 2)).intervalIntegrable 0 A)
    ((continuous_const.mul ((hF d hd).norm.pow 2)).intervalIntegrable 0 A) hp
  change (∫ u in (0 : ℝ)..A, u^2 * ‖𝓕 f u‖^2) ≤
    ∫ u in (0 : ℝ)..A, A^2 * ‖𝓕 d u‖^2 at hm
  rw [intervalIntegral.integral_const_mul] at hm
  calc
    _ ≤ A^2 * (∫ u in (0 : ℝ)..A, ‖𝓕 d u‖^2) := hm
    _ ≤ A^2 * (C / (4*A)) := mul_le_mul_of_nonneg_left hband (sq_nonneg _)
    _ = _ := by field_simp [hA.ne'] <;> ring

#print axioms fourier_frequencyMoment_le_of_translation

end RiemannResearch.Analysis.MontgomeryPrimeTrace
