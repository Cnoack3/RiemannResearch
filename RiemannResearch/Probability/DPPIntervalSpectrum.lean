import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Interval spectra and the sine pair density

The Fourier phase uses cycles per unit length. The starting point of the
unit interval affects the kernel by a phase whose norm is one. The overlap
calculation uses a half-open interval so its two endpoints do not require
special cases in the integral.
-/

noncomputable section

open MeasureTheory Set Complex
open scoped FourierTransform Convolution

namespace RiemannResearch.DPPSpectral

/-- The real multiplier given by the unit interval with left endpoint `a`. -/
def intervalMultiplier (a : ℝ) : ℝ → ℝ := (Ioc a (a + 1)).indicator (1 : ℝ → ℝ)

theorem intervalMultiplier_integrable (a : ℝ) : Integrable (intervalMultiplier a) := by
  apply IntegrableOn.integrable_indicator _ measurableSet_Ioc
  exact integrableOn_const (by simp [Real.volume_Ioc])

theorem integral_intervalMultiplier (a : ℝ) : ∫ t, intervalMultiplier a t = 1 := by
  rw [intervalMultiplier, integral_indicator_one measurableSet_Ioc, Real.volume_real_Ioc]
  simp

/-- The autocorrelation of a unit interval, at every real shift. -/
theorem intervalMultiplier_overlap (a h : ℝ) :
    (∫ t, intervalMultiplier a t * intervalMultiplier a (t + h)) = max (1 - |h|) 0 := by
  let J := Ioc (max a (a - h)) (min (a + 1) (a + 1 - h))
  have hJ (t : ℝ) : t ∈ J ↔ t ∈ Ioc a (a + 1) ∧ t + h ∈ Ioc a (a + 1) := by
    simp only [J, mem_Ioc, max_lt_iff, le_min_iff]
    constructor <;> rintro ⟨⟨H₁, H₂⟩, H₃, H₄⟩ <;>
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  rw [show (fun t ↦ intervalMultiplier a t * intervalMultiplier a (t + h)) =
      J.indicator (1 : ℝ → ℝ) by
    funext t
    by_cases ht : t ∈ Ioc a (a + 1) <;> by_cases hs : t + h ∈ Ioc a (a + 1) <;>
      simp [intervalMultiplier, Set.indicator, hJ, ht, hs]]
  rw [integral_indicator_one (s := J) measurableSet_Ioc, Real.volume_real_Ioc]
  by_cases hh : 0 ≤ h
  · rw [abs_of_nonneg hh, max_eq_left (by linarith : a - h ≤ a),
      min_eq_right (by linarith : a + 1 - h ≤ a + 1)]
    congr 1
    ring
  · rw [abs_of_neg (lt_of_not_ge hh), max_eq_right (by linarith : a ≤ a - h),
      min_eq_left (by linarith : a + 1 ≤ a + 1 - h)]
    congr 1
    ring

/-- Exact Fourier integral of the unit interval in the positive-phase convention. -/
theorem interval_fourier_phase (a x : ℝ) :
    (∫ t in a..a + 1, Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * I * t)) =
    Complex.exp (((2 * Real.pi * x * (a + 1 / 2) : ℝ) : ℂ) * I) *
      (Real.sinc (Real.pi * x) : ℂ) := by
  by_cases hx : x = 0
  · subst x; simp
  have hp : Real.pi * x ≠ 0 := mul_ne_zero Real.pi_ne_zero hx
  let z : ℂ := ((Real.pi * x : ℝ) : ℂ)
  let c : ℂ := ((2 * Real.pi * x * (a + 1 / 2) : ℝ) : ℂ) * I
  have hz : z ≠ 0 := Complex.ofReal_ne_zero.mpr hp
  have hd : (((2 * Real.pi * x : ℝ) : ℂ) * I) ≠ 0 := by
    rw [show ((2 * Real.pi * x : ℝ) : ℂ) = 2 * z by dsimp [z]; push_cast; ring]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hz) I_ne_zero
  rw [integral_exp_mul_complex hd, Real.sinc_of_ne_zero hp]
  change (exp _ - exp _) / _ = exp c * (_ : ℂ)
  rw [show ((2 * Real.pi * x : ℝ) : ℂ) * I * ((a + 1 : ℝ) : ℂ) = c + z * I by
      dsimp [z,c]; push_cast; ring,
    show ((2 * Real.pi * x : ℝ) : ℂ) * I * (a : ℂ) = c + (-z * I) by
      dsimp [z,c]; push_cast; ring,
    Complex.exp_add, Complex.exp_add, Complex.exp_mul_I z, Complex.exp_mul_I (-z),
    Complex.cos_neg, Complex.sin_neg, Complex.ofReal_div, Complex.ofReal_sin]
  change _ = _ * (Complex.sin z / z)
  rw [show ((2 * Real.pi * x : ℝ) : ℂ) * I = 2 * z * I by dsimp [z]; push_cast; ring]
  field_simp
  ring

/-- The second factorial density of a unit-intensity continuous convolution DPP
with this interval multiplier. -/
theorem interval_fourier_pair (a x : ℝ) :
    1 - ‖∫ t in a..a + 1, Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * I * t)‖ ^ 2 =
    1 - Real.sinc (Real.pi * x) ^ 2 := by
  rw [interval_fourier_phase, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Overlap is convolution with the reflected real multiplier. -/
theorem overlap_as_convolution (f : ℝ → ℝ) (h : ℝ) :
    ((fun t ↦ f (-t)) ⋆[ContinuousLinearMap.mul ℝ ℝ] f) h =
      ∫ t, f t * f (t + h) := by
  rw [convolution_def]
  simpa [sub_eq_add_neg, add_comm, ContinuousLinearMap.mul_apply'] using
    (integral_neg_eq_self (fun t ↦ f t * f (t + h)) volume)

theorem unitTent_integrable : Integrable (fun h : ℝ ↦ max (1 - |h|) 0) := by
  have eqn := funext fun h ↦ (overlap_as_convolution (intervalMultiplier 0) h).trans
    (intervalMultiplier_overlap 0 h)
  rw [← eqn]
  exact (intervalMultiplier_integrable 0).comp_neg.integrable_convolution _
    (intervalMultiplier_integrable 0)

theorem integral_unitTent : (∫ h : ℝ, max (1 - |h|) 0) = 1 := by
  have eqn := funext fun h ↦ (overlap_as_convolution (intervalMultiplier 0) h).trans
    (intervalMultiplier_overlap 0 h)
  rw [← eqn, integral_convolution _ (intervalMultiplier_integrable 0).comp_neg
    (intervalMultiplier_integrable 0), integral_neg_eq_self, integral_intervalMultiplier]
  simp

private theorem complexOverlap (f : ℝ → ℝ) (h : ℝ) :
    ((fun t ↦ (f (-t) : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ] (fun t ↦ (f t : ℂ))) h =
      (((∫ t, f t * f (t + h)) : ℝ) : ℂ) := by
  rw [convolution_def, ← integral_complex_ofReal]
  simpa [sub_eq_add_neg, add_comm, ContinuousLinearMap.mul_apply', Complex.ofReal_mul] using
    (integral_neg_eq_self (fun t ↦ ((f t * f (t + h) : ℝ) : ℂ)) volume)

private theorem fourier_reflect (f : ℝ → ℝ) (x : ℝ) :
    𝓕 (fun t ↦ (f (-t) : ℂ)) x = (starRingEnd ℂ) (𝓕 (fun t ↦ (f t : ℂ)) x) := by
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  rw [← integral_conj]
  rw [← integral_neg_eq_self (fun t ↦ (starRingEnd ℂ)
    (exp (((-2 * Real.pi * t * x : ℝ) : ℂ) * I) * (f t : ℂ))) volume]
  apply integral_congr_ae
  filter_upwards with t
  simp [← Complex.exp_conj, map_mul]
  ring_nf
  exact Or.inl (by rw [map_ofNat (starRingEnd ℂ) 2])

/-- The Fourier transform of the overlap gives the square of the kernel norm.
This identity holds for every real integrable multiplier. -/
theorem fourier_overlap (f : ℝ → ℝ) (hf : Integrable f) (x : ℝ) :
    𝓕 (fun h ↦ (((∫ t, f t * f (t + h)) : ℝ) : ℂ)) x = (‖𝓕 (fun t ↦ (f t : ℂ)) x‖ ^ 2 : ℝ) := by
  have hfor : Integrable (fun t : ℝ ↦ (f (-t) : ℂ)) := hf.comp_neg.ofReal
  have hpos : Integrable (fun t : ℝ ↦ (f t : ℂ)) := hf.ofReal
  rw [← funext (complexOverlap f), Real.fourier_mul_convolution_eq
    (f₁ := fun t ↦ (f (-t) : ℂ)) (f₂ := fun t ↦ (f t : ℂ)) hfor hpos,
    fourier_reflect, Complex.conj_mul']
  all_goals norm_cast

/-- The standard Fourier kernel of a translated interval, expressed in the
positive-phase convention by evaluation at -x. -/
theorem fourier_intervalMultiplier (a x : ℝ) :
    𝓕 (fun t ↦ (intervalMultiplier a t : ℂ)) (-x) =
      ∫ t in a..a + 1, Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * I * t) := by
  rw [Real.fourier_real_eq_integral_exp_smul, intervalIntegral.integral_of_le (by linarith)]
  rw [← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : t ∈ Ioc a (a + 1)
  · simp [intervalMultiplier, Set.indicator_of_mem ht, smul_eq_mul]
    congr 1
    ring
  · simp [intervalMultiplier, Set.indicator_of_notMem ht]

/-- Fourier kernel with the phase retained for a multiplier equal almost
everywhere to an open unit interval. -/
theorem fourier_of_interval_ae {f : ℝ → ℝ} {a : ℝ}
    (hf : f =ᵐ[volume] (Ioo a (a + 1)).indicator (1 : ℝ → ℝ)) (x : ℝ) :
    𝓕 (fun t ↦ (f t : ℂ)) (-x) =
      Complex.exp (((2 * Real.pi * x * (a + 1 / 2) : ℝ) : ℂ) * I) *
        (Real.sinc (Real.pi * x) : ℂ) := by
  have he : (fun t ↦ (f t : ℂ)) =ᵐ[volume] (fun t ↦ (intervalMultiplier a t : ℂ)) := by
    filter_upwards [hf, (Ioo_ae_eq_Ioc (μ := volume) (a := a) (b := a + 1))] with t ht he
    rw [ht]
    change (t ∈ Ioo a (a + 1)) = (t ∈ Ioc a (a + 1)) at he
    simp [intervalMultiplier, Set.indicator, he]
  rw [Real.fourier_congr_ae he, fourier_intervalMultiplier, interval_fourier_phase]

/-- Sine pair density for a multiplier equal almost everywhere to a unit interval. -/
theorem fourier_pair_of_interval_ae {f : ℝ → ℝ} {a : ℝ}
    (hf : f =ᵐ[volume] (Ioo a (a + 1)).indicator (1 : ℝ → ℝ)) (x : ℝ) :
    1 - ‖𝓕 (fun t ↦ (f t : ℂ)) (-x)‖ ^ 2 = 1 - Real.sinc (Real.pi * x) ^ 2 := by
  rw [fourier_of_interval_ae hf, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Almost-everywhere triangular overlap identifies the full pair density,
without any hypothesis about reconstruction of the Fourier phase. -/
theorem fourier_pair_of_triangle_ae {f : ℝ → ℝ} (hf : Integrable f)
    (ht : ∀ᵐ h : ℝ, (∫ t, f t * f (t + h)) = max (1 - |h|) 0) (x : ℝ) :
    1 - ‖𝓕 (fun t ↦ (f t : ℂ)) (-x)‖ ^ 2 = 1 - Real.sinc (Real.pi * x) ^ 2 := by
  have hEq := Real.fourier_congr_ae (f₁ := fun h ↦ (((∫ t, f t * f (t + h)) : ℝ) : ℂ))
    (f₂ := fun h ↦ (((∫ t, intervalMultiplier 0 t * intervalMultiplier 0 (t + h)) : ℝ) : ℂ))
    (by filter_upwards [ht] with h hh; rw [hh, intervalMultiplier_overlap]) (-x)
  rw [fourier_overlap f hf, fourier_overlap _ (intervalMultiplier_integrable 0)] at hEq
  have hReal : ‖𝓕 (fun t ↦ (f t : ℂ)) (-x)‖ ^ 2 =
      ‖𝓕 (fun t ↦ (intervalMultiplier 0 t : ℂ)) (-x)‖ ^ 2 := by exact_mod_cast hEq
  rw [hReal, fourier_intervalMultiplier, interval_fourier_pair]

end RiemannResearch.DPPSpectral
