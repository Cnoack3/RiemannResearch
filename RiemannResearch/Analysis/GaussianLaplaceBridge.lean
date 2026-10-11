/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
Infinite Gaussian-to-resolvent exchange for arbitrary countable weighted
complex rates with positive real part. The input is only the summability
of the exact absolute integral majorant; no pointwise positivity or RH
is assumed. Natural-number weights retain all analytic multiplicities.
Source: the scalar integrals and absolute Fubini exchange use Mathlib's
Analysis.SpecialFunctions.ImproperIntegrals and MeasureTheory.Integral.DominatedConvergence.
The signed assembly is independently developed for the Gaussian defect.
-/

noncomputable section
open MeasureTheory Set Complex ENNReal
open scoped BigOperators ENNReal

namespace RiemannResearch.Analysis.GaussianLaplaceBridge

def exponentialKernel (m : ℕ) (z : ℂ) (t : ℝ) : ℂ :=
  (m : ℂ) * Complex.exp (-z * (t : ℂ))

theorem exponentialKernel_integrable (m : ℕ) (z : ℂ) (hz : 0 < z.re) :
    IntegrableOn (exponentialKernel m z) (Ioi 0) := by
  exact (integrableOn_exp_mul_complex_Ioi (a := -z) (by simpa using hz) 0).const_mul _

theorem exponentialKernel_integral (m : ℕ) (z : ℂ) (hz : 0 < z.re) :
    (∫ t : ℝ in Ioi 0, exponentialKernel m z t) = (m : ℂ) / z := by
  unfold exponentialKernel
  rw [integral_const_mul, integral_exp_mul_complex_Ioi (a := -z) (by simpa using hz) 0]
  simp [div_eq_mul_inv]

theorem exponentialKernel_integral_norm (m : ℕ) (z : ℂ) (hz : 0 < z.re) :
    (∫ t : ℝ in Ioi 0, ‖exponentialKernel m z t‖) = (m : ℝ) / z.re := by
  simp only [exponentialKernel, norm_mul, Complex.norm_natCast, Complex.norm_exp,
    Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  rw [integral_const_mul, integral_exp_mul_Ioi (a := -z.re) (by linarith) 0]
  simp [div_eq_mul_inv]

theorem infinite_exponential_integral {ι : Type*} [Countable ι]
    (m : ι → ℕ) (z : ι → ℂ) (hz : ∀ i, 0 < (z i).re)
    (hs : Summable (fun i => (m i : ℝ) / (z i).re)) :
    (∫ t : ℝ in Ioi 0, ∑' i, exponentialKernel (m i) (z i) t) =
      ∑' i, (m i : ℂ) / z i := by
  have hint := fun i => exponentialKernel_integrable (m i) (z i) (hz i)
  have hnorm : Summable (fun i => ∫ t : ℝ in Ioi 0,
      ‖exponentialKernel (m i) (z i) t‖) := by
    simpa only [exponentialKernel_integral_norm _ _ (hz _)] using hs
  rw [← integral_tsum_of_summable_integral_norm hint hnorm]
  exact tsum_congr (fun i => exponentialKernel_integral (m i) (z i) (hz i))



theorem exponentialKernel_norm_le (m : ℕ) (z : ℂ) (hz : 0 < z.re)
    {t : ℝ} (ht : 0 < t) :
    ‖exponentialKernel m z t‖ ≤ (1 / t) * ((m : ℝ) / z.re) := by
  have hu : 0 < z.re * t := mul_pos hz ht
  have hexp : z.re * t ≤ Real.exp (z.re * t) :=
    le_trans (by linarith) (Real.add_one_le_exp _)
  have hinv : Real.exp (-(z.re * t)) ≤ (z.re * t)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ hu hexp
  simp only [exponentialKernel, norm_mul, Complex.norm_natCast, Complex.norm_exp,
    Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  calc
    (m : ℝ) * Real.exp (-z.re * t) ≤ (m : ℝ) * (z.re * t)⁻¹ := by
      simpa only [neg_mul] using mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg m)
    _ = (1 / t) * ((m : ℝ) / z.re) := by
      rw [mul_inv_rev]
      ring

theorem exponentialKernel_summable {ι : Type*} (m : ι → ℕ) (z : ι → ℂ)
    (hz : ∀ i, 0 < (z i).re)
    (hs : Summable (fun i => (m i : ℝ) / (z i).re))
    {t : ℝ} (ht : 0 < t) :
    Summable (fun i => exponentialKernel (m i) (z i) t) := by
  have hs' : Summable (fun i => ‖exponentialKernel (m i) (z i) t‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _)
      (fun i => exponentialKernel_norm_le (m i) (z i) (hz i) ht)
      (hs.mul_left (1 / t))
  exact summable_norm_iff.mp hs'

def signedExponentialKernel (m : ℕ) (p q : ℂ) (t : ℝ) : ℂ :=
  exponentialKernel m p t - exponentialKernel m q t

theorem signedExponentialKernel_integrable (m : ℕ) (p q : ℂ)
    (hp : 0 < p.re) (hq : 0 < q.re) :
    IntegrableOn (signedExponentialKernel m p q) (Ioi 0) :=
  (exponentialKernel_integrable m p hp).sub (exponentialKernel_integrable m q hq)

theorem signedExponentialKernel_integral (m : ℕ) (p q : ℂ)
    (hp : 0 < p.re) (hq : 0 < q.re) :
    (∫ t : ℝ in Ioi 0, signedExponentialKernel m p q t) =
      (m : ℂ) / p - (m : ℂ) / q := by
  unfold signedExponentialKernel
  rw [integral_sub
    (exponentialKernel_integrable m p hp) (exponentialKernel_integrable m q hq),
    exponentialKernel_integral m p hp, exponentialKernel_integral m q hq]

theorem signedExponentialKernel_integral_norm_le (m : ℕ) (p q : ℂ)
    (hp : 0 < p.re) (hq : 0 < q.re) :
    (∫ t : ℝ in Ioi 0, ‖signedExponentialKernel m p q t‖) ≤
      (m : ℝ) / p.re + (m : ℝ) / q.re := by
  have hip := exponentialKernel_integrable m p hp
  have hiq := exponentialKernel_integrable m q hq
  calc
    _ ≤ ∫ t : ℝ in Ioi 0,
        (‖exponentialKernel m p t‖ + ‖exponentialKernel m q t‖) :=
      integral_mono (hip.sub hiq).norm (hip.norm.add hiq.norm)
        (fun t => norm_sub_le _ _)
    _ = (∫ t : ℝ in Ioi 0, ‖exponentialKernel m p t‖) +
        (∫ t : ℝ in Ioi 0, ‖exponentialKernel m q t‖) :=
      integral_add hip.norm hiq.norm
    _ = _ := by rw [exponentialKernel_integral_norm m p hp,
      exponentialKernel_integral_norm m q hq]

theorem infinite_signed_exponential_integral {ι : Type*} [Countable ι]
    (m : ι → ℕ) (p q : ι → ℂ)
    (hp : ∀ i, 0 < (p i).re) (hq : ∀ i, 0 < (q i).re)
    (hsp : Summable (fun i => (m i : ℝ) / (p i).re))
    (hsq : Summable (fun i => (m i : ℝ) / (q i).re)) :
    (∫ t : ℝ in Ioi 0, ∑' i, signedExponentialKernel (m i) (p i) (q i) t) =
      ∑' i, ((m i : ℂ) / p i - (m i : ℂ) / q i) := by
  have hint := fun i => signedExponentialKernel_integrable (m i) (p i) (q i)
    (hp i) (hq i)
  have hnorm : Summable (fun i => ∫ t : ℝ in Ioi 0,
      ‖signedExponentialKernel (m i) (p i) (q i) t‖) :=
    Summable.of_nonneg_of_le
      (fun i => integral_nonneg (fun t => norm_nonneg _))
      (fun i => signedExponentialKernel_integral_norm_le (m i) (p i) (q i)
        (hp i) (hq i)) (hsp.add hsq)
  rw [← integral_tsum_of_summable_integral_norm hint hnorm]
  exact tsum_congr (fun i => signedExponentialKernel_integral (m i) (p i) (q i)
    (hp i) (hq i))

/-- Explicit integrability of a countable complex series from its full L1 budget.
The ENNReal proof below follows the norm-integral conversion used by mathlib's
`hasSum_integral_of_summable_integral_norm`. -/
theorem complex_tsum_integrable_of_summable_integral_norm
    {ι α : Type*} [Countable ι] [MeasurableSpace α] {μ : Measure α}
    (F : ι → α → ℂ) (hint : ∀ i, Integrable (F i) μ)
    (hs : Summable (fun i => ∫ a, ‖F i a‖ ∂μ)) :
    Integrable (fun a => ∑' i, F i a) μ := by
  have hfin : (∑' i, ∫⁻ a, ‖F i a‖ₑ ∂μ) ≠ ⊤ := by
    have heq (i : ι) : (∫⁻ a, ‖F i a‖ₑ ∂μ) = ‖∫ a, ‖F i a‖ ∂μ‖ₑ := by
      dsimp [enorm]
      rw [lintegral_coe_eq_integral _ (hint i).norm, coe_nnreal_eq, coe_nnnorm,
        Real.norm_of_nonneg (integral_nonneg (fun a => norm_nonneg (F i a)))]
      rfl
    rw [funext heq]
    apply tsum_enorm_ne_top_iff_summable_norm.mpr
    simpa only [Real.norm_eq_abs] using hs.abs
  refine ⟨(AEMeasurable.tsum (fun i => (hint i).aemeasurable)).aestronglyMeasurable, ?_⟩
  change (∫⁻ a, ‖∑' i, F i a‖ₑ ∂μ) < ⊤
  calc
    _ ≤ ∫⁻ a, ∑' i, ‖F i a‖ₑ ∂μ :=
      lintegral_mono (fun a => enorm_tsum_le_tsum_enorm)
    _ = ∑' i, ∫⁻ a, ‖F i a‖ₑ ∂μ :=
      lintegral_tsum (fun i => (hint i).aestronglyMeasurable.enorm)
    _ < ⊤ := lt_top_iff_ne_top.mpr hfin

theorem infinite_exponential_integrable {ι : Type*} [Countable ι]
    (m : ι → ℕ) (z : ι → ℂ) (hz : ∀ i, 0 < (z i).re)
    (hs : Summable (fun i => (m i : ℝ) / (z i).re)) :
    IntegrableOn (fun t : ℝ => ∑' i, exponentialKernel (m i) (z i) t) (Ioi 0) := by
  apply complex_tsum_integrable_of_summable_integral_norm _
    (fun i => exponentialKernel_integrable (m i) (z i) (hz i))
  have heq : (fun i => ∫ t : ℝ in Ioi 0, ‖exponentialKernel (m i) (z i) t‖) =
      (fun i => (m i : ℝ) / (z i).re) := by
    funext i
    exact exponentialKernel_integral_norm (m i) (z i) (hz i)
  rw [heq]
  exact hs

theorem infinite_signed_exponential_integrable {ι : Type*} [Countable ι]
    (m : ι → ℕ) (p q : ι → ℂ)
    (hp : ∀ i, 0 < (p i).re) (hq : ∀ i, 0 < (q i).re)
    (hsp : Summable (fun i => (m i : ℝ) / (p i).re))
    (hsq : Summable (fun i => (m i : ℝ) / (q i).re)) :
    IntegrableOn (fun t : ℝ => ∑' i,
      signedExponentialKernel (m i) (p i) (q i) t) (Ioi 0) := by
  apply complex_tsum_integrable_of_summable_integral_norm _
    (fun i => signedExponentialKernel_integrable (m i) (p i) (q i) (hp i) (hq i))
  exact Summable.of_nonneg_of_le
    (fun i => integral_nonneg (fun t => norm_nonneg _))
    (fun i => signedExponentialKernel_integral_norm_le (m i) (p i) (q i)
      (hp i) (hq i)) (hsp.add hsq)


/-- The complete reciprocal spectrum is summable, not a totalized divergent tsum. -/
theorem reciprocalRate_summable {ι : Type*}
    (m : ι → ℕ) (z : ι → ℂ) (hz : ∀ i, 0 < (z i).re)
    (hs : Summable (fun i => (m i : ℝ) / (z i).re)) :
    Summable (fun i => (m i : ℂ) / z i) := by
  have hnorm : Summable (fun i => ∫ t : ℝ in Ioi 0,
      ‖exponentialKernel (m i) (z i) t‖) := by
    simpa only [exponentialKernel_integral_norm _ _ (hz _)] using hs
  have hsum := hnorm.of_norm_bounded
    (fun i => norm_integral_le_integral_norm (fun t : ℝ => exponentialKernel (m i) (z i) t))
  simpa only [exponentialKernel_integral _ _ (hz _)] using hsum

end RiemannResearch.Analysis.GaussianLaplaceBridge
