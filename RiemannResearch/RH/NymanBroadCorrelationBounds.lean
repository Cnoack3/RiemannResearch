import RiemannResearch.RH.NymanBroadFamilyBounds
import RiemannResearch.Analysis.RealKernelCorrelationBounds
import RiemannResearch.RH.AutocorrelationHalfMass

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Uniform bounds for the actual broad autocorrelations

The actual normalized arithmetic profiles have uniformly bounded correlation
variation and a uniform quadratic displacement at the origin. Both facts are
derived from the actual profile derivatives. The correlation mass is exactly
one-half the actual mean squared, with full Fubini and evenness justification.
-/

open MeasureTheory Set Filter
open scoped Topology
namespace RiemannResearch.RH
open RiemannResearch.Analysis

noncomputable def nymanBroadCorrelation (n : ℕ) (φ : ℝ → ℝ) (R : ℝ) : ℝ → ℝ :=
  SignedWeilCorrelation.realAutocorrelation (fun x => (nymanBroadProfile n φ R x : ℂ))

theorem realAutocorrelation_ofReal_eq_realKernelCorrelation (f : ℝ → ℝ) :
    SignedWeilCorrelation.realAutocorrelation (fun x => (f x : ℂ)) =
      realKernelCorrelation f f := by
  funext t
  change (∫y,(f (y+t):ℂ)*star (f y:ℂ)).re = ∫y,f (y+t)*f y
  simp only [Complex.star_def,Complex.conj_ofReal,←Complex.ofReal_mul]
  rw [integral_complex_ofReal]
  simp only [Complex.ofReal_re]

theorem nymanBroadCorrelation_eq_realKernel (n : ℕ) (φ : ℝ → ℝ) (R : ℝ) :
    nymanBroadCorrelation n φ R =
      realKernelCorrelation (nymanBroadProfile n φ R) (nymanBroadProfile n φ R) :=
  realAutocorrelation_ofReal_eq_realKernelCorrelation _

theorem integral_realKernelCorrelation_self_Ioi (f : ℝ → ℝ)
    (hf : Integrable f) (hfc : Continuous f) :
    (∫t in Ioi 0,realKernelCorrelation f f t) = (∫x,f x)^2/2 := by
  rw [integral_Ioi_zero_eq_half_of_even _
    (integrable_realKernelCorrelation f f hf hf hfc) (realKernelCorrelation_self_neg f)]
  congr 1
  rw [realKernelCorrelation_eq_scaledKernelConvolution,
    integral_scaledKernelConvolution _ _ hf.comp_neg hf hfc,
    integral_neg_eq_self f volume,pow_two]

theorem integral_nymanBroadCorrelation_Ioi (n : ℕ) (φ : ℝ → ℝ) (R : ℝ)
    (hf : Integrable (nymanBroadProfile n φ R))
    (hfc : Continuous (nymanBroadProfile n φ R)) :
    (∫t in Ioi 0,nymanBroadCorrelation n φ R t) =
      (∫x,nymanBroadProfile n φ R x)^2/2 := by
  rw [nymanBroadCorrelation_eq_realKernel]
  exact integral_realKernelCorrelation_self_Ioi _ hf hfc

/-- All correlation hypotheses needed for the square variation error and the
gamma/higher-power quadratic errors hold uniformly in the actual broad family. -/
theorem eventually_nymanBroadCorrelation_uniform_bounds (n : ℕ) (hn : 2≤n)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (hc : HasCompactSupport φ) (hmass : (∫x,φ x) ≠ 0) :
    ∃ V B : ℝ, 0≤V ∧ 0≤B ∧ ∀ᶠ R : ℝ in atTop,
      Differentiable ℝ (nymanBroadCorrelation n φ R) ∧
      Continuous (deriv (nymanBroadCorrelation n φ R)) ∧
      Integrable (nymanBroadCorrelation n φ R) ∧
      Integrable (deriv (nymanBroadCorrelation n φ R)) ∧
      (∫t,|deriv (nymanBroadCorrelation n φ R) t|)≤V ∧
      nymanBroadCorrelation n φ R 0=1 ∧
      ∀ t,|1-nymanBroadCorrelation n φ R t|≤B*t^2 := by
  obtain ⟨L0,S0,hL0,hS0,h0⟩ := eventually_nymanBroadProfile_derivative_bounds n hn hφ hc hmass 0
  obtain ⟨L1,S1,hL1,hS1,h1⟩ := eventually_nymanBroadProfile_derivative_bounds n hn hφ hc hmass 1
  obtain ⟨L2,S2,hL2,hS2,h2⟩ := eventually_nymanBroadProfile_derivative_bounds n hn hφ hc hmass 2
  refine ⟨L1*L0,S2*L0,mul_nonneg hL1 hL0,mul_nonneg hS2 hL0,?_⟩
  filter_upwards [h0,h1,h2,eventually_integral_sq_nymanBroadProfile n hn hφ hc hmass]
    with R h0R h1R h2R hunit
  simp only [iteratedDeriv_succ,iteratedDeriv_zero] at h0R h1R h2R
  let f := nymanBroadProfile n φ R
  have hfd : Differentiable ℝ f := by
    simpa only [iteratedDeriv_zero] using
      differentiable_iteratedDeriv_nymanBroadProfile n (by omega) hφ hc 0 R
  have hdfd : Differentiable ℝ (deriv f) := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
      differentiable_iteratedDeriv_nymanBroadProfile n (by omega) hφ hc 1 R
  have hddfc : Continuous (deriv (deriv f)) := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
      (differentiable_iteratedDeriv_nymanBroadProfile n (by omega) hφ hc 2 R).continuous
  rw [nymanBroadCorrelation_eq_realKernel]
  have hd : Differentiable ℝ (realKernelCorrelation f f) :=
    fun t => (hasDerivAt_realKernelCorrelation f f h0R.1 hfd hdfd.continuous
      S0 S1 h0R.2.2 h1R.2.2 t).differentiableAt
  have hderiv := deriv_realKernelCorrelation f f h0R.1 hfd hdfd.continuous
    S0 S1 h0R.2.2 h1R.2.2
  have hdc : Continuous (deriv (realKernelCorrelation f f)) := by
    rw [hderiv]
    exact (show Differentiable ℝ (realKernelCorrelation (deriv f) f) from
      fun t => (hasDerivAt_realKernelCorrelation _ _ h0R.1 hdfd hddfc
        S1 S2 h1R.2.2 h2R.2.2 t).differentiableAt).continuous
  have hvar := integral_abs_deriv_realKernelCorrelation_le f f h0R.1 h1R.1
    hfd hdfd.continuous S0 S1 h0R.2.2 h1R.2.2
  have hzero : realKernelCorrelation f f 0=1 := by
    simpa only [realKernelCorrelation,add_zero,pow_two] using hunit
  refine ⟨hd,hdc,integrable_realKernelCorrelation f f h0R.1 h0R.1 hfd.continuous,
    hvar.1,?_,hzero,?_⟩
  · exact hvar.2.trans (mul_le_mul h1R.2.1 h0R.2.1
      (integral_nonneg (fun x => abs_nonneg _)) hL1)
  · intro t
    rw [←hzero]
    exact (abs_realKernelCorrelation_sub_origin_le_sq f h0R.1 hfd hdfd hddfc
      S0 S1 S2 h0R.2.2 h1R.2.2 h2R.2.2 t).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h0R.2.1 hS2)
          (sq_nonneg t))

end RiemannResearch.RH
