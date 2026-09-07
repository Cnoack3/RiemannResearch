import RiemannResearch.RH.NymanBroadCorrelationBounds
import RiemannResearch.RH.NymanBroadKernelEnergy
import RiemannResearch.RH.RealAutocorrelationSquare

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Actual broad prime-square asymptotic with bounded error

This is the varying arithmetic family from the note. Its C1 superexponential
correlations, uniform variation, exact mass, and quantitative mean-square
limit have concrete providers. The signed Mertens discrepancy is retained;
only its boundedness is used, so no convergence of that error is asserted.
-/

open MeasureTheory Set Filter
open scoped Topology
namespace RiemannResearch.RH
open RiemannResearch.Analysis

/-- Actual decay of the broad correlation and its actual derivative. -/
theorem nymanBroadCorrelation_decay (n : ℕ) (hn : 0<n)
    {φ : ℝ → ℝ} {a b R : ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (ha : ∀ x<a,φ x=0) (hb : ∀ x>b,φ x=0) (hR : 0<R) :
    SuperexponentialDecay (nymanBroadCorrelation n φ R) ∧
      SuperexponentialDecay (deriv (nymanBroadCorrelation n φ R)) := by
  let f : ℝ → ℂ := fun x => (nymanBroadProfile n φ R x:ℂ)
  have hs := smoothSuperexponentialDecay_nymanBroadProfile n hn hφ ha hb hR
  have h0 : SuperexponentialDecay f := by simpa only [iteratedDeriv_zero] using hs.2 0
  have h1 : SuperexponentialDecay (deriv f) := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hs.2 1
  have h2 : SuperexponentialDecay (deriv (deriv f)) := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hs.2 2
  have hd : Differentiable ℝ f := hs.1.differentiable (by simp)
  have hdc : ContDiff ℝ (↑(⊤:ℕ∞)) (deriv f) := by
    simpa only [Function.iterate_one] using ContDiff.iterate_deriv 1 hs.1
  have hdd : Differentiable ℝ (deriv f) := hdc.differentiable (by simp)
  exact ⟨SignedWeilCorrelation.superexponential_realAutocorrelation f h0 hd.continuous,
    (SignedWeilCorrelation.realAutocorrelation_calculus_providers h0 h1 h2 hd hdd).2.2⟩

/-- The entire prime-square sector of the actual broad return has its negative
linear term with a bounded, possibly oscillatory, signed remainder. -/
theorem eventually_nymanBroad_primeSquare_linear_error (n : ℕ) (hn : 2≤n)
    {φ : ℝ → ℝ} {a b : ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (ha : ∀ x<a,φ x=0) (hb : ∀ x>b,φ x=0) (hmass : (∫x,φ x)≠0) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ R : ℝ in atTop,
      |primeSquareSector (nymanBroadCorrelation n φ R) R +
        (R/2)*((∫x,φ x)^2/(∫x,φ x^2))|≤C := by
  have hc := broadProfile_hasCompactSupport_of_bounds ha hb
  obtain ⟨V,B,hV,hB,hbounds⟩ := eventually_nymanBroadCorrelation_uniform_bounds n hn hφ hc hmass
  obtain ⟨C,hC,hmean⟩ := eventually_nymanBroadProfile_mean_square_error n hn hφ hc hmass
  obtain ⟨D,hD,hMertens⟩ := exists_primeSquare_superexponential_variation_bound
  refine ⟨2*D*V+C/2,by positivity,?_⟩
  filter_upwards [hbounds,hmean,eventually_gt_atTop (0:ℝ)] with R hcorr hmeanR hR
  rcases hcorr with ⟨hcd,hcc,hci,hdi,hvar,hzero,hdisp⟩
  have hs := nymanBroadCorrelation_decay n (by omega) hφ ha hb hR
  have hsq := hMertens (nymanBroadCorrelation n φ R) hcd hcc hs.1 hs.2 R hR
  have hhalf : (∫t in Ioi 0,|deriv (nymanBroadCorrelation n φ R) t|)≤V :=
    (setIntegral_le_integral hdi.abs (ae_of_all _ (fun t => abs_nonneg _))).trans hvar
  have hvarbound := mul_le_mul_of_nonneg_left hhalf (show 0≤2*D by positivity)
  have hfc := (contDiff_nymanBroadProfile n (by omega) hφ ha hb hR).continuous
  have hfi := integrable_real_of_superexponential hfc
    (by simpa only [iteratedDeriv_zero] using
      superexponential_iteratedDeriv_nymanBroadProfile n (by omega) hφ ha hb hR 0)
  rw [integral_nymanBroadCorrelation_Ioi n φ R hfi hfc] at hsq
  have hsqbound := hsq.trans hvarbound
  let q := (∫x,φ x)^2/(∫x,φ x^2)
  let m := (∫x,nymanBroadProfile n φ R x)^2
  have hmerror : |(R/2)*(q-m)|≤C/2 := by
    rw [abs_mul,abs_of_pos (div_pos hR (by norm_num)),abs_sub_comm]
    change (R/2)*|m-q|≤C/2
    change R*|m-q|≤C at hmeanR
    nlinarith
  calc
    _ = |(primeSquareSector (nymanBroadCorrelation n φ R) R +R*(m/2))+
          (R/2)*(q-m)| := by congr 1; ring
    _ ≤ |primeSquareSector (nymanBroadCorrelation n φ R) R +R*(m/2)|+
          |(R/2)*(q-m)| := abs_add_le _ _
    _ ≤ 2*D*V+C/2 := add_le_add hsqbound hmerror

/-- The linear slope is a proved limit of the actual varying-family series. -/
theorem tendsto_nymanBroad_primeSquare_div (n : ℕ) (hn : 2≤n)
    {φ : ℝ → ℝ} {a b : ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (ha : ∀ x<a,φ x=0) (hb : ∀ x>b,φ x=0) (hmass : (∫x,φ x)≠0) :
    Tendsto (fun R : ℝ => primeSquareSector (nymanBroadCorrelation n φ R) R/R)
      atTop (𝓝 (-((∫x,φ x)^2/(∫x,φ x^2))/2)) := by
  obtain ⟨C,hC,hbound⟩ := eventually_nymanBroad_primeSquare_linear_error n hn hφ ha hb hmass
  let q := (∫x,φ x)^2/(∫x,φ x^2)
  have hlim : Tendsto (fun R : ℝ => C/R) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using tendsto_inv_atTop_zero.const_mul C
  have he : Tendsto (fun R : ℝ =>
      (primeSquareSector (nymanBroadCorrelation n φ R) R+(R/2)*q)/R) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hlim
    filter_upwards [hbound,eventually_gt_atTop (0:ℝ)] with R hR hR0
    rw [Real.norm_eq_abs,abs_div,abs_of_pos hR0]
    exact div_le_div_of_nonneg_right hR hR0.le
  have ht := he.sub_const (q/2)
  apply (show Tendsto
    (fun R : ℝ => (primeSquareSector (nymanBroadCorrelation n φ R) R+(R/2)*q)/R-q/2)
    atTop (𝓝 (-q/2)) by simpa only [zero_sub,neg_div] using ht).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
  field_simp
  ring

end RiemannResearch.RH
