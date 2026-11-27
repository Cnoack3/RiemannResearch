import RiemannResearch.Probability.DPPSpectralMultiplier
import RiemannResearch.Probability.DPPAveragedVariation
import RiemannResearch.Probability.DPPBinaryInterval
import RiemannResearch.Probability.DPPIntervalSpectrum

/-!
# Sharp spectral rigidity for continuous convolution determinantal kernels

A bound strictly below two for the regular structure-factor slope along one
sequence of positive frequencies tending to zero forces a length-one interval
multiplier. The Fourier phase is a translation gauge. See B. Galerne,
*Computation of the perimeter of measurable sets via their covariogram* (2011),
https://doi.org/10.5566/ias.v30.p39-51, for the general variation identity.
-/

open Filter MeasureTheory Set
open scoped Topology FourierTransform

namespace RiemannResearch.DPPSpectral

/-- The spectral interval is identified up to translation from one sequence. -/
theorem interval_spectrum_of_small_slope {f : ℝ → ℝ} (hf : Integrable f)
    (hb : ∀ᵐ t, 0 ≤ f t ∧ f t ≤ 1) (hm : (∫ t, f t) = 1)
    {h : ℕ → ℝ} (hp : ∀ n, 0 < h n) (hz : Tendsto h atTop (𝓝 0))
    {c : ℝ} (hc : c < 2) (hs : ∀ᶠ n in atTop, structureFactor f (h n) ≤ c * h n) :
    ∃ a : ℝ, f =ᵐ[volume] (Ioo a (a + 1)).indicator (1 : ℝ → ℝ) := by
  have h0 : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have hc0 : Tendsto (fun n => c * h n) atTop (𝓝 0) := by simpa using hz.const_mul c
  have hs0 := tendsto_of_tendsto_of_tendsto_of_le_of_le' h0 hc0
    (Eventually.of_forall fun n => structureFactor_nonneg hf hb hm (h n)) hs
  obtain ⟨E, _, _, hef⟩ := exists_indicator_of_structureFactor_tendsto_zero hf hb hm hs0
  have hbin : ∀ᵐ t, f t = 0 ∨ f t = 1 := by
    filter_upwards [hef] with t ht
    by_cases hE : t ∈ E <;> simp_all
  let D := {x | (f x = 0 ∨ f x = 1) ∧ Tendsto (fun n => rightAverage f (h n) x) atTop (𝓝 (f x))}
  have hD : ∀ᵐ x, x ∈ D := hbin.and (ae_tendsto_rightAverage hf hp hz)
  obtain ⟨a, ha⟩ := exists_unit_interval_of_no_five hf hm hD (fun _ ht => ht.1) (by
    intro a b d e j ha hb' hd he hj hab hbd hde hej h0 h1 h2 h3 h4
    have hv := ((((hb'.2.sub ha.2).abs.add (hd.2.sub hb'.2).abs).add
      (he.2.sub hd.2).abs).add (hj.2.sub he.2).abs)
    have hle := le_of_tendsto hv (b := 2 * c) (by
      filter_upwards [hs] with n hn
      refine (fivePoint_variation_bound hf (hp n) hab.le hbd.le hde.le hej.le).trans ?_
      rw [← twice_structureFactor_eq_integral_abs hf hm hbin (h n)]
      apply (div_le_iff₀ (hp n)).mpr
      linarith only [hn])
    rw [h0,h1,h2,h3,h4] at hle
    norm_num at hle
    linarith)
  exact ⟨a, ha⟩

/-- Sharp right lower slope criterion, including the Fourier phase and
second factorial density at every separation. -/
theorem spectral_rigidity_of_liminf_lt_two {f : ℝ → ℝ} (hf : Integrable f)
    (hb : ∀ᵐ t, 0 ≤ f t ∧ f t ≤ 1) (hm : (∫ t, f t) = 1)
    (hs : liminf (fun h => ENNReal.ofReal (structureFactor f h / h)) (𝓝[>] 0) < ENNReal.ofReal 2) :
    ∃ a : ℝ, f =ᵐ[volume] (Ioo a (a + 1)).indicator (1 : ℝ → ℝ) ∧ ∀ x : ℝ,
      𝓕 (fun t ↦ (f t : ℂ)) (-x) =
        Complex.exp (((2 * Real.pi * x * (a + 1 / 2) : ℝ) : ℂ) * Complex.I) * (Real.sinc (Real.pi * x) : ℂ) ∧
      1 - ‖𝓕 (fun t ↦ (f t : ℂ)) (-x)‖ ^ 2 = 1 - Real.sinc (Real.pi * x) ^ 2 := by
  obtain ⟨c, _, hc, h, hp, hz, hbound⟩ := exists_small_steps_of_liminf_lt hs
  obtain ⟨a, ha⟩ := interval_spectrum_of_small_slope hf hb hm hp hz hc (Eventually.of_forall hbound)
  refine ⟨a, ha, fun x => ?_⟩
  exact ⟨fourier_of_interval_ae ha x, fourier_pair_of_interval_ae ha x⟩

/--
info: 'RiemannResearch.DPPSpectral.spectral_rigidity_of_liminf_lt_two' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms spectral_rigidity_of_liminf_lt_two

end RiemannResearch.DPPSpectral
