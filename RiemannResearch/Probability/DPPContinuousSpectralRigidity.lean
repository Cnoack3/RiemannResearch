import RiemannResearch.Probability.DPPSpectralMultiplier
import RiemannResearch.Probability.DPPAveragedVariation
import RiemannResearch.Probability.DPPBinaryInterval
import RiemannResearch.Probability.DPPIntervalSpectrum
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

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

/-- The regular structure factor of any translate of the unit band, at every frequency. -/
theorem structureFactor_of_interval_ae {f : ℝ → ℝ} {a : ℝ}
    (hf : f =ᵐ[volume] (Ioo a (a + 1)).indicator (1 : ℝ → ℝ)) (h : ℝ) :
    structureFactor f h = min |h| 1 := by
  have he : f =ᵐ[volume] intervalMultiplier a := by
    filter_upwards [hf, (Ioo_ae_eq_Ioc (μ := volume) (a := a) (b := a + 1))] with t ht he
    change (t ∈ Ioo a (a + 1)) = (t ∈ Ioc a (a + 1)) at he
    simp [ht, intervalMultiplier, Set.indicator, he]
  have hshift : (fun t => f (t + h)) =ᵐ[volume] (fun t => intervalMultiplier a (t + h)) :=
    (measurePreserving_add_right volume h).quasiMeasurePreserving.ae he
  unfold structureFactor
  rw [integral_congr_ae (show (fun t => f t * f (t + h)) =ᵐ[volume]
    (fun t => intervalMultiplier a t * intervalMultiplier a (t + h)) from
      he.mul hshift), intervalMultiplier_overlap]
  by_cases hh : |h| ≤ 1
  · rw [max_eq_left (sub_nonneg.mpr hh), min_eq_left hh]
    ring
  · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge hh)), min_eq_right (le_of_not_ge hh), sub_zero]

/-- In the unit-band case the right slope exists, including in the extended-real
normalization used in the rigidity theorem. -/
theorem structureFactor_rightSlope_of_interval_ae {f : ℝ → ℝ} {a : ℝ}
    (hf : f =ᵐ[volume] (Ioo a (a + 1)).indicator (1 : ℝ → ℝ)) :
    Tendsto (fun h => ENNReal.ofReal (structureFactor f h / h)) (𝓝[>] 0) (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with h hp h1
  change 0 < h at hp
  change h < 1 at h1
  simp [structureFactor_of_interval_ae hf, abs_of_pos hp, min_eq_left h1.le, hp.ne']

/-- There are no intermediate lower slopes below the two-component threshold. -/
theorem structureFactor_liminf_lt_two_iff_eq_one {f : ℝ → ℝ} (hf : Integrable f)
    (hb : ∀ᵐ t, 0 ≤ f t ∧ f t ≤ 1) (hm : (∫ t, f t) = 1) :
    (liminf (fun h => ENNReal.ofReal (structureFactor f h / h)) (𝓝[>] 0) < ENNReal.ofReal 2) ↔
      liminf (fun h => ENNReal.ofReal (structureFactor f h / h)) (𝓝[>] 0) = 1 := by
  constructor
  · intro hs
    obtain ⟨a, ha, _⟩ := spectral_rigidity_of_liminf_lt_two hf hb hm hs
    exact (structureFactor_rightSlope_of_interval_ae ha).liminf_eq
  · intro hs
    rw [hs]
    norm_num

/-- For a convolution DPP the strict lower-slope test identifies every finite
correlation determinant. This algebraic statement evaluates the candidate
kernel; the DPP law of a physical process is a separate hypothesis. -/
theorem sine_det_of_liminf_lt_two {f : ℝ → ℝ} (hf : Integrable f)
    (hb : ∀ᵐ t, 0 ≤ f t ∧ f t ≤ 1) (hm : (∫ t, f t) = 1)
    (hs : liminf (fun h => ENNReal.ofReal (structureFactor f h / h)) (𝓝[>] 0) < ENNReal.ofReal 2)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℝ) :
    Matrix.det (fun i j => 𝓕 (fun t ↦ (f t : ℂ)) (-(x i - x j))) =
      Matrix.det (fun i j => (Real.sinc (Real.pi * (x i - x j)) : ℂ)) := by
  obtain ⟨a, _, hkernel⟩ := spectral_rigidity_of_liminf_lt_two hf hb hm hs
  let θ (i : ι) : ℂ := ((2 * Real.pi * x i * (a + 1 / 2) : ℝ) : ℂ) * Complex.I
  let K : Matrix ι ι ℂ := fun i j => (Real.sinc (Real.pi * (x i - x j)) : ℂ)
  have hmatrix : (fun i j => 𝓕 (fun t ↦ (f t : ℂ)) (-(x i - x j))) =
      Matrix.of (fun i j => Complex.exp (θ i) *
        (Matrix.of (fun k l => Complex.exp (-θ l) * K k l)) i j) := by
    funext i j
    rw [(hkernel (x i - x j)).1]
    change _ = Complex.exp (θ i) * (Complex.exp (-θ j) * K i j)
    rw [← mul_assoc, ← Complex.exp_add]
    apply congrArg (fun z : ℂ => Complex.exp z * K i j)
    dsimp only [θ]
    push_cast
    ring
  rw [hmatrix, Matrix.det_mul_column, Matrix.det_mul_row, ← mul_assoc, ← Finset.prod_mul_distrib]
  simp only [← Complex.exp_add, add_neg_cancel, Complex.exp_zero, Finset.prod_const_one, one_mul] <;> rfl

/--
info: 'RiemannResearch.DPPSpectral.structureFactor_liminf_lt_two_iff_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms structureFactor_liminf_lt_two_iff_eq_one

/--
info: 'RiemannResearch.DPPSpectral.sine_det_of_liminf_lt_two' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sine_det_of_liminf_lt_two

end RiemannResearch.DPPSpectral
