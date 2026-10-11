/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ZeroSamplingQuadratic
import RiemannResearch.Analysis.ZeroOrdinateEquidistribution

/-!
# Positive ordinate kernels and finite character detection

All finite identities below hold for arbitrary real frequencies and weights.
The sampling limit and uniqueness theorems take `FourierCancellation times`
as an explicit hypothesis; no analytic estimate for zeta zeros is asserted.

The Fourier cancellation motivation is Ford--Zaharescu,
https://arxiv.org/abs/math/0405459. The sum-of-squares identity is the ordinary
finite positive-measure Gram construction, specialized to the existing
sampling quadratic-form module.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.OrdinateSpectralKernel

open RiemannResearch.Analysis.ZeroSamplingQuadratic
open RiemannResearch.Analysis.ZeroOrdinate

variable {ι κ : Type*}

/-- Positivity is derived from the exact squared-amplitude expansion. -/
theorem sampling_form_real_identity
    (s : Finset ι) (samples : Finset κ) (weight : κ → ℝ)
    (feature : κ → ι → ℂ) (coefficient : ι → ℂ) :
    (form s (samplingGram samples weight feature) coefficient).re =
      ∑ k ∈ samples, weight k * Complex.normSq
        (∑ i ∈ s, coefficient i * feature k i) := by
  rw [form_samplingGram]
  simp only [Complex.star_def, Complex.mul_conj, ← Complex.ofReal_mul,
    Complex.re_sum, Complex.ofReal_re]

theorem sampling_form_nonnegative
    (s : Finset ι) (samples : Finset κ) (weight : κ → ℝ)
    (feature : κ → ι → ℂ) (coefficient : ι → ℂ)
    (hweight : ∀ k ∈ samples, 0 ≤ weight k) :
    0 ≤ (form s (samplingGram samples weight feature) coefficient).re := by
  rw [sampling_form_real_identity]
  exact Finset.sum_nonneg fun k hk =>
    mul_nonneg (hweight k hk) (Complex.normSq_nonneg _)

/-- With strictly positive weights, zero sampled energy is exactly pointwise
annihilation on the sampled support. No full-rank assumption is hidden. -/
theorem sampling_form_zero_iff
    (s : Finset ι) (samples : Finset κ) (weight : κ → ℝ)
    (feature : κ → ι → ℂ) (coefficient : ι → ℂ)
    (hweight : ∀ k ∈ samples, 0 < weight k) :
    (form s (samplingGram samples weight feature) coefficient).re = 0 ↔
      ∀ k ∈ samples, (∑ i ∈ s, coefficient i * feature k i) = 0 := by
  rw [sampling_form_real_identity]
  constructor
  · intro h k hk
    have hterm : weight k * Complex.normSq
        (∑ i ∈ s, coefficient i * feature k i) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun k hk => mul_nonneg (hweight k hk).le (Complex.normSq_nonneg _))).mp h k hk
    apply Complex.normSq_eq_zero.mp
    exact (mul_eq_zero.mp hterm).resolve_left (ne_of_gt (hweight k hk))
  · intro h
    apply Finset.sum_eq_zero
    intro k hk
    rw [h k hk, Complex.normSq_zero, mul_zero]

def kernel (samples : Finset κ) (weight frequency : κ → ℝ) (time : ℝ) : ℂ :=
  ∑ k ∈ samples, (weight k : ℂ) * phase time (frequency k)

/-- The ordinate spectral kernel is Hermitian, including multiplicities. -/
theorem kernel_neg
    (samples : Finset κ) (weight frequency : κ → ℝ) (time : ℝ) :
    kernel samples weight frequency (-time) = star (kernel samples weight frequency time) := by
  simp only [kernel, phase_neg, star_sum, star_mul, Complex.star_def,
    Complex.conj_ofReal, mul_comm]

theorem kernel_mass_bound
    (samples : Finset κ) (weight frequency : κ → ℝ) (time : ℝ)
    (hweight : ∀ k ∈ samples, 0 ≤ weight k) :
    ‖kernel samples weight frequency time‖ ≤ ∑ k ∈ samples, weight k := by
  unfold kernel
  calc
    _ ≤ ∑ k ∈ samples, ‖(weight k : ℂ) * phase time (frequency k)‖ :=
      norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [norm_mul, phase_norm, Complex.norm_of_nonneg (hweight k hk), mul_one]

/-- Genuine positive definiteness for arbitrary finite time tests. -/
theorem kernel_positive_definite
    (s : Finset ι) (samples : Finset κ) (weight frequency : κ → ℝ)
    (time : ι → ℝ) (coefficient : ι → ℂ)
    (hweight : ∀ k ∈ samples, 0 ≤ weight k) :
    0 ≤ (form s (fun i j => kernel samples weight frequency (time i - time j))
      coefficient).re := by
  have h := sampling_form_nonnegative s samples weight
    (fun k i => phase (time i) (frequency k)) coefficient hweight
  unfold samplingGram at h
  simpa only [kernel, phase_sub, mul_assoc] using h

def weightedEnergy (samples : Finset κ) (weight : κ → ℝ)
    (value : κ → ℂ) : ℝ := ∑ k ∈ samples, weight k * Complex.normSq (value k)

def modulate (frequency : κ → ℝ) (time : ℝ)
    (value : κ → ℂ) (k : κ) : ℂ := phase time (frequency k) * value k

theorem modulation_preserves_energy
    (samples : Finset κ) (weight frequency : κ → ℝ)
    (value : κ → ℂ) (time : ℝ) :
    weightedEnergy samples weight (modulate frequency time value) =
      weightedEnergy samples weight value := by
  simp [weightedEnergy, modulate,
    Complex.normSq_eq_norm_sq, phase_norm]

theorem modulation_add
    (frequency : κ → ℝ) (time shift : ℝ) (value : κ → ℂ) :
    modulate frequency (time + shift) value =
      modulate frequency time (modulate frequency shift value) := by
  funext k
  simp only [modulate, phase_add, mul_assoc]

/-- The exact real symmetric two-point PSD criterion, including zero mass. -/
theorem two_point_psd_iff_abs_bound (mass correlation : ℝ) :
    (∀ a b : ℝ, 0 ≤ mass * (a ^ 2 + b ^ 2) + 2 * correlation * a * b) ↔
      |correlation| ≤ mass := by
  constructor
  · intro h
    have hplus := h 1 1
    have hminus := h 1 (-1)
    apply abs_le.mpr
    constructor <;> nlinarith
  · intro h a b
    obtain ⟨hlo, hhi⟩ := abs_le.mp h
    have hp : 0 ≤ (mass + correlation) * (a + b) ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    have hm : 0 ≤ (mass - correlation) * (a - b) ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    nlinarith

def amplitude (s : Finset ι) (frequency : ι → ℝ)
    (coefficient : ι → ℂ) (time : ℝ) : ℂ :=
  ∑ i ∈ s, coefficient i * phase (frequency i) time

/-- Every off-diagonal term is retained before taking the mean. -/
theorem mean_amplitude_square_expansion
    (s : Finset ι) (frequency : ι → ℝ) (coefficient : ι → ℂ)
    (times : ℕ → ℝ) (n : ℕ) :
    mean n (fun j => amplitude s frequency coefficient (times j) *
      star (amplitude s frequency coefficient (times j))) =
    form s (fun i k => mean n (fun j =>
      phase (frequency i) (times j) * star (phase (frequency k) (times j))))
      coefficient := by
  calc
    _ = mean n (fun j => ∑ i ∈ s, ∑ k ∈ s,
        coefficient i * star (coefficient k) *
          (phase (frequency i) (times j) * star (phase (frequency k) (times j)))) := by
      congr 1
      funext j
      simp only [amplitude, star_sum, star_mul, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = _ := by
      simp only [mean_sum, mean_mul_left, form]

/-- Entrywise convergence may be passed through one fixed finite form. -/
theorem form_tendsto
    (s : Finset ι) (matrix : ℕ → ι → ι → ℂ) (limit : ι → ι → ℂ)
    (coefficient : ι → ℂ)
    (h : ∀ i ∈ s, ∀ j ∈ s,
      Tendsto (fun n => matrix n i j) atTop (𝓝 (limit i j))) :
    Tendsto (fun n => form s (matrix n) coefficient) atTop
      (𝓝 (form s limit coefficient)) := by
  unfold form
  apply tendsto_finsetSum
  intro i hi
  apply tendsto_finsetSum
  intro j hj
  exact tendsto_const_nhds.mul (h i hi j hj)

/-- Fourier cancellation gives the exact frequency-collision Gram limit.
In particular repeated frequencies are not incorrectly treated as independent. -/
theorem character_energy_limit
    (s : Finset ι) (frequency : ι → ℝ) (coefficient : ι → ℂ)
    (times : ℕ → ℝ) (hcancel : FourierCancellation times) :
    Tendsto (fun n => mean n (fun j =>
      amplitude s frequency coefficient (times j) *
        star (amplitude s frequency coefficient (times j)))) atTop
      (𝓝 (form s (fun i k => if frequency i = frequency k then 1 else 0)
        coefficient)) := by
  classical
  simp_rw [mean_amplitude_square_expansion]
  exact form_tendsto s _ _ coefficient
    (fun i _ k _ => phase_covariance_limit times hcancel (frequency i) (frequency k))

/-- For a fixed set of distinct frequencies, sampled energy tends to coefficient energy. -/
theorem distinct_character_energy_limit
    (s : Finset ι) (frequency : ι → ℝ) (coefficient : ι → ℂ)
    (times : ℕ → ℝ) (hcancel : FourierCancellation times)
    (hfrequency : ∀ i ∈ s, ∀ k ∈ s, frequency i = frequency k → i = k) :
    Tendsto (fun n => mean n (fun j =>
      amplitude s frequency coefficient (times j) *
        star (amplitude s frequency coefficient (times j)))) atTop
      (𝓝 (coefficientEnergy s coefficient : ℂ)) := by
  classical
  have h := character_energy_limit s frequency coefficient times hcancel
  have hform : form s (fun i k => if frequency i = frequency k then 1 else 0)
        coefficient = (coefficientEnergy s coefficient : ℂ) := by
    calc
      _ = form s (fun i k => if i = k then 1 else 0) coefficient := by
        unfold form
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro k hk
        have heq : frequency i = frequency k ↔ i = k :=
          ⟨hfrequency i hi k hk, by intro h; rw [h]⟩
        simp only [heq]
      form s (fun i k => if i = k then 1 else 0) coefficient =
        (coefficientEnergy s coefficient : ℂ) := form_identity s coefficient
  simpa only [hform] using h

/-- Fixed finite frequency sets have coefficient-uniform Parseval control.
The coefficient vector may be chosen after observing the samples. The support
is fixed; this theorem supplies no growing-support rate. -/
theorem eventually_uniform_energy_error
    (s : Finset ι) (frequency : ι → ℝ)
    (times : ℕ → ℝ) (hcancel : FourierCancellation times)
    (hfrequency : ∀ i ∈ s, ∀ k ∈ s, frequency i = frequency k → i = k)
    (error : ℝ) (herror : 0 < error) :
    ∀ᶠ n in atTop, ∀ coefficient : ι → ℂ,
      |(mean n (fun j => amplitude s frequency coefficient (times j) *
          star (amplitude s frequency coefficient (times j)))).re -
        coefficientEnergy s coefficient| ≤ error * coefficientEnergy s coefficient := by
  classical
  let entryError : ℝ := error / ((s.card : ℝ) + 1)
  have hdenom : 0 < (s.card : ℝ) + 1 := by positivity
  have hentry : 0 < entryError := div_pos herror hdenom
  have hentryEventually : ∀ᶠ n in atTop, ∀ i ∈ s, ∀ k ∈ s,
      ‖mean n (fun j => phase (frequency i) (times j) *
          star (phase (frequency k) (times j))) - (if i = k then 1 else 0)‖ ≤ entryError := by
    apply (Filter.eventually_all_finset s).mpr
    intro i hi
    apply (Filter.eventually_all_finset s).mpr
    intro k hk
    have heq : frequency i = frequency k ↔ i = k :=
      ⟨hfrequency i hi k hk, by intro h; rw [h]⟩
    have hlimit := phase_covariance_limit times hcancel (frequency i) (frequency k)
    simp only [heq] at hlimit
    have hnorm : Tendsto (fun n => ‖mean n (fun j =>
        phase (frequency i) (times j) * star (phase (frequency k) (times j))) -
        (if i = k then 1 else 0)‖) atTop (𝓝 0) := by
      simpa using (hlimit.sub (tendsto_const_nhds
        (x := (if i = k then (1 : ℂ) else 0)))).norm
    exact (hnorm.eventually_lt_const hentry).mono (fun n hn => hn.le)
  have hcoefficient : (s.card : ℝ) * entryError ≤ error := by
    calc
      _ = ((s.card : ℝ) * error) / ((s.card : ℝ) + 1) := by
        dsimp [entryError]
        ring
      _ ≤ error := (div_le_iff₀ hdenom).mpr (by nlinarith [herror.le])
  filter_upwards [hentryEventually] with n hn coefficient
  rw [mean_amplitude_square_expansion]
  exact (real_form_error s _ coefficient entryError hentry.le hn).trans
    (mul_le_mul_of_nonneg_right hcoefficient (coefficientEnergy_nonneg s coefficient))

/-- One sample threshold works for every nonzero coefficient vector on the
fixed support: the sampled finite Gram is eventually strictly positive. -/
theorem eventually_strict_character_detection
    (s : Finset ι) (frequency : ι → ℝ)
    (times : ℕ → ℝ) (hcancel : FourierCancellation times)
    (hfrequency : ∀ i ∈ s, ∀ k ∈ s, frequency i = frequency k → i = k) :
    ∀ᶠ n in atTop, ∀ coefficient : ι → ℂ,
      (∃ i ∈ s, coefficient i ≠ 0) →
        0 < (mean n (fun j => amplitude s frequency coefficient (times j) *
          star (amplitude s frequency coefficient (times j)))).re := by
  have h := eventually_uniform_energy_error s frequency times hcancel hfrequency
    (1 / 2 : ℝ) (by norm_num)
  filter_upwards [h] with n hn coefficient hnonzero
  obtain ⟨i, hi, hci⟩ := hnonzero
  have hnorm : 0 < ‖coefficient i‖ := norm_pos_iff.mpr hci
  have henergy : 0 < coefficientEnergy s coefficient := by
    apply Finset.sum_pos' (fun _ _ => sq_nonneg _)
    exact ⟨i, hi, sq_pos_of_pos hnorm⟩
  have herror := abs_le.mp (hn coefficient)
  nlinarith [herror.1]

/-- Under Fourier cancellation, a finite distinct-frequency polynomial cannot
vanish at every sample unless every coefficient vanishes. This is exact
detection, with no growing-support or uniform-rate conclusion. -/
theorem sampling_annihilator_trivial
    (s : Finset ι) (frequency : ι → ℝ) (coefficient : ι → ℂ)
    (times : ℕ → ℝ) (hcancel : FourierCancellation times)
    (hfrequency : ∀ i ∈ s, ∀ k ∈ s, frequency i = frequency k → i = k)
    (hvanish : ∀ j, amplitude s frequency coefficient (times j) = 0) :
    ∀ i ∈ s, coefficient i = 0 := by
  have hlimit := distinct_character_energy_limit s frequency coefficient times hcancel hfrequency
  have hzero : Tendsto (fun n => mean n (fun j =>
      amplitude s frequency coefficient (times j) *
        star (amplitude s frequency coefficient (times j)))) atTop (𝓝 0) := by
    simp only [hvanish, zero_mul, mean_zero]
    exact tendsto_const_nhds
  have hc : (coefficientEnergy s coefficient : ℂ) = 0 :=
    tendsto_nhds_unique hlimit hzero
  have he : coefficientEnergy s coefficient = 0 := by
    exact_mod_cast hc
  intro i hi
  have hterm : ‖coefficient i‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖coefficient i‖)).mp he i hi
  have hn : ‖coefficient i‖ = 0 := by nlinarith [norm_nonneg (coefficient i)]
  exact norm_eq_zero.mp hn

end RiemannResearch.Analysis.OrdinateSpectralKernel
