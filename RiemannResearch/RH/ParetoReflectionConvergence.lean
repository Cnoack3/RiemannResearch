/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoLegalApproximationClosure
import RiemannResearch.RH.ParetoReflectionVariance
import Mathlib.Topology.Order.Basic

/-!
# Convergence consequences of the reflection variance objective

Source: user-provided argument, 11 September 2026.

These theorems prove implications from precise convergence hypotheses.
They do not assert that suitable finite legal packets exist.  In particular,
passing from a legal mean-one variance sequence to actual RH uses the existing
proved Mellin-separation theorem, not an assumed RH bridge.
-/

open Filter
open scoped Topology

namespace FinitePairVariance

/-- Uniformly comparable nonnegative objectives have exactly the same
zero-limit sequences. The comparison constant is fixed along the sequence. -/
theorem objective_tendsto_zero_iff_of_comparable
    (v L : ℕ → ℝ) (K : ℝ)
    (hv : ∀ n, 0 ≤ v n) (hvL : ∀ n, v n ≤ L n)
    (hLv : ∀ n, L n ≤ K * v n) :
    Tendsto v atTop (𝓝 0) ↔ Tendsto L atTop (𝓝 0) := by
  constructor
  · intro h
    exact squeeze_zero (fun n => (hv n).trans (hvL n)) hLv
      (by simpa using h.const_mul K)
  · intro h
    exact squeeze_zero hv hvL h

/-- An exact split into nonnegative terms vanishes precisely when both do. -/
theorem objective_sum_tendsto_zero_iff
    (J T : ℕ → ℝ) (hJ : ∀ n, 0 ≤ J n) (hT : ∀ n, 0 ≤ T n) :
    Tendsto (fun n => J n + T n) atTop (𝓝 0) ↔
      Tendsto J atTop (𝓝 0) ∧ Tendsto T atTop (𝓝 0) := by
  constructor
  · intro h
    constructor
    · exact squeeze_zero hJ (fun n => le_add_of_nonneg_right (hT n)) h
    · exact squeeze_zero hT (fun n => le_add_of_nonneg_left (hJ n)) h
  · rintro ⟨h₁, h₂⟩
    simpa using h₁.add h₂

end FinitePairVariance

namespace RiemannResearch.RH.Pareto
open FinitePairVariance

/-- Mean-one legal variance convergence implies the actual Riemann
hypothesis. No rate, coefficient bound, or omitted boundary is assumed. -/
theorem riemannHypothesis_of_legal_mean_one_variance_tendsto
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (F : ℕ → ℕ → ℝ)
    (hlegal : ∀ n, F n ∈ legalSeedSpan A)
    (hmean : ∀ n, paretoMean (F n) = 1)
    (hvar : Tendsto (fun n => paretoVariance (F n)) atTop (𝓝 0)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_legal_noiseSignalRatio A hA
  intro ε hε
  obtain ⟨n, hn⟩ := (hvar.eventually_lt_const hε).exists
  refine ⟨F n, hlegal n, ?_, ?_⟩
  · rw [hmean n]
    norm_num
  · simpa [noiseSignalRatio, hmean n] using hn

/-- A vanishing proved majorant of the complete legal variance suffices.
Applications must supply a bound on the full Pareto variance. -/
theorem riemannHypothesis_of_legal_mean_one_variance_majorant
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (F : ℕ → ℕ → ℝ) (L : ℕ → ℝ)
    (hlegal : ∀ n, F n ∈ legalSeedSpan A)
    (hmean : ∀ n, paretoMean (F n) = 1)
    (hbound : ∀ n, paretoVariance (F n) ≤ L n)
    (hlim : Tendsto L atTop (𝓝 0)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_legal_mean_one_variance_tendsto A hA F hlegal hmean
  exact squeeze_zero (fun n => paretoVariance_nonneg (F n)) hbound hlim

/-- An even reflection period exists for every actual finite legal witness. -/
theorem legalSeedSpan_exists_even_reflectionPeriod
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    {f : ℕ → ℝ} (hf : f ∈ legalSeedSpan A) :
    ∃ Q : ℕ, 0 < Q ∧ Even Q ∧
      (∀ n, f (n + Q) = f n) ∧
      (∀ n, n < Q → f n + f (Q - 1 - n) = f (Q - 1)) := by
  obtain ⟨d, hd, hp⟩ := legalSeedSpan_hasLegalReflectionPeriod A hA hf
  have h := hp (2 * d) (dvd_mul_left d 2)
  exact ⟨2 * d, by omega, ⟨d, by omega⟩, h.1, h.2⟩

/-- The actual surrogate has precisely the same zero-limit sequences as
the full variance. Each function may have its own bound and period. -/
theorem paretoVariance_tendsto_iff_reflectionSurrogate
    (Q : ℕ → ℕ) (F : ℕ → ℕ → ℝ) (B C : ℕ → ℝ)
    (hQ : ∀ n, 0 < Q n) (heven : ∀ n, Even (Q n))
    (hB : ∀ n k, |F n k| ≤ B n)
    (hp : ∀ n k, F n (k + Q n) = F n k)
    (href : ∀ n k, k < Q n → F n k + F n (Q n - 1 - k) = C n) :
    Tendsto (fun n => paretoVariance (F n)) atTop (𝓝 0) ↔
      Tendsto (fun n => reflectionSurrogate (Q n) (F n) (paretoMean (F n)) (C n))
        atTop (𝓝 0) := by
  apply objective_tendsto_zero_iff_of_comparable _ _ (1 + Real.pi ^ 2)
    (fun n => paretoVariance_nonneg (F n))
  · intro n
    exact (paretoVariance_reflectionSurrogate_comparison (Q n) (hQ n) (heven n)
      (F n) (hB n) (hp n) (C n) (href n)).1
  · intro n
    exact (paretoVariance_reflectionSurrogate_comparison (Q n) (hQ n) (heven n)
      (F n) (hB n) (hp n) (C n) (href n)).2

/-- Convergence of the actual reflection objective on mean-one legal
witnesses implies RH. The existence of such witnesses remains an input. -/
theorem riemannHypothesis_of_legal_reflectionSurrogate_tendsto
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (Q : ℕ → ℕ) (F : ℕ → ℕ → ℝ) (C : ℕ → ℝ)
    (hlegal : ∀ n, F n ∈ legalSeedSpan A)
    (hmean : ∀ n, paretoMean (F n) = 1)
    (hQ : ∀ n, 0 < Q n) (heven : ∀ n, Even (Q n))
    (hp : ∀ n k, F n (k + Q n) = F n k)
    (href : ∀ n k, k < Q n → F n k + F n (Q n - 1 - k) = C n)
    (hlim : Tendsto (fun n => reflectionSurrogate (Q n) (F n) 1 (C n))
      atTop (𝓝 0)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_legal_mean_one_variance_majorant A hA F
    (fun n => reflectionSurrogate (Q n) (F n) 1 (C n)) hlegal hmean _ hlim
  intro n
  obtain ⟨B, hB⟩ := legalSeedSpan_bounded A hA (hlegal n)
  have h := (paretoVariance_reflectionSurrogate_comparison (Q n) (hQ n) (heven n)
    (F n) hB (hp n) (C n) (href n)).1
  simpa only [hmean n] using h

/-- The two concrete remaining arithmetic obligations suffice: calibration
vanishes and the uniform reflection variance divided by the period vanishes.
This theorem supplies no approximating sequence and assumes no RH provider. -/
theorem riemannHypothesis_of_legal_reflection_split_tendsto
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (Q : ℕ → ℕ) (F : ℕ → ℕ → ℝ) (C : ℕ → ℝ)
    (hlegal : ∀ n, F n ∈ legalSeedSpan A)
    (hmean : ∀ n, paretoMean (F n) = 1)
    (hQ : ∀ n, 0 < Q n) (heven : ∀ n, Even (Q n))
    (hp : ∀ n k, F n (k + Q n) = F n k)
    (href : ∀ n k, k < Q n → F n k + F n (Q n - 1 - k) = C n)
    (hJ : Tendsto (fun n => reflectionCalibration (Q n) (F n) 1) atTop (𝓝 0))
    (hU : Tendsto (fun n => uniformReflectionVariance (Q n) (F n) (C n) / Q n)
      atTop (𝓝 0)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_legal_reflectionSurrogate_tendsto
    A hA Q F C hlegal hmean hQ heven hp href
  have hpen : Tendsto
      (fun n => Real.pi ^ 2 / (Q n : ℝ) * uniformReflectionVariance (Q n) (F n) (C n))
      atTop (𝓝 0) := by
    have heq :
        (fun n => Real.pi ^ 2 / (Q n : ℝ) * uniformReflectionVariance (Q n) (F n) (C n)) =
        (fun n => Real.pi ^ 2 * (uniformReflectionVariance (Q n) (F n) (C n) / Q n)) := by
      funext n
      ring
    rw [heq]
    simpa using hU.const_mul (Real.pi ^ 2)
  simpa only [reflectionSurrogate, add_zero] using hJ.add hpen

/-- If the witness is fixed and conditioning noise vanishes along a sequence
of reflection periods, its unchanged full variance passes into calibration.
Shrinking the noise by changing periods therefore creates no variance gain. -/
theorem reflectionCalibration_tendsto_variance_of_noise_tendsto_zero
    (Q : ℕ → ℕ) (C : ℕ → ℝ) (f : ℕ → ℝ) {B : ℝ}
    (hf : ∀ k, |f k| ≤ B)
    (hQ : ∀ n, 0 < Q n)
    (hp : ∀ n k, f (k + Q n) = f k)
    (href : ∀ n k, k < Q n → f k + f (Q n - 1 - k) = C n)
    (hnoise : Tendsto (fun n => reflectionNoise (Q n) f (C n)) atTop (𝓝 0)) :
    Tendsto (fun n => reflectionCalibration (Q n) f (paretoMean f))
      atTop (𝓝 (paretoVariance f)) := by
  have heq :
      (fun n => reflectionCalibration (Q n) f (paretoMean f)) =
      (fun n => paretoVariance f - reflectionNoise (Q n) f (C n)) := by
    funext n
    have h := paretoVariance_eq_reflection (Q n) (hQ n) f hf (hp n) (C n) (href n)
    linarith
  rw [heq]
  simpa only [sub_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => paretoVariance f)
      atTop (𝓝 (paretoVariance f))).sub hnoise

end RiemannResearch.RH.Pareto
