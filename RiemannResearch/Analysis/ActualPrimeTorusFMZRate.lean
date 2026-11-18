/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualRationalFMZRate
import RiemannResearch.Analysis.ActualZeroLoglogRate
import RiemannResearch.Analysis.ActualPrimeTorusFMZ
import RiemannResearch.Analysis.ActualPrimeTorusFMZPoisson
import RiemannResearch.Analysis.ActualPrimeTorusFMZSeries
import RiemannResearch.Analysis.ArithmeticWeightedFourierRemainder
import RiemannResearch.Analysis.FinitePrimeModeArithmetic
import RiemannResearch.Analysis.PrimePhaseTorus
import RiemannResearch.Analysis.PrimeTorusFourierSeries
import RiemannResearch.Analysis.PrimeTorusHaarSpecialization
import Mathlib.Tactic.Linarith

/-!
# Quantitative prime-torus FMZ with moving tests and growing prime sets

The exact literal zero-sum/Haar/Poisson remainder is identified with the
rational Fourier pairing before applying its uniform squared-height bound.
The constants precede the prime set, coefficients and frequencies. Therefore
the prime set and dimension may vary with height, subject to the displayed
weighted mass condition; no unrestricted growth claim is made.

Source: the user-provided FMZ comparison and the rational estimates proved in
ActualRationalFMZRate. The conditional analytic obligation remains exactly
UniformSelbergDensity (1/4). This supplies a quantitative version of the
existing prime-torus Fourier synthesis used in the RH phase program.
-/

noncomputable section
open Filter Zeta23
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.ActualPrimeTorusFMZ
open ActualZeroOrdinate PrimePhaseTorus PrimeTorusHaar

/-- An exact identification of the signed prime-torus remainder with the
rational Fourier pairing. Both main terms are retained before taking norms. -/
theorem fourierSeries_remainder_eq_rationalPairing {ι : Type*}
    (P : Finset ℕ) (a : ι → ℂ) (k : ι → ℕ → ℤ)
    (hP : ∀ p ∈ P, p.Prime) (ha : Summable (fun i => ‖a i‖)) (T : ℝ) :
    (sampleFunctional P T (fourierSeries a (fun i => fun p : P => k i p)) -
      (Ncount 0 T : ℂ) * haarIntegral
        (fourierSeries a (fun i => fun p : P => k i p))) / (T : ℂ) -
      haarIntegral (fourierSeries a (fun i => fun p : P => k i p) * primeDensity P) =
    Fourier.weightedFourierPairing a (fun i =>
      centeredRationalOrdinate T (primeNumerator P (k i)) (primeDenominator P (k i)) /
        (T : ℂ)) -
    Fourier.weightedFourierPairing a (fun i =>
      rationalFMZMain (primeNumerator P (k i)) (primeDenominator P (k i))) := by
  have hrhs := haarIntegral_fourierSeries_density a (fun i => fun p : P => k i p)
    ha (primeConstants P) (primeRadii P)
    (fun p => primeRadius_nonneg p) (fun p => primeRadius_lt_one (hP p p.property))
  simp_rw [← prime_rationalFMZMain_eq_axisMultiplier P _ hP] at hrhs
  change haarIntegral (fourierSeries a (fun i => fun p : P => k i p) * primeDensity P) =
    Fourier.weightedFourierPairing a (fun i =>
      rationalFMZMain (primeNumerator P (k i)) (primeDenominator P (k i))) at hrhs
  rw [hrhs]
  congr 1
  rw [sampleFunctional_apply, actualDiscrepancy_fourierSeries a
    (fun i => fun p : P => k i p) ha (primeOrbit P) T]
  apply tsum_congr
  intro i
  congr 2
  simpa only [sampleFunctional_apply, haarIntegral_character_eq] using
    centered_character_eq_rational P (k i) hP T

theorem summable_norm_of_primeModeWeight_sq {ι : Type*}
    (P : Finset ℕ) (a : ι → ℂ) (k : ι → ℕ → ℤ)
    (ha : Summable (fun i => ‖a i‖ * primeModeWeight P (k i) ^ 2)) :
    Summable (fun i => ‖a i‖) := by
  apply ha.of_norm_bounded
  intro i
  have hw := one_le_primeModeWeight P (k i)
  have hw2 : 1 ≤ primeModeWeight P (k i) ^ 2 := by nlinarith
  simpa only [norm_norm, mul_one] using
    mul_le_mul_of_nonneg_left hw2 (norm_nonneg (a i))

/-- A bound for centered rational modes transfers to prime-torus tests
with the same coefficient and the full squared-height Wiener mass. -/
theorem fourierSeries_remainder_le_of_mode_bound {ι : Type*} {T B : ℝ}
    (P : Finset ℕ) (a : ι → ℂ) (k : ι → ℕ → ℤ)
    (hP : ∀ p ∈ P, p.Prime)
    (ha : Summable (fun i => ‖a i‖ * primeModeWeight P (k i) ^ 2))
    (hmode : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m →
      ‖centeredRationalOrdinate T n m / (T : ℂ) - rationalFMZMain n m‖ ≤
        B * rationalModeWeight n m ^ 2) :
    ‖(sampleFunctional P T (fourierSeries a (fun i => fun p : P => k i p)) -
        (Ncount 0 T : ℂ) * haarIntegral
          (fourierSeries a (fun i => fun p : P => k i p))) / (T : ℂ) -
      haarIntegral (fourierSeries a (fun i => fun p : P => k i p) * primeDensity P)‖ ≤
      B * Fourier.weightedFourierMass a (fun i => primeModeWeight P (k i) ^ 2) := by
  rw [fourierSeries_remainder_eq_rationalPairing P a k hP
    (summable_norm_of_primeModeWeight_sq P a k ha)]
  exact rational_fourier_remainder_le_of_mode_bound a
    (fun i => primeNumerator P (k i)) (fun i => primeDenominator P (k i))
    (fun i => primeProduct_pos P (fun p => (k i p).toNat) hP)
    (fun i => primeProduct_pos P (fun p => (-k i p).toNat) hP) ha hmode

/-- Uniform quantitative prime-torus FMZ. The bound is independent of the
prime set, dimension, coefficients and frequencies; all are quantified after
the height threshold. The price is the explicit squared-height Wiener mass. -/
theorem eventually_fourierSeries_remainder_bound {ι : Type*}
    (hD : UniformSelbergDensity (1 / 4)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (P : Finset ℕ) (a : ι → ℂ) (k : ι → ℕ → ℤ),
      (∀ p ∈ P, p.Prime) →
      Summable (fun i => ‖a i‖ * primeModeWeight P (k i) ^ 2) →
      ‖(sampleFunctional P T (fourierSeries a (fun i => fun p : P => k i p)) -
          (Ncount 0 T : ℂ) * haarIntegral
            (fourierSeries a (fun i => fun p : P => k i p))) / (T : ℂ) -
        haarIntegral (fourierSeries a (fun i => fun p : P => k i p) * primeDensity P)‖ ≤
        (K / Real.log T) *
          Fourier.weightedFourierMass a (fun i => primeModeWeight P (k i) ^ 2) := by
  obtain ⟨K, hK, hb⟩ := eventually_centeredRationalOrdinate_remainder_rate hD
  refine ⟨K, hK, hb.mono ?_⟩
  intro T hT P a k hP ha
  exact fourierSeries_remainder_le_of_mode_bound P a k hP ha hT

/-- Unconditional quantitative prime-torus FMZ with one height threshold
for every prime set and summable squared-height Fourier test. -/
theorem eventually_fourierSeries_remainder_loglog {ι : Type*} :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (P : Finset ℕ) (a : ι → ℂ) (k : ι → ℕ → ℤ),
      (∀ p ∈ P, p.Prime) →
      Summable (fun i => ‖a i‖ * primeModeWeight P (k i) ^ 2) →
      ‖(sampleFunctional P T (fourierSeries a (fun i => fun p : P => k i p)) -
          (Ncount 0 T : ℂ) * haarIntegral
            (fourierSeries a (fun i => fun p : P => k i p))) / (T : ℂ) -
        haarIntegral (fourierSeries a (fun i => fun p : P => k i p) * primeDensity P)‖ ≤
        (K * horizontalLogRate T) *
          Fourier.weightedFourierMass a (fun i => primeModeWeight P (k i) ^ 2) := by
  obtain ⟨K, hK, hb⟩ := eventually_centeredRationalOrdinate_remainder_loglog
  refine ⟨K, hK, hb.mono ?_⟩
  intro T hT P a k hP ha
  exact fourierSeries_remainder_le_of_mode_bound P a k hP ha hT

/-- The prime set itself may grow, while coefficients and Fourier frequencies
move with height, provided the squared-height Wiener mass is o(log T). -/
theorem tendsto_moving_fourierSeries_remainder {ι : Type*}
    (P : ℝ → Finset ℕ) (a : ℝ → ι → ℂ) (k : ℝ → ι → ℕ → ℤ)
    (hP : ∀ T p, p ∈ P T → p.Prime)
    (ha : ∀ T, Summable (fun i => ‖a T i‖ * primeModeWeight (P T) (k T i) ^ 2))
    (hsmall : Tendsto (fun T : ℝ =>
      Fourier.weightedFourierMass (a T)
        (fun i => primeModeWeight (P T) (k T i) ^ 2) / Real.log T) atTop (𝓝 0))
    (hD : UniformSelbergDensity (1 / 4)) :
    Tendsto (fun T : ℝ =>
      (sampleFunctional (P T) T
          (fourierSeries (a T) (fun i => fun p : P T => k T i p)) -
        (Ncount 0 T : ℂ) * haarIntegral
          (fourierSeries (a T) (fun i => fun p : P T => k T i p))) / (T : ℂ) -
      haarIntegral (fourierSeries (a T) (fun i => fun p : P T => k T i p) *
        primeDensity (P T))) atTop (𝓝 0) := by
  obtain ⟨K, hK, hb⟩ := eventually_fourierSeries_remainder_bound (ι := ι) hD
  have hlim := hsmall.const_mul K
  simp only [mul_zero] at hlim
  apply squeeze_zero_norm' _ hlim
  filter_upwards [hb] with T hT
  simpa only [div_mul_eq_mul_div, mul_div_assoc] using
    hT (P T) (a T) (k T) (hP T) (ha T)

/-- Moving prime-torus FMZ using the unconditional horizontal energy scale
and the weighted Wiener mass of each height-dependent test. -/
theorem tendsto_moving_fourierSeries_remainder_loglog {ι : Type*}
    (P : ℝ → Finset ℕ) (a : ℝ → ι → ℂ) (k : ℝ → ι → ℕ → ℤ)
    (hP : ∀ T p, p ∈ P T → p.Prime)
    (ha : ∀ T, Summable (fun i => ‖a T i‖ * primeModeWeight (P T) (k T i) ^ 2))
    (hsmall : Tendsto (fun T : ℝ =>
      horizontalLogRate T * Fourier.weightedFourierMass (a T)
        (fun i => primeModeWeight (P T) (k T i) ^ 2)) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ =>
      (sampleFunctional (P T) T
          (fourierSeries (a T) (fun i => fun p : P T => k T i p)) -
        (Ncount 0 T : ℂ) * haarIntegral
          (fourierSeries (a T) (fun i => fun p : P T => k T i p))) / (T : ℂ) -
      haarIntegral (fourierSeries (a T) (fun i => fun p : P T => k T i p) *
        primeDensity (P T))) atTop (𝓝 0) := by
  obtain ⟨K, hK, hb⟩ := eventually_fourierSeries_remainder_loglog (ι := ι)
  have hlim := hsmall.const_mul K
  simp only [mul_zero] at hlim
  apply squeeze_zero_norm' _ hlim
  filter_upwards [hb] with T hT
  simpa only [mul_assoc] using
    hT (P T) (a T) (k T) (hP T) (ha T)

end RiemannResearch.Analysis.ActualPrimeTorusFMZ

#print axioms RiemannResearch.Analysis.ActualPrimeTorusFMZ.eventually_fourierSeries_remainder_bound
#print axioms RiemannResearch.Analysis.ActualPrimeTorusFMZ.tendsto_moving_fourierSeries_remainder
