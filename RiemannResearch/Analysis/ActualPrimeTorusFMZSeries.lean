/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualPrimeTorusFMZPoisson
import RiemannResearch.Analysis.ActualRationalFMZDomination
import RiemannResearch.Analysis.PrimeTorusFourierSeries

/-!
# Joint prime-torus FMZ for weighted absolutely convergent Fourier series

The test function is an actual continuous Fourier series. Its exact weighted
summability norm and actual zero sampling are connected to product Haar and
the explicit prime Poisson density. Only Selberg density remains an analytic
premise. No arithmetic limit, Haar coefficient, or FMZ limit is assumed.
-/

noncomputable section
open Filter Zeta23
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.ActualPrimeTorusFMZ
open ActualZeroOrdinate PrimePhaseTorus PrimeTorusHaar

/-- The arithmetic weight used by the proved uniform mode domination. -/
def primeModeWeight (P : Finset ℕ) (k : ℕ → ℤ) : ℝ :=
  rationalModeWeight (primeNumerator P k) (primeDenominator P k)

/-- The rational weight is exactly the square of the natural prime-logarithm
Fourier height, with no Diophantine denominator hidden in the test norm. -/
theorem primeModeWeight_eq (P : Finset ℕ) (k : ℕ → ℤ)
    (hP : ∀ p ∈ P, p.Prime) :
    primeModeWeight P k =
      1 + (∑ p ∈ P, |(k p : ℝ)| * Real.log p) ^ 2 := by
  have hheight : Real.log (primeNumerator P k : ℝ) +
      Real.log (primeDenominator P k : ℝ) =
      ∑ p ∈ P, |(k p : ℝ)| * Real.log p := by
    rw [primeNumerator, primeDenominator, primeProduct_log P _ hP,
      primeProduct_log P _ hP, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have hi : ((k p).toNat : ℝ) + ((-k p).toNat : ℝ) = |(k p : ℝ)| := by
      by_cases hk : 0 ≤ k p
      · have hkR : (0 : ℝ) ≤ (k p : ℝ) := by exact_mod_cast hk
        have hneg : (-k p).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
        have hcast : ((k p).toNat : ℝ) = (k p : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg hk
        simp [hneg, hcast, abs_of_nonneg hkR]
      · have hkR : (k p : ℝ) < 0 := by exact_mod_cast lt_of_not_ge hk
        have hpos : (k p).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
        have hcast : ((-k p).toNat : ℝ) = -(k p : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ -k p by omega)
        simp [hpos, hcast, abs_of_neg hkR]
    rw [← add_mul, hi]
  unfold primeModeWeight rationalModeWeight
  rw [hheight]

theorem one_le_primeModeWeight (P : Finset ℕ) (k : ℕ → ℤ) :
    1 ≤ primeModeWeight P k := by
  unfold primeModeWeight rationalModeWeight
  linarith [sq_nonneg (Real.log (primeNumerator P k : ℝ) +
    Real.log (primeDenominator P k : ℝ))]

theorem summable_norm_of_primeModeWeight {ι : Type*}
    (P : Finset ℕ) (a : ι → ℂ) (k : ι → ℕ → ℤ)
    (ha : Summable (fun i => ‖a i‖ * primeModeWeight P (k i))) :
    Summable (fun i => ‖a i‖) := by
  apply ha.of_norm_bounded
  intro i
  simpa only [norm_norm, mul_one] using mul_le_mul_of_nonneg_left
    (one_le_primeModeWeight P (k i)) (norm_nonneg (a i))

/-- Actual joint prime-torus FMZ for the arithmetic weighted Wiener class.
The function is an actual continuous Fourier series. Both the left-hand zero
sum and right-hand product-Haar integral are literal, with all constant,
prime-axis and mixed-frequency contributions identified. The only analytic
premise is the named classical Selberg zero-density estimate. -/
theorem tendsto_centered_fourierSeries_div_poisson {ι : Type*}
    (P : Finset ℕ) (a : ι → ℂ) (k : ι → ℕ → ℤ)
    (hP : ∀ p ∈ P, p.Prime)
    (ha : Summable (fun i => ‖a i‖ * primeModeWeight P (k i)))
    (hD : UniformSelbergDensity (1 / 4)) :
    Tendsto (fun T : ℝ =>
      (sampleFunctional P T (fourierSeries a (fun i => fun p : P => k i p)) -
        (Ncount 0 T : ℂ) * haarIntegral
          (fourierSeries a (fun i => fun p : P => k i p))) / (T : ℂ))
      atTop (𝓝 (haarIntegral
        (fourierSeries a (fun i => fun p : P => k i p) * primeDensity P))) := by
  have ha0 := summable_norm_of_primeModeWeight P a k ha
  have h := tendsto_rational_fourier_series_of_uniformSelberg a
    (fun i => primeNumerator P (k i)) (fun i => primeDenominator P (k i))
    (fun i => primeProduct_pos P (fun p => (k i p).toNat) hP)
    (fun i => primeProduct_pos P (fun p => (-k i p).toNat) hP) ha hD
  have hrhs := haarIntegral_fourierSeries_density a (fun i => fun p : P => k i p)
    ha0 (primeConstants P) (primeRadii P)
    (fun p => primeRadius_nonneg p) (fun p => primeRadius_lt_one (hP p p.property))
  simp_rw [← prime_rationalFMZMain_eq_axisMultiplier P _ hP] at hrhs
  change haarIntegral (fourierSeries a (fun i => fun p : P => k i p) * primeDensity P) = _ at hrhs
  rw [hrhs]
  convert h using 1
  funext T
  rw [sampleFunctional_apply, actualDiscrepancy_fourierSeries a
    (fun i => fun p : P => k i p) ha0 (primeOrbit P) T]
  apply tsum_congr
  intro i
  congr 2
  simpa only [sampleFunctional_apply, haarIntegral_character_eq] using
    centered_character_eq_rational P (k i) hP T

end RiemannResearch.Analysis.ActualPrimeTorusFMZ

#print axioms RiemannResearch.Analysis.ActualPrimeTorusFMZ.tendsto_centered_fourierSeries_div_poisson
