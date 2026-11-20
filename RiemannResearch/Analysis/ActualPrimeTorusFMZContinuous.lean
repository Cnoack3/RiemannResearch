/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.PrimeTorusFourierDecay
import RiemannResearch.Analysis.PrimeTorusFourierInversion
import RiemannResearch.Analysis.ActualPrimeTorusFMZRate
import RiemannResearch.Analysis.ActualPrimeTorusFMZInterpolation
import RiemannResearch.Analysis.PrimeTorusHaarSpecialization

/-!
# Joint prime-torus FMZ for continuous functions with Fourier decay

This is the classical finite-prime specialization with the strengthened strict
Fourier-decay threshold B > card(P) + 1. Arithmetic limits, product Haar,
Poisson coefficients, uniform Fourier domination and Fourier reconstruction
are proved in the imported development. Fractional Wiener interpolation
removes the density premise at every strict exponent B > card(P) + 1.

The squared-height Fourier norm additionally gives an O(T/log T) remainder
under the one-log Selberg density premise when B > card(P) + 2. Exact product-Haar identities
yield cancellation of both main terms for products with two distinct centered factors.
-/

noncomputable section
open Filter Zeta23
open scoped Topology

namespace RiemannResearch.Analysis.ActualPrimeTorusFMZ
open ActualZeroOrdinate PrimeTorusHaar

/-- The full finite-prime-torus FMZ conclusion for an arbitrary continuous
test function with the strict decay threshold B > dimension + 1. -/
theorem tendsto_centered_continuous_div_poisson
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (f : C(Torus P, ℂ))
    (C B : ℝ) (hC : 0 ≤ C) (hB : (P.card : ℝ) + 1 < B)
    (hf : ∀ k : P → ℤ,
      ‖UnitAddTorus.mFourierCoeff (f : Torus P → ℂ) k‖ ≤ C * (1 + ‖k‖) ^ (-B)) :
    Tendsto (fun T : ℝ =>
      (sampleFunctional P T f - (Ncount 0 T : ℂ) * haarIntegral f) / (T : ℂ))
      atTop (𝓝 (haarIntegral (f * primeDensity P))) := by
  have ha := summable_primeModeWeight_of_fourierDecay P hP
    (UnitAddTorus.mFourierCoeff (f : Torus P → ℂ)) C B hC hB hf
  have ha0 := summable_norm_of_primeModeWeight P
    (UnitAddTorus.mFourierCoeff (f : Torus P → ℂ)) (ambientPrimeMode P) ha
  obtain ⟨s, hs, hs'⟩ := exists_between
    (lt_min (by norm_num : (1 : ℝ) < 2) (show 1 < B - (P.card : ℝ) by linarith))
  obtain ⟨hs2, hsB⟩ := lt_min_iff.mp hs'
  have hfrac := summable_primeModeWeight_rpow_of_fourierDecay (s := s) (by linarith) P hP
    (UnitAddTorus.mFourierCoeff (f : Torus P → ℂ)) C B hC (by linarith) hf
  have h := tendsto_centered_fourierSeries_div_poisson_of_fractional hs hs2.le P
    (UnitAddTorus.mFourierCoeff (f : Torus P → ℂ)) (ambientPrimeMode P) hP hfrac
  have hseries := fourierSeries_mFourierCoeff f ha0
  have hmodes : (fun i : P → ℤ => fun p : P => ambientPrimeMode P i p) = id := by
    funext i p
    exact ambientPrimeMode_apply P i p
  rw [hmodes, hseries] at h
  exact h

/-- Compatibility form of the continuous FMZ limit with its original density argument. -/
theorem tendsto_centered_continuous_div_poisson_of_selberg
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (f : C(Torus P, ℂ))
    (C B : ℝ) (hC : 0 ≤ C) (hB : (P.card : ℝ) + 1 < B)
    (hf : ∀ k : P → ℤ,
      ‖UnitAddTorus.mFourierCoeff (f : Torus P → ℂ) k‖ ≤ C * (1 + ‖k‖) ^ (-B))
    (hD : UniformSelbergDensity (1 / 4)) :
    Tendsto (fun T : ℝ =>
      (sampleFunctional P T f - (Ncount 0 T : ℂ) * haarIntegral f) / (T : ℂ))
      atTop (𝓝 (haarIntegral (f * primeDensity P))) := by
  clear hD
  exact tendsto_centered_continuous_div_poisson P hP f C B hC hB hf

/-- A smooth tensor interaction with two centered coordinates has neither a
Haar main term nor an order-T Poisson correction. The actual-zero conclusion
uses unconditional fractional Wiener summability. -/
theorem tendsto_productTest_div_zero_of_two_centered
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (f : P → PoissonHaar.CircleFunction)
    (C B : ℝ) (hC : 0 ≤ C) (hB : (P.card : ℝ) + 1 < B)
    (hf : ∀ k : P → ℤ,
      ‖UnitAddTorus.mFourierCoeff (productTest f : Torus P → ℂ) k‖ ≤
        C * (1 + ‖k‖) ^ (-B))
    (i j : P) (hij : i ≠ j)
    (hi : PoissonHaar.haarIntegralCLM (f i) = 0)
    (hj : PoissonHaar.haarIntegralCLM (f j) = 0) :
    Tendsto (fun T : ℝ => sampleFunctional P T (productTest f) / (T : ℂ))
      atTop (𝓝 0) := by
  have h := tendsto_centered_continuous_div_poisson
    P hP (productTest f) C B hC hB hf
  have hm : haarIntegral (productTest f) = 0 :=
    haarIntegral_productTest_eq_zero f i hi
  have hc : haarIntegral (productTest f * primeDensity P) = 0 := by
    change haarIntegral (productTest f * density (primeConstants P) (primeRadii P)) = 0
    exact haarIntegral_productTest_density_eq_zero_of_two_centered
      f (primeConstants P) (primeRadii P) i j hij hi hj
  simpa only [hm, hc, mul_zero, sub_zero] using h



/-- The quoted B > card(P) + 2 smoothness threshold gives a quantitative
O(T / log T) remainder after subtracting both exact FMZ main terms. The
displayed squared Fourier mass retains the dependence on the test function. -/
theorem eventually_continuous_remainder_bound_of_selberg
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (f : C(Torus P, ℂ))
    (C B : ℝ) (hC : 0 ≤ C) (hB : (P.card : ℝ) + 2 < B)
    (hf : ∀ k : P → ℤ,
      ‖UnitAddTorus.mFourierCoeff (f : Torus P → ℂ) k‖ ≤ C * (1 + ‖k‖) ^ (-B))
    (hD : UniformSelbergDensity (1 / 4)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop,
      ‖(sampleFunctional P T f - (Ncount 0 T : ℂ) * haarIntegral f) / (T : ℂ) -
        haarIntegral (f * primeDensity P)‖ ≤
        (K / Real.log T) *
          Fourier.weightedFourierMass (UnitAddTorus.mFourierCoeff (f : Torus P → ℂ))
            (fun k => primeModeWeight P (ambientPrimeMode P k) ^ 2) := by
  have ha := summable_primeModeWeight_sq_of_fourierDecay P hP
    (UnitAddTorus.mFourierCoeff (f : Torus P → ℂ)) C B hC hB hf
  have ha0 := summable_norm_of_primeModeWeight_sq P
    (UnitAddTorus.mFourierCoeff (f : Torus P → ℂ)) (ambientPrimeMode P) ha
  have hseries := fourierSeries_mFourierCoeff f ha0
  have hmodes : (fun i : P → ℤ => fun p : P => ambientPrimeMode P i p) = id := by
    funext i p
    exact ambientPrimeMode_apply P i p
  obtain ⟨K, hK, hb⟩ := eventually_fourierSeries_remainder_bound (ι := P → ℤ) hD
  refine ⟨K, hK, hb.mono ?_⟩
  intro T hT
  have h := hT P (UnitAddTorus.mFourierCoeff (f : Torus P → ℂ))
    (ambientPrimeMode P) hP ha
  rw [hmodes, hseries] at h
  exact h

/-- With two centered factors, both main terms vanish exactly. Under the
squared-moment decay threshold the remaining actual-zero sum is O(T / log T). -/
theorem eventually_productTest_div_bound_of_two_centered
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (f : P → PoissonHaar.CircleFunction)
    (C B : ℝ) (hC : 0 ≤ C) (hB : (P.card : ℝ) + 2 < B)
    (hf : ∀ k : P → ℤ,
      ‖UnitAddTorus.mFourierCoeff (productTest f : Torus P → ℂ) k‖ ≤
        C * (1 + ‖k‖) ^ (-B))
    (i j : P) (hij : i ≠ j)
    (hi : PoissonHaar.haarIntegralCLM (f i) = 0)
    (hj : PoissonHaar.haarIntegralCLM (f j) = 0)
    (hD : UniformSelbergDensity (1 / 4)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop,
      ‖sampleFunctional P T (productTest f) / (T : ℂ)‖ ≤
        (K / Real.log T) * Fourier.weightedFourierMass
          (UnitAddTorus.mFourierCoeff (productTest f : Torus P → ℂ))
          (fun k => primeModeWeight P (ambientPrimeMode P k) ^ 2) := by
  have h := eventually_continuous_remainder_bound_of_selberg
    P hP (productTest f) C B hC hB hf hD
  have hm : haarIntegral (productTest f) = 0 :=
    haarIntegral_productTest_eq_zero f i hi
  have hc : haarIntegral (productTest f * primeDensity P) = 0 := by
    change haarIntegral (productTest f * density (primeConstants P) (primeRadii P)) = 0
    exact haarIntegral_productTest_density_eq_zero_of_two_centered
      f (primeConstants P) (primeRadii P) i j hij hi hj
  simpa only [hm, hc, mul_zero, sub_zero] using h

end RiemannResearch.Analysis.ActualPrimeTorusFMZ

#print axioms RiemannResearch.Analysis.ActualPrimeTorusFMZ.tendsto_centered_continuous_div_poisson
