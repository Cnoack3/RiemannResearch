/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.PrimeTorusFourierDecay
import RiemannResearch.Analysis.PrimeTorusFourierInversion

/-!
# Joint prime-torus FMZ for continuous functions with Fourier decay

This is the classical finite-prime specialization with the strengthened strict
Fourier-decay threshold B > card(P) + 1. Arithmetic limits, product Haar,
Poisson coefficients, uniform Fourier domination and Fourier reconstruction
are proved in the imported development. The remaining analytic premise is
exactly UniformSelbergDensity (1/4), whose unconditional provider is not yet
formalized in this project.
-/

noncomputable section
open Filter Zeta23
open scoped Topology

namespace RiemannResearch.Analysis.ActualPrimeTorusFMZ
open ActualZeroOrdinate PrimeTorusHaar

/-- The full finite-prime-torus FMZ conclusion for an arbitrary continuous
test function with the strengthened Fourier decay. Selberg remains explicit. -/
theorem tendsto_centered_continuous_div_poisson_of_selberg
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (f : C(Torus P, ℂ))
    (C B : ℝ) (hC : 0 ≤ C) (hB : (P.card : ℝ) + 1 < B)
    (hf : ∀ k : P → ℤ,
      ‖UnitAddTorus.mFourierCoeff (f : Torus P → ℂ) k‖ ≤ C * (1 + ‖k‖) ^ (-B))
    (hD : UniformSelbergDensity (1 / 4)) :
    Tendsto (fun T : ℝ =>
      (sampleFunctional P T f - (Ncount 0 T : ℂ) * haarIntegral f) / (T : ℂ))
      atTop (𝓝 (haarIntegral (f * primeDensity P))) := by
  have ha := summable_primeModeWeight_of_fourierDecay P hP
    (UnitAddTorus.mFourierCoeff (f : Torus P → ℂ)) C B hC hB hf
  have ha0 := summable_norm_of_primeModeWeight P
    (UnitAddTorus.mFourierCoeff (f : Torus P → ℂ)) (ambientPrimeMode P) ha
  have h := tendsto_centered_fourierSeries_div_poisson P
    (UnitAddTorus.mFourierCoeff (f : Torus P → ℂ)) (ambientPrimeMode P) hP ha hD
  have hseries := fourierSeries_mFourierCoeff f ha0
  have hmodes : (fun i : P → ℤ => fun p : P => ambientPrimeMode P i p) = id := by
    funext i p
    exact ambientPrimeMode_apply P i p
  rw [hmodes, hseries] at h
  exact h

end RiemannResearch.Analysis.ActualPrimeTorusFMZ

#print axioms RiemannResearch.Analysis.ActualPrimeTorusFMZ.tendsto_centered_continuous_div_poisson_of_selberg
