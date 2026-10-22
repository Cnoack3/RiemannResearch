/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualPrimeTorusFMZ
import RiemannResearch.Analysis.FinitePrimeModeCoefficients

/-!
# Actual finite prime-torus Poisson density

Prime factorization identifies every arithmetic mode with the actual product
Haar coefficient of the sum of centered coordinate Poisson kernels. The final
polynomial FMZ limit keeps only the explicit Selberg density premise.
-/

noncomputable section
open Filter Zeta23
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.ActualPrimeTorusFMZ
open ActualZeroOrdinate PrimePhaseTorus PrimeTorusHaar

def primeConstants (P : Finset ℕ) : P → ℝ :=
  fun p => Real.log (p : ℝ) / (2 * Real.pi)

def primeRadii (P : Finset ℕ) : P → ℝ := fun p => primeRadius p

def primeDensity (P : Finset ℕ) : C(Torus P, ℂ) :=
  density (primeConstants P) (primeRadii P)

/-- Prime factorization identifies the actual arithmetic coefficient with
the Fourier coefficient of the actual sum of axis Poisson densities. -/
theorem prime_rationalFMZMain_eq_axisMultiplier
    (P : Finset ℕ) (k : ℕ → ℤ) (hP : ∀ p ∈ P, p.Prime) :
    rationalFMZMain (primeNumerator P k) (primeDenominator P k) =
      axisMultiplier (primeConstants P) (primeRadii P) (fun p : P => k p) := by
  classical
  by_cases hz : ∀ p ∈ P, k p = 0
  · have hND := (primeNumerator_eq_denominator_iff P k hP).mpr hz
    have hk : (fun p : P => k p) = 0 := (restrictedMode_eq_zero_iff P k).mpr hz
    rw [hND, hk, axisMultiplier_zero]
    simp [rationalFMZMain]
  · push_neg at hz
    obtain ⟨p, hp, hkp⟩ := hz
    by_cases hsingle : ∀ q ∈ P, q ≠ p → k q = 0
    · have hk : (fun q : P => k q) = Pi.single (⟨p, hp⟩ : P) (k p) := by
        funext q
        by_cases hqp : (q : ℕ) = p
        · have heq : q = (⟨p, hp⟩ : P) := Subtype.ext hqp
          subst q
          simp
        · have hne : q ≠ (⟨p, hp⟩ : P) := by
            intro h
            exact hqp (congrArg Subtype.val h)
          simp [Pi.single_apply, hne, Ne.symm hne, hsingle q q.property hqp]
      rw [hk, axisMultiplier_single]
      simpa [primeConstants, primeRadii, primeRadius,
        PoissonHaar.centeredPoissonMultiplier, hkp] using
        rationalFMZMain_prime_single_axis P k hP hp hkp hsingle
    · push_neg at hsingle
      obtain ⟨q, hq, hqp, hkq⟩ := hsingle
      have hpq' : (⟨p, hp⟩ : P) ≠ (⟨q, hq⟩ : P) := by
        intro h
        exact hqp (congrArg Subtype.val h).symm
      rw [rationalFMZMain_prime_eq_zero_of_two_nonzero
        P k hP hp hq hqp.symm hkp hkq]
      exact (axisMultiplier_eq_zero_of_two_nonzero
        (primeConstants P) (primeRadii P) (fun p : P => k p)
        (⟨p, hp⟩ : P) (⟨q, hq⟩ : P) hpq' hkp hkq).symm

theorem haarIntegral_character_primeDensity
    (P : Finset ℕ) (k : ℕ → ℤ) (hP : ∀ p ∈ P, p.Prime) :
    haarIntegral (character (fun p : P => k p) * primeDensity P) =
      rationalFMZMain (primeNumerator P k) (primeDenominator P k) := by
  rw [primeDensity, haarIntegral_character_density]
  · exact (prime_rationalFMZMain_eq_axisMultiplier P k hP).symm
  · intro p
    exact primeRadius_nonneg p
  · intro p
    exact primeRadius_lt_one (hP p p.property)

/-- The finite prime-torus FMZ theorem for every trigonometric polynomial,
with actual product Haar measure and the actual signed Poisson density.
The sole analytic premise is the classical Selberg density proposition. -/
theorem tendsto_centered_polynomial_div_poisson {ι : Type*}
    (P : Finset ℕ) (s : Finset ι) (a : ι → ℂ) (k : ι → ℕ → ℤ)
    (hP : ∀ p ∈ P, p.Prime) (hD : UniformSelbergDensity (1 / 4)) :
    Tendsto (fun T : ℝ =>
      (sampleFunctional P T (polynomial P s a k) -
        (Ncount 0 T : ℂ) * haarIntegral (polynomial P s a k)) / (T : ℂ))
      atTop (𝓝 (haarIntegral (polynomial P s a k * primeDensity P))) := by
  have hmain : haarIntegral (polynomial P s a k * primeDensity P) =
      ∑ i ∈ s,
        a i * rationalFMZMain (primeNumerator P (k i)) (primeDenominator P (k i)) := by
    simp only [polynomial, Finset.sum_mul, smul_mul_assoc, map_sum, map_smul,
      smul_eq_mul, haarIntegral_character_primeDensity P _ hP]
  rw [hmain]
  exact tendsto_centered_polynomial_div P s a k hP hD

end RiemannResearch.Analysis.ActualPrimeTorusFMZ
