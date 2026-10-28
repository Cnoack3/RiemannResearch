/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.PrimeTorusPlancherel
import RiemannResearch.Analysis.PrimeTorusFourierDecay
import RiemannResearch.Analysis.ArithmeticWeightedFourierRemainder

/-!
# Exact actual-zero Gram identities on A2

Source: the user's prime-torus Plancherel question (2026-10-28),
Mathlib finite-torus Fourier theory, and the cited project modules.
-/


noncomputable section
open Filter Zeta23
open scoped Topology BigOperators ComplexConjugate
namespace RiemannResearch.Analysis.ActualPrimeTorusFMZ
open ActualZeroOrdinate PrimePhaseTorus PrimeTorusHaar FiniteTorusWiener

abbrev A2 (P : Finset ℕ) :=
  {f : C(Torus P, ℂ) // MemA2 (fun p : P => Real.log (p : ℝ)) f}

theorem primeLog_nonneg (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∀ p : P, 0 ≤ Real.log (p : ℝ) := by
  intro p
  exact Real.log_nonneg (by exact_mod_cast (hP p p.property).one_lt.le)

theorem native_weight_eq (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k : P → ℤ) :
    weight (fun p : P => Real.log (p : ℝ)) k =
      primeModeWeight P (ambientPrimeMode P k) := by
  rw [primeModeWeight_eq P (ambientPrimeMode P k) hP]
  unfold weight height
  congr 1
  conv_rhs => rw [← Finset.sum_coe_sort]
  simp only [ambientPrimeMode_apply]

theorem summable_prime_weighted (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (f : C(Torus P, ℂ))
    (hf : MemA2 (fun p : P => Real.log (p : ℝ)) f) :
    Summable (fun k : P → ℤ =>
      ‖coeff f k‖ * primeModeWeight P (ambientPrimeMode P k)^2) := by
  simpa only [MemA2, native_weight_eq P hP] using hf

theorem a2Mass_eq_weightedFourierMass
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (f : C(Torus P, ℂ)) :
    a2Mass (fun p : P => Real.log (p : ℝ)) f =
      Fourier.weightedFourierMass (coeff f)
        (fun k => primeModeWeight P (ambientPrimeMode P k)^2) := by
  simp only [a2Mass, Fourier.weightedFourierMass, native_weight_eq P hP]

theorem sampleFunctional_fourierSeries
    {κ : Type*} (P : Finset ℕ) (T : ℝ)
    (a : κ → ℂ) (k : κ → P → ℤ)
    (ha : Summable (fun j => ‖a j‖)) :
    sampleFunctional P T (fourierSeries a k) =
      ∑' j, a j * ordinateSum T
        (primeFrequency P (ambientPrimeMode P (k j))) := by
  classical
  calc
    _ = actualSampleCLM (primeOrbit P) T (fourierSeries a k) := by
      simp only [actualSampleCLM_apply, sampleFunctional_apply]
    _ = ∑' j, actualSampleCLM (primeOrbit P) T (a j • character (k j)) := by
      unfold fourierSeries
      exact (actualSampleCLM (primeOrbit P) T).map_tsum
        (summable_fourierSeries a k ha)
    _ = _ := by
      apply tsum_congr
      intro j
      have hc := sampleFunctional_character P (ambientPrimeMode P (k j)) T
      simp only [ambientPrimeMode_apply] at hc
      rw [map_smul, smul_eq_mul, actualSampleCLM_apply,
        ← sampleFunctional_apply, hc]

theorem sampleFunctional_a2_gram
    (P : Finset ℕ) (T : ℝ) (hP : ∀ p ∈ P, p.Prime)
    (f g : C(Torus P, ℂ))
    (hf : MemA2 (fun p : P => Real.log (p : ℝ)) f)
    (hg : MemA2 (fun p : P => Real.log (p : ℝ)) g) :
    sampleFunctional P T (f * star g) =
      ∑' j : (P → ℤ) × (P → ℤ),
        coeff f j.1 * star (coeff g j.2) *
          ordinateSum T (primeFrequency P (ambientPrimeMode P (j.1 - j.2))) := by
  rw [product_eq_pairSeries _ (primeLog_nonneg P hP) f g hf hg]
  exact sampleFunctional_fourierSeries P T (pairCoeff f g) pairMode
    (summable_pairCoeff_norm _ (primeLog_nonneg P hP) f g hf hg)

theorem sampleFunctional_energy_apply (P : Finset ℕ) (T : ℝ)
    (f : C(Torus P, ℂ)) :
    sampleFunctional P T (f * star f) =
      ActualZeroOrdinate.sum T
        (fun ρ => ((‖f (primeOrbit P ρ.im)‖^2 : ℝ) : ℂ)) := by
  simp only [sampleFunctional_apply, normSq_product_apply]

theorem countNormalized_a2_gram
    (P : Finset ℕ) (T : ℝ) (hP : ∀ p ∈ P, p.Prime)
    (f g : C(Torus P, ℂ))
    (hf : MemA2 (fun p : P => Real.log (p : ℝ)) f)
    (hg : MemA2 (fun p : P => Real.log (p : ℝ)) g) :
    sampleFunctional P T (f * star g) / (Ncount 0 T : ℂ) =
      ∑' j : (P → ℤ) × (P → ℤ),
        (coeff f j.1 * star (coeff g j.2) *
          ordinateSum T (primeFrequency P (ambientPrimeMode P (j.1 - j.2)))) /
            (Ncount 0 T : ℂ) := by
  rw [sampleFunctional_a2_gram P T hP f g hf hg, tsum_div_const]

theorem primeFrequency_ambient_sub (P : Finset ℕ) (k l : P → ℤ) :
    primeFrequency P (ambientPrimeMode P (k - l)) =
      primeFrequency P (ambientPrimeMode P k) -
        primeFrequency P (ambientPrimeMode P l) := by
  classical
  unfold primeFrequency
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [ambientPrimeMode_apply P (k - l) ⟨p, hp⟩,
    ambientPrimeMode_apply P k ⟨p, hp⟩,
    ambientPrimeMode_apply P l ⟨p, hp⟩]
  simp only [Pi.sub_apply, Int.cast_sub, mul_sub, sub_mul]

end RiemannResearch.Analysis.ActualPrimeTorusFMZ
