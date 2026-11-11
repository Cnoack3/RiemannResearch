/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ActualPrimeTorusHorizontalEndpoint
import RiemannResearch.Analysis.ActualPrimeTorusEnergy

/-!
# Literal actual-zero, Haar and horizontal-energy expansion at A₂

Source: FRZ_Strengthening_2026-11-10, equations (34)--(35). The signed
directional second derivative is an actual continuous Fourier series. Its
integral against the actual positive horizontal-energy measure is identified
exactly, including the factor one half and every zero multiplicity. The
endpoint limit then follows from the checked rational endpoint theorem.

No limiting horizontal measure is assumed for the endpoint remainder. When
a weakly convergent subsequence is supplied, the same subsequence applies to
every A₂ test. The classical density input is explicit; this is not RH.
-/

noncomputable section
open Filter MeasureTheory Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ActualPrimeTorusFMZ
open ActualZeroOrdinate PrimePhaseTorus PrimeTorusHaar ActualPrimeTorusEnergy

/-- The literal centered and prime-density-corrected statistic at third scale. -/
def thirdFunctional (P : Finset ℕ) (T : ℝ) (f : C(Torus P, ℂ)) : ℂ :=
  (Real.log T : ℂ) *
    ((sampleFunctional P T f - (Ncount 0 T : ℂ) * haarIntegral f) / (T : ℂ) -
      haarIntegral (f * primeDensity P))

/-- Fourier realization of the second derivative along the prime flow. -/
def directionalSecondSeries {ι : Type*}
    (P : Finset ℕ) (a : ι → ℂ) (k : ι → ℕ → ℤ) : C(Torus P, ℂ) :=
  fourierSeries (fun i => -((primeFrequency P (k i) : ℂ) ^ 2) * a i)
    (fun i (p : P) => k i p)

theorem primeFrequency_sq_le_weight (P : Finset ℕ) (k : ℕ → ℤ)
    (hP : ∀ p ∈ P, p.Prime) :
    primeFrequency P k ^ 2 ≤ primeModeWeight P k ^ 2 := by
  have h := rational_log_abs_le_weight (primeNumerator P k) (primeDenominator P k)
    (primeProduct_pos P _ hP) (primeProduct_pos P _ hP)
  rw [prime_log_ratio_eq_frequency P k hP] at h
  change |primeFrequency P k| ≤ primeModeWeight P k at h
  nlinarith [sq_abs (primeFrequency P k), abs_nonneg (primeFrequency P k),
    one_le_primeModeWeight P k]

theorem summable_directionalSecondCoefficients {ι : Type*}
    (P : Finset ℕ) (a : ι → ℂ) (k : ι → ℕ → ℤ)
    (hP : ∀ p ∈ P, p.Prime)
    (ha : Summable (fun i => ‖a i‖ * primeModeWeight P (k i) ^ 2)) :
    Summable (fun i => ‖-((primeFrequency P (k i) : ℂ) ^ 2) * a i‖) := by
  apply ha.of_norm_bounded
  intro i
  rw [norm_norm, norm_mul, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right
    (primeFrequency_sq_le_weight P (k i) hP) (norm_nonneg (a i))

theorem norm_centeredRationalOrdinate_le_two_count (T : ℝ) (n m : ℕ) :
    ‖centeredRationalOrdinate T n m‖ ≤ 2 * (Ncount 0 T : ℝ) := by
  unfold centeredRationalOrdinate
  have h := norm_ordinateSum_le_count T (Real.log ((n : ℝ) / (m : ℝ)))
  by_cases hnm : n = m
  · rw [if_pos hnm]
    have hb := norm_sub_le (ordinateSum T (Real.log ((n : ℝ) / (m : ℝ))))
      (Ncount 0 T : ℂ)
    have hc : ‖(Ncount 0 T : ℂ)‖ = (Ncount 0 T : ℝ) := by simp
    rw [hc] at hb
    linarith
  · rw [if_neg hnm, sub_zero]
    exact h.trans (by have hn : (0 : ℝ) ≤ Ncount 0 T := Nat.cast_nonneg _; linarith)

theorem summable_prime_centeredOrdinate {ι : Type*}
    (P : Finset ℕ) (a : ι → ℂ) (k : ι → ℕ → ℤ)
    (ha : Summable (fun i => ‖a i‖)) (T : ℝ) (hT : 0 < T) :
    Summable (fun i => a i *
      (centeredRationalOrdinate T (primeNumerator P (k i)) (primeDenominator P (k i)) /
        (T : ℂ))) := by
  apply (ha.mul_left (2 * (Ncount 0 T : ℝ) / T)).of_norm_bounded
  intro i
  rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
  calc
    _ ≤ ‖a i‖ * (2 * (Ncount 0 T : ℝ) / T) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (norm_centeredRationalOrdinate_le_two_count T _ _) hT.le)
        (norm_nonneg _)
    _ = _ := by ring

theorem summable_prime_main {ι : Type*}
    (P : Finset ℕ) (a : ι → ℂ) (k : ι → ℕ → ℤ)
    (hP : ∀ p ∈ P, p.Prime)
    (ha : Summable (fun i => ‖a i‖ * primeModeWeight P (k i) ^ 2)) :
    Summable (fun i => a i * rationalFMZMain
      (primeNumerator P (k i)) (primeDenominator P (k i))) := by
  apply ha.of_norm_bounded
  intro i
  rw [norm_mul]
  have hb := rationalFMZMain_norm_le_weight (primeNumerator P (k i))
    (primeDenominator P (k i)) (primeProduct_pos P _ hP) (primeProduct_pos P _ hP)
  change ‖rationalFMZMain (primeNumerator P (k i)) (primeDenominator P (k i))‖ ≤
    primeModeWeight P (k i) at hb
  have hw := one_le_primeModeWeight P (k i)
  exact mul_le_mul_of_nonneg_left (hb.trans (by nlinarith)) (norm_nonneg _)

theorem summable_prime_horizontalCorrection {ι : Type*}
    (P : Finset ℕ) (a : ι → ℂ) (k : ι → ℕ → ℤ)
    (hP : ∀ p ∈ P, p.Prime)
    (ha : Summable (fun i => ‖a i‖ * primeModeWeight P (k i) ^ 2))
    (T : ℝ) (hT : 0 < T) :
    Summable (fun i => a i * rationalHorizontalCorrection T
      (primeNumerator P (k i)) (primeDenominator P (k i))) := by
  apply (ha.mul_left (horizontalEnergy T / (2 * T))).of_norm_bounded
  intro i
  rw [rationalHorizontalCorrection, prime_log_ratio_eq_frequency P (k i) hP,
    norm_mul, norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
  calc
    _ ≤ ‖a i‖ * (primeModeWeight P (k i) ^ 2 / 2 * (horizontalEnergy T / T)) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact mul_le_mul
        (div_le_div_of_nonneg_right (primeFrequency_sq_le_weight P (k i) hP) (by norm_num))
        (div_le_div_of_nonneg_right (norm_evenHorizontalMoment_one_le T _) hT.le)
        (by positivity) (by positivity)
    _ = _ := by ring

/-- Exact identity of the literal derivative integral with the complete
signed Fourier correction. No density estimate is needed for this identity. -/
theorem directionalSecond_integral_exact {ι : Type*}
    (P : Finset ℕ) (a : ι → ℂ) (k : ι → ℕ → ℤ)
    (hP : ∀ p ∈ P, p.Prime)
    (ha : Summable (fun i => ‖a i‖ * primeModeWeight P (k i) ^ 2))
    (T : ℝ) (hT : 1 < T) :
    (∫ x, directionalSecondSeries P a k x ∂energyMeasure P T) =
      -2 * (Real.log T : ℂ) * ∑' i, a i * rationalHorizontalCorrection T
        (primeNumerator P (k i)) (primeDenominator P (k i)) := by
  rw [directionalSecondSeries, integral_fourierSeries_energyMeasure P T hT _ k
    (summable_directionalSecondCoefficients P a k hP ha), ← tsum_mul_left]
  apply tsum_congr
  intro i
  rw [rationalHorizontalCorrection, prime_log_ratio_eq_frequency P (k i) hP]
  ring

/-- Literal sample/Haar/arithmetic/energy identity, before passing to limits. -/
theorem thirdFunctional_sub_energy_exact {ι : Type*}
    (P : Finset ℕ) (a : ι → ℂ) (k : ι → ℕ → ℤ)
    (hP : ∀ p ∈ P, p.Prime)
    (ha : Summable (fun i => ‖a i‖ * primeModeWeight P (k i) ^ 2))
    (T : ℝ) (hT : 1 < T) :
    thirdFunctional P T (fourierSeries a (fun i (p : P) => k i p)) -
        (1 / 2 : ℂ) * (∫ x, directionalSecondSeries P a k x ∂energyMeasure P T) =
      (Real.log T : ℂ) * ∑' i, a i * correctedRationalRemainder T
        (primeNumerator P (k i)) (primeDenominator P (k i)) := by
  have ha0 := summable_norm_of_primeModeWeight_sq P a k ha
  have hT0 : 0 < T := by linarith
  have hz := summable_prime_centeredOrdinate P a k ha0 T hT0
  have hb := summable_prime_main P a k hP ha
  have hh := summable_prime_horizontalCorrection P a k hP ha T hT0
  rw [thirdFunctional, fourierSeries_remainder_eq_rationalPairing P a k hP ha0 T,
    directionalSecond_integral_exact P a k hP ha T hT]
  simp only [Fourier.weightedFourierPairing, correctedRationalRemainder, mul_add, mul_sub]
  rw [(hz.sub hb).tsum_add hh, hz.tsum_sub hb]
  ring

/-- A₂ endpoint for the actual statistic and the actual horizontal measure. -/
theorem tendsto_thirdFunctional_sub_energy {ι : Type*}
    (P : Finset ℕ) (a : ι → ℂ) (k : ι → ℕ → ℤ)
    (hP : ∀ p ∈ P, p.Prime)
    (ha : Summable (fun i => ‖a i‖ * primeModeWeight P (k i) ^ 2))
    (hD : UniformSelbergDensity (1 / 4)) :
    Tendsto (fun T : ℝ =>
      thirdFunctional P T (fourierSeries a (fun i (p : P) => k i p)) -
        (1 / 2 : ℂ) * (∫ x, directionalSecondSeries P a k x ∂energyMeasure P T))
      atTop (𝓝 0) := by
  apply (tendsto_prime_correctedFourier_endpoint P a k hP ha hD).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  exact (thirdFunctional_sub_energy_exact P a k hP ha T hT).symm

/-- Every weak energy subsequence yields the literal third correction for
all A₂ tests; the subsequence need not depend on the chosen coefficients. -/
theorem thirdFunctional_tendsto_of_energy_subsequence {ι : Type*}
    (P : Finset ℕ) (a : ι → ℂ) (k : ι → ℕ → ℤ)
    (hP : ∀ p ∈ P, p.Prime)
    (ha : Summable (fun i => ‖a i‖ * primeModeWeight P (k i) ^ 2))
    (hD : UniformSelbergDensity (1 / 4))
    (τ : ℕ → ℝ) (hτ : Tendsto τ atTop atTop) (ν : FiniteMeasure (Torus P))
    (hν : Tendsto (fun n => finiteEnergyMeasure P (τ n)) atTop (𝓝 ν)) :
    Tendsto (fun n => thirdFunctional P (τ n)
      (fourierSeries a (fun i (p : P) => k i p))) atTop
        (𝓝 ((1 / 2 : ℂ) * ∫ x, directionalSecondSeries P a k x ∂(ν : Measure (Torus P)))) := by
  have he := (tendsto_thirdFunctional_sub_energy P a k hP ha hD).comp hτ
  have hi := (integral_tendsto_of_weak hν (directionalSecondSeries P a k)).const_mul (1 / 2 : ℂ)
  have hcoe (t : ℝ) : (finiteEnergyMeasure P t : Measure (Torus P)) = energyMeasure P t := rfl
  simp only [hcoe] at hi
  have h := he.add hi
  simpa only [Function.comp_def, sub_add_cancel, zero_add] using h

/-- The second directional series is invisible to the Haar component. -/
theorem haarIntegral_directionalSecondSeries {ι : Type*}
    (P : Finset ℕ) (a : ι → ℂ) (k : ι → ℕ → ℤ)
    (hP : ∀ p ∈ P, p.Prime)
    (ha : Summable (fun i => ‖a i‖ * primeModeWeight P (k i) ^ 2)) :
    haarIntegral (directionalSecondSeries P a k) = 0 := by
  classical
  rw [directionalSecondSeries, haarIntegral_fourierSeries _ _
    (summable_directionalSecondCoefficients P a k hP ha)]
  trans ∑' _ : ι, (0 : ℂ)
  · apply tsum_congr
    intro i
    split_ifs with hk
    · have hfreq : primeFrequency P (k i) = 0 := by
        apply Finset.sum_eq_zero
        intro p hp
        have hkp : k i p = 0 := congrFun hk (⟨p, hp⟩ : P)
        simp only [hkp, Int.cast_zero, zero_mul]
      simp only [hfreq, Complex.ofReal_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
        neg_zero, zero_mul]
    · exact mul_zero _
  · exact tsum_zero

/-- Centered weak convergence suffices for the full-height correction;
convergence of total horizontal energy is not required. -/
theorem thirdFunctional_tendsto_of_centered_limit {ι : Type*}
    (P : Finset ℕ) (a : ι → ℂ) (k : ι → ℕ → ℤ)
    (hP : ∀ p ∈ P, p.Prime)
    (ha : Summable (fun i => ‖a i‖ * primeModeWeight P (k i) ^ 2))
    (hD : UniformSelbergDensity (1 / 4)) (ν : FiniteMeasure (Torus P))
    (hcenter : ∀ f : C(Torus P, ℂ),
      Tendsto (fun T : ℝ => PrimeTorusCenteredMeasure.centeredIntegral
        (finiteEnergyMeasure P T) f) atTop
        (𝓝 (PrimeTorusCenteredMeasure.centeredIntegral ν f))) :
    Tendsto (fun T : ℝ => thirdFunctional P T
      (fourierSeries a (fun i (p : P) => k i p))) atTop
        (𝓝 ((1 / 2 : ℂ) * ∫ x, directionalSecondSeries P a k x ∂(ν : Measure (Torus P)))) := by
  have he := tendsto_thirdFunctional_sub_energy P a k hP ha hD
  have hz := haarIntegral_directionalSecondSeries P a k hP ha
  have hi : Tendsto (fun T : ℝ => ∫ x, directionalSecondSeries P a k x ∂energyMeasure P T)
      atTop (𝓝 (∫ x, directionalSecondSeries P a k x ∂(ν : Measure (Torus P)))) := by
    have hcoe (t : ℝ) : (finiteEnergyMeasure P t : Measure (Torus P)) = energyMeasure P t := rfl
    have hh := hcenter (directionalSecondSeries P a k)
    simp only [PrimeTorusCenteredMeasure.centeredIntegral_apply, hz, mul_zero, sub_zero] at hh
    simpa only [hcoe] using hh
  have h := he.add (hi.const_mul (1 / 2 : ℂ))
  simpa only [sub_add_cancel, zero_add] using h

end RiemannResearch.Analysis.ActualPrimeTorusFMZ
