/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualPrimeTorusPlancherel
import RiemannResearch.Analysis.ActualPrimeTorusFMZRate
import RiemannResearch.Analysis.ActualZeroCountAsymptotics
import RiemannResearch.Analysis.LogarithmicSampleNormalization
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Corrected actual-zero Plancherel and uniform A2-ball convergence

All sampling-rate and convergence theorems retain the explicit
UniformSelbergDensity (1/4) premise. P is fixed before constants are chosen.
The exact Haar and Gram identities have no density or RH premise.

Source: the user's prime-torus Plancherel question (2026-10-28),
Mathlib finite-torus Fourier theory, and the cited project modules.
-/
noncomputable section
open Filter Zeta23
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.ActualPrimeTorusFMZ
open ActualZeroOrdinate PrimePhaseTorus PrimeTorusHaar FiniteTorusWiener
theorem norm_haarIntegral_fourierSeries_primeDensity_le {ι : Type*}
    (P : Finset ℕ) (a : ι → ℂ) (k : ι → ℕ → ℤ)
    (hP : ∀ p ∈ P, p.Prime)
    (ha : Summable (fun i => ‖a i‖ * primeModeWeight P (k i) ^ 2)) :
    ‖haarIntegral (fourierSeries a (fun i => fun p : P => k i p) * primeDensity P)‖ ≤
      Fourier.weightedFourierMass a (fun i => primeModeWeight P (k i) ^ 2) := by
  have ha0 := summable_norm_of_primeModeWeight_sq P a k ha
  have he := haarIntegral_fourierSeries_density a (fun i => fun p : P => k i p)
    ha0 (primeConstants P) (primeRadii P)
    (fun p => primeRadius_nonneg p)
    (fun p => primeRadius_lt_one (hP p p.property))
  simp_rw [← prime_rationalFMZMain_eq_axisMultiplier P _ hP] at he
  change haarIntegral (fourierSeries a (fun i => fun p : P => k i p) * primeDensity P) = _ at he
  rw [he]
  change ‖∑' i, a i * rationalFMZMain (primeNumerator P (k i))
      (primeDenominator P (k i))‖ ≤
    ∑' i, ‖a i‖ * primeModeWeight P (k i) ^ 2
  apply tsum_of_norm_bounded ha.hasSum
  intro i
  rw [norm_mul]
  have hb : ‖rationalFMZMain (primeNumerator P (k i))
      (primeDenominator P (k i))‖ ≤ primeModeWeight P (k i) :=
    rationalFMZMain_norm_le_weight _ _
      (primeProduct_pos P (fun p => (k i p).toNat) hP)
      (primeProduct_pos P (fun p => (-k i p).toNat) hP)
  have hw := one_le_primeModeWeight P (k i)
  have hw2 : primeModeWeight P (k i) ≤ primeModeWeight P (k i) ^ 2 := by nlinarith
  exact mul_le_mul_of_nonneg_left (hb.trans hw2) (norm_nonneg _)

theorem norm_a2_densityIntegral_le
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (g : C(Torus P, ℂ))
    (hg : MemA2 (fun p : P => Real.log (p : ℝ)) g) :
    ‖haarIntegral (g * primeDensity P)‖ ≤
      a2Mass (fun p : P => Real.log (p : ℝ)) g := by
  have ha := summable_prime_weighted P hP g hg
  have ha0 := summable_norm_of_primeModeWeight_sq P (coeff g) (ambientPrimeMode P) ha
  have hs := fourierSeries_mFourierCoeff g ha0
  have hmodes : (fun k : P → ℤ => fun p : P => ambientPrimeMode P k p) = id := by
    funext k p
    exact ambientPrimeMode_apply P k p
  have h := norm_haarIntegral_fourierSeries_primeDensity_le P (coeff g)
    (ambientPrimeMode P) hP ha
  rw [hmodes, hs] at h
  simpa only [← a2Mass_eq_weightedFourierMass P hP g] using h

theorem eventually_a2_height_remainder_bound
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hD : UniformSelbergDensity (1 / 4)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop,
      ∀ g : C(Torus P, ℂ),
        MemA2 (fun p : P => Real.log (p : ℝ)) g →
        ‖(sampleFunctional P T g - (Ncount 0 T : ℂ) * haarIntegral g) / (T : ℂ) -
          haarIntegral (g * primeDensity P)‖ ≤
          (K / Real.log T) * a2Mass (fun p : P => Real.log (p : ℝ)) g := by
  obtain ⟨K, hK, hb⟩ := eventually_fourierSeries_remainder_bound (ι := P → ℤ) hD
  refine ⟨K, hK, hb.mono ?_⟩
  intro T hT g hg
  have ha := summable_prime_weighted P hP g hg
  have ha0 := summable_norm_of_primeModeWeight_sq P (coeff g) (ambientPrimeMode P) ha
  have hs := fourierSeries_mFourierCoeff g ha0
  have hmodes : (fun k : P → ℤ => fun p : P => ambientPrimeMode P k p) = id := by
    funext k p
    exact ambientPrimeMode_apply P k p
  have h := hT P (coeff g) (ambientPrimeMode P) hP ha
  rw [hmodes, hs] at h
  simpa only [← a2Mass_eq_weightedFourierMass P hP g] using h

theorem eventually_a2_count_remainder_bound
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hD : UniformSelbergDensity (1 / 4)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop,
      ∀ g : C(Torus P, ℂ),
        MemA2 (fun p : P => Real.log (p : ℝ)) g →
        ‖sampleFunctional P T g / (Ncount 0 T : ℂ) - haarIntegral g -
          ((T / (Ncount 0 T : ℝ) : ℝ) : ℂ) * haarIntegral (g * primeDensity P)‖ ≤
          (K / (Real.log T)^2) * a2Mass (fun p : P => Real.log (p : ℝ)) g := by
  obtain ⟨K, hK, hb⟩ := eventually_a2_height_remainder_bound P hP hD
  obtain ⟨c, hc, hcount⟩ := exists_count_normalization
  refine ⟨K / c, by positivity, ?_⟩
  filter_upwards [hb, hcount, eventually_gt_atTop (1 : ℝ)] with T hB hN hT
  intro g hg
  have hmass : 0 ≤ a2Mass (fun p : P => Real.log (p : ℝ)) g := a2Mass_nonneg _ g
  simpa only [Complex.ofReal_natCast] using
    countNormalized_remainder_norm_le T (Ncount 0 T : ℝ) c K
      (a2Mass (fun p : P => Real.log (p : ℝ)) g)
      (sampleFunctional P T g) (haarIntegral g) (haarIntegral (g * primeDensity P))
      hT hc hK.le hmass hN (hB g hg)

theorem eventually_a2_count_error_bound
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hD : UniformSelbergDensity (1 / 4)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop,
      ∀ g : C(Torus P, ℂ),
        MemA2 (fun p : P => Real.log (p : ℝ)) g →
        ‖sampleFunctional P T g / (Ncount 0 T : ℂ) - haarIntegral g‖ ≤
          (K / Real.log T) * a2Mass (fun p : P => Real.log (p : ℝ)) g := by
  obtain ⟨K, hK, hb⟩ := eventually_a2_height_remainder_bound P hP hD
  obtain ⟨c, hc, hcount⟩ := exists_count_normalization
  refine ⟨(K + 1) / c, by positivity, ?_⟩
  filter_upwards [hb, hcount, eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with T hB hN hT hL
  intro g hg
  have hmass : 0 ≤ a2Mass (fun p : P => Real.log (p : ℝ)) g := a2Mass_nonneg _ g
  simpa only [Complex.ofReal_natCast] using
    countNormalized_error_norm_le T (Ncount 0 T : ℝ) c K
      (a2Mass (fun p : P => Real.log (p : ℝ)) g)
      (sampleFunctional P T g) (haarIntegral g) (haarIntegral (g * primeDensity P))
      hT hL hc hK.le hmass hN (norm_a2_densityIntegral_le P hP g hg) (hB g hg)

theorem eventually_a2_energy_remainder_bound
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hD : UniformSelbergDensity (1 / 4)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop,
      ∀ f : C(Torus P, ℂ),
        MemA2 (fun p : P => Real.log (p : ℝ)) f →
        ‖sampleFunctional P T (f * star f) / (Ncount 0 T : ℂ) -
          ((∑' k : P → ℤ, ‖coeff f k‖ ^ 2 : ℝ) : ℂ) -
          ((T / (Ncount 0 T : ℝ) : ℝ) : ℂ) *
            haarIntegral ((f * star f) * primeDensity P)‖ ≤
          (K / (Real.log T)^2) *
            (a2Mass (fun p : P => Real.log (p : ℝ)) f)^2 := by
  obtain ⟨K, hK, hb⟩ := eventually_a2_count_remainder_bound P hP hD
  refine ⟨K, hK, hb.mono ?_⟩
  intro T hT f hf
  obtain ⟨hff, hmass⟩ := memA2_mul_star_and_mass_le
    (fun p : P => Real.log (p : ℝ)) (primeLog_nonneg P hP) f f hf hf
  have h := hT (f * star f) hff
  rw [haarIntegral_mul_star_self] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [pow_two] using hmass

theorem eventually_a2_energy_error_bound
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hD : UniformSelbergDensity (1 / 4)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop,
      ∀ f : C(Torus P, ℂ),
        MemA2 (fun p : P => Real.log (p : ℝ)) f →
        ‖sampleFunctional P T (f * star f) / (Ncount 0 T : ℂ) -
          ((∑' k : P → ℤ, ‖coeff f k‖ ^ 2 : ℝ) : ℂ)‖ ≤
          (K / Real.log T) *
            (a2Mass (fun p : P => Real.log (p : ℝ)) f)^2 := by
  obtain ⟨K, hK, hb⟩ := eventually_a2_count_error_bound P hP hD
  refine ⟨K, hK, ?_⟩
  filter_upwards [hb, eventually_gt_atTop (1 : ℝ)] with T hT hT1
  intro f hf
  have hL : 0 ≤ Real.log T := (Real.log_pos hT1).le
  obtain ⟨hff, hmass⟩ := memA2_mul_star_and_mass_le
    (fun p : P => Real.log (p : ℝ)) (primeLog_nonneg P hP) f f hf hf
  have h := hT (f * star f) hff
  rw [haarIntegral_mul_star_self] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hK.le hL)
  simpa only [pow_two] using hmass

theorem tendstoUniformlyOn_a2_energy
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hD : UniformSelbergDensity (1 / 4)) (R : ℝ) :
    TendstoUniformlyOn
      (fun T : ℝ => fun f : C(Torus P, ℂ) =>
        sampleFunctional P T (f * star f) / (Ncount 0 T : ℂ))
      (fun f : C(Torus P, ℂ) =>
        ((∑' k : P → ℤ, ‖coeff f k‖^2 : ℝ) : ℂ)) atTop
      {f | MemA2 (fun p : P => Real.log (p : ℝ)) f ∧
        a2Mass (fun p : P => Real.log (p : ℝ)) f ≤ R} := by
  obtain ⟨K, hK, hb⟩ := eventually_a2_energy_error_bound P hP hD
  have hrate : Tendsto (fun T : ℝ => (K / Real.log T) * R^2)
      atTop (𝓝 0) := by
    have h : Tendsto (fun T : ℝ => (K * R^2) / Real.log T)
        atTop (𝓝 0) := tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    simpa only [div_mul_eq_mul_div] using h
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hb, hrate.eventually_lt_const hε,
    eventually_gt_atTop (1 : ℝ)] with T hB hεT hT
  intro f hf
  have hL : 0 ≤ Real.log T := (Real.log_pos hT).le
  have hmass : (a2Mass (fun p : P => Real.log (p : ℝ)) f)^2 ≤ R^2 := by
    simpa only [pow_two] using mul_self_le_mul_self
      (a2Mass_nonneg (fun p : P => Real.log (p : ℝ)) f) hf.2
  have h := ((hB f hf.1).trans
    (mul_le_mul_of_nonneg_left hmass (div_nonneg hK.le hL))).trans_lt hεT
  simpa only [dist_eq_norm, norm_sub_rev] using h
end RiemannResearch.Analysis.ActualPrimeTorusFMZ
