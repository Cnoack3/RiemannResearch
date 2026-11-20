/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualPrimeTorusPlancherel
import RiemannResearch.Analysis.ActualPrimeTorusFMZRate
import RiemannResearch.Analysis.ActualZeroLoglogRate
import RiemannResearch.Analysis.ActualZeroCountNormalization
import RiemannResearch.Analysis.ActualZeroCountAsymptotics
import RiemannResearch.Analysis.LogarithmicSampleNormalization
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Corrected actual-zero Plancherel and uniform A2-ball convergence

The empirical energy converges uniformly on each A2 ball at rate 1/log T.
After subtraction of the signed prime-density bias the unconditional bound
is (log log T)^2/(log T)^2, uniformly over finite prime sets. The one-log
Selberg input improves this corrected bound to 1/(log T)^2.

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

/-- Transfer any uniform rational-mode bound to actual continuous functions
in the squared prime-logarithm Wiener class. -/
theorem a2_height_remainder_le_of_mode_bound {T B : ℝ}
    (hmode : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m →
      ‖centeredRationalOrdinate T n m / (T : ℂ) - rationalFMZMain n m‖ ≤
        B * rationalModeWeight n m ^ 2)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (g : C(Torus P, ℂ))
    (hg : MemA2 (fun p : P => Real.log (p : ℝ)) g) :
    ‖(sampleFunctional P T g - (Ncount 0 T : ℂ) * haarIntegral g) / (T : ℂ) -
      haarIntegral (g * primeDensity P)‖ ≤ B * a2Mass (fun p : P => Real.log (p : ℝ)) g := by
  have ha := summable_prime_weighted P hP g hg
  have ha0 := summable_norm_of_primeModeWeight_sq P (coeff g) (ambientPrimeMode P) ha
  have hs := fourierSeries_mFourierCoeff g ha0
  have hmodes : (fun k : P → ℤ => fun p : P => ambientPrimeMode P k p) = id := by
    funext k p
    exact ambientPrimeMode_apply P k p
  have h := fourierSeries_remainder_le_of_mode_bound P (coeff g) (ambientPrimeMode P) hP ha hmode
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
  obtain ⟨K, hK, hb⟩ := eventually_centeredRationalOrdinate_remainder_rate hD
  exact ⟨K, hK, hb.mono (fun _ ht => a2_height_remainder_le_of_mode_bound ht P hP)⟩

/-- Unconditional corrected sampling, uniform in the prime set and the test.
The arithmetic bias is retained at the exact factor `T / N(T)`. -/
theorem eventually_a2_count_remainder_loglog :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ (P : Finset ℕ),
      (∀ p ∈ P, p.Prime) → ∀ g : C(Torus P, ℂ),
      MemA2 (fun p : P => Real.log (p : ℝ)) g →
      ‖sampleFunctional P T g / (Ncount 0 T : ℂ) - haarIntegral g -
        ((T / (Ncount 0 T : ℝ) : ℝ) : ℂ) * haarIntegral (g * primeDensity P)‖ ≤
        (K * horizontalLogRate T / Real.log T) * a2Mass (fun p : P => Real.log (p : ℝ)) g := by
  obtain ⟨K, hK, hb⟩ := eventually_centeredRationalOrdinate_remainder_loglog
  obtain ⟨c, hc, hcount⟩ := exists_count_normalization
  refine ⟨K / c, by positivity, ?_⟩
  filter_upwards [hb, hcount, eventually_gt_atTop (1 : ℝ)] with T hB hN hT P hP g hg
  have hT0 : 0 < T := zero_lt_one.trans hT
  obtain ⟨hN0, hratio⟩ := count_normalization_ratio_bound T (Ncount 0 T : ℝ) c hT hc hN
  have hr : 0 ≤ horizontalLogRate T := div_nonneg (sq_nonneg _) (Real.log_pos hT).le
  have hm := a2Mass_nonneg (fun p : P => Real.log (p : ℝ)) g
  have he := countNormalized_remainder_eq T (Ncount 0 T : ℝ) (sampleFunctional P T g)
    (haarIntegral g) (haarIntegral (g * primeDensity P)) hT0.ne' hN0.ne'
  simp only [Complex.ofReal_natCast] at he
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hT0.le hN0.le)]
  apply (mul_le_mul hratio (a2_height_remainder_le_of_mode_bound hB P hP g hg)
    (norm_nonneg _) (div_nonneg zero_le_one (mul_nonneg hc.le (Real.log_pos hT).le))).trans_eq
  ring

/-- The first-order signed empirical bias converges in the norm dual to
the squared-weight Wiener norm. Both the prime set and the test may vary. -/
theorem eventually_a2_first_order_bias {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) → ∀ g : C(Torus P, ℂ),
      MemA2 (fun p : P => Real.log (p : ℝ)) g →
      ‖(Real.log T : ℂ) * (sampleFunctional P T g / (Ncount 0 T : ℂ) - haarIntegral g) -
        ((2 * Real.pi : ℝ) : ℂ) * haarIntegral (g * primeDensity P)‖ ≤
        ε * a2Mass (fun p : P => Real.log (p : ℝ)) g := by
  obtain ⟨K, _, hbound⟩ := eventually_a2_count_remainder_loglog
  have hratio : Tendsto (fun T : ℝ => Real.log T * (T / (Ncount 0 T : ℝ)))
      atTop (𝓝 (2 * Real.pi)) := by
    have hh := (tendsto_count_div_mainTerm.inv₀ (by norm_num : (1 : ℝ) ≠ 0)).const_mul (2*Real.pi)
    simp only [inv_one, mul_one] at hh
    apply hh.congr' (Eventually.of_forall (fun T => ?_))
    simp only [inv_div]
    field_simp [Real.pi_ne_zero]
    <;> ring
  have hlim := (horizontalLogRate_tendsto_zero.const_mul K).add
    ((hratio.sub_const (2 * Real.pi)).norm)
  simp only [mul_zero, sub_self, norm_zero, add_zero] at hlim
  filter_upwards [hbound, hlim.eventually_le_const hε, eventually_gt_atTop (1 : ℝ)]
    with T hT hsmall hT1 P hP g hg
  let N : ℝ := Ncount 0 T
  let S := sampleFunctional P T g / (Ncount 0 T : ℂ) - haarIntegral g
  let B := haarIntegral (g * primeDensity P)
  let M := a2Mass (fun p : P => Real.log (p : ℝ)) g
  have hL := Real.log_pos hT1
  have hrem := hT P hP g hg
  have hB : ‖B‖ ≤ M := norm_a2_densityIntegral_le P hP g hg
  have hm : 0 ≤ M := a2Mass_nonneg _ g
  have he : (Real.log T : ℂ) * S - ((2 * Real.pi : ℝ) : ℂ) * B =
      (Real.log T : ℂ) * (S - ((T/N : ℝ) : ℂ) * B) +
      ((Real.log T * (T/N) - 2*Real.pi : ℝ) : ℂ) * B := by push_cast; ring
  change ‖(Real.log T : ℂ) * S - ((2 * Real.pi : ℝ) : ℂ) * B‖ ≤ ε * M
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL, Complex.norm_real]
  calc
    _ ≤ Real.log T * ((K * horizontalLogRate T / Real.log T) * M) +
        ‖Real.log T * (T/N) - 2*Real.pi‖ * M :=
      add_le_add (mul_le_mul_of_nonneg_left hrem hL.le)
        (mul_le_mul_of_nonneg_left hB (norm_nonneg _))
    _ = (K * horizontalLogRate T + ‖Real.log T * (T/N) - 2*Real.pi‖) * M := by
      field_simp
      <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall hm

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
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop,
      ∀ g : C(Torus P, ℂ),
        MemA2 (fun p : P => Real.log (p : ℝ)) g →
        ‖sampleFunctional P T g / (Ncount 0 T : ℂ) - haarIntegral g‖ ≤
          (K / Real.log T) * a2Mass (fun p : P => Real.log (p : ℝ)) g := by
  obtain ⟨K, hK, hb⟩ := eventually_a2_count_remainder_loglog
  obtain ⟨c, hc, hcount⟩ := exists_count_normalization
  refine ⟨K + 1/c, by positivity, ?_⟩
  filter_upwards [hb, hcount, eventually_gt_atTop (1 : ℝ),
    horizontalLogRate_tendsto_zero.eventually_le_const (by norm_num : (0 : ℝ) < 1)]
    with T hB hN hT hsmall g hg
  have hT0 : 0 < T := zero_lt_one.trans hT
  have hL := Real.log_pos hT
  obtain ⟨hN0, hratio⟩ := count_normalization_ratio_bound T (Ncount 0 T : ℝ) c hT hc hN
  let M := a2Mass (fun p : P => Real.log (p : ℝ)) g
  let bias := ((T / (Ncount 0 T : ℝ) : ℝ) : ℂ) * haarIntegral (g * primeDensity P)
  have hm : 0 ≤ M := a2Mass_nonneg _ g
  have hbias : ‖bias‖ ≤ 1 / (c * Real.log T) * M := by
    rw [show ‖bias‖ = T / (Ncount 0 T : ℝ) * ‖haarIntegral (g * primeDensity P)‖ by
      simp only [bias, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg hT0.le hN0.le)]]
    exact mul_le_mul hratio (norm_a2_densityIntegral_le P hP g hg) (norm_nonneg _) (by positivity)
  have hrem := hB P hP g hg
  have hscale : K * horizontalLogRate T / Real.log T ≤ K / Real.log T := by
    apply div_le_div_of_nonneg_right _ hL.le
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hsmall hK.le
  calc
    _ ≤ ‖sampleFunctional P T g / (Ncount 0 T : ℂ) - haarIntegral g - bias‖ + ‖bias‖ := by
      simpa only [sub_add_cancel] using norm_add_le
        (sampleFunctional P T g / (Ncount 0 T : ℂ) - haarIntegral g - bias) bias
    _ ≤ (K * horizontalLogRate T / Real.log T) * M + (1 / (c * Real.log T)) * M :=
      add_le_add hrem hbias
    _ ≤ (K / Real.log T) * M + (1 / (c * Real.log T)) * M :=
      add_le_add (mul_le_mul_of_nonneg_right hscale hm) le_rfl
    _ = _ := by ring

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

/-- The bias-corrected Plancherel estimate holds uniformly over prime sets. -/
theorem eventually_a2_energy_remainder_loglog :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) → ∀ f : C(Torus P, ℂ),
        MemA2 (fun p : P => Real.log (p : ℝ)) f →
        ‖sampleFunctional P T (f * star f) / (Ncount 0 T : ℂ) -
          ((∑' k : P → ℤ, ‖coeff f k‖ ^ 2 : ℝ) : ℂ) -
          ((T / (Ncount 0 T : ℝ) : ℝ) : ℂ) *
            haarIntegral ((f * star f) * primeDensity P)‖ ≤
          (K * horizontalLogRate T / Real.log T) *
            (a2Mass (fun p : P => Real.log (p : ℝ)) f)^2 := by
  obtain ⟨K, hK, hb⟩ := eventually_a2_count_remainder_loglog
  refine ⟨K, hK, ?_⟩
  filter_upwards [hb, eventually_gt_atTop (1 : ℝ)] with T hT hT1 P hP f hf
  have hr : 0 ≤ horizontalLogRate T := div_nonneg (sq_nonneg _) (Real.log_pos hT1).le
  have hL := Real.log_pos hT1
  obtain ⟨hff, hmass⟩ := memA2_mul_star_and_mass_le
    (fun p : P => Real.log (p : ℝ)) (primeLog_nonneg P hP) f f hf hf
  have h := hT P hP (f * star f) hff
  rw [haarIntegral_mul_star_self] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [pow_two] using hmass

theorem eventually_a2_energy_error_bound
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop,
      ∀ f : C(Torus P, ℂ),
        MemA2 (fun p : P => Real.log (p : ℝ)) f →
        ‖sampleFunctional P T (f * star f) / (Ncount 0 T : ℂ) -
          ((∑' k : P → ℤ, ‖coeff f k‖ ^ 2 : ℝ) : ℂ)‖ ≤
          (K / Real.log T) *
            (a2Mass (fun p : P => Real.log (p : ℝ)) f)^2 := by
  obtain ⟨K, hK, hb⟩ := eventually_a2_count_error_bound P hP
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
    (R : ℝ) :
    TendstoUniformlyOn
      (fun T : ℝ => fun f : C(Torus P, ℂ) =>
        sampleFunctional P T (f * star f) / (Ncount 0 T : ℂ))
      (fun f : C(Torus P, ℂ) =>
        ((∑' k : P → ℤ, ‖coeff f k‖^2 : ℝ) : ℂ)) atTop
      {f | MemA2 (fun p : P => Real.log (p : ℝ)) f ∧
        a2Mass (fun p : P => Real.log (p : ℝ)) f ≤ R} := by
  obtain ⟨K, hK, hb⟩ := eventually_a2_energy_error_bound P hP
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
