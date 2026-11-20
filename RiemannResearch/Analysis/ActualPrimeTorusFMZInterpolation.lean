/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.ActualPrimeTorusFMZRate
import RiemannResearch.Analysis.ActualZeroLoglogRate
import RiemannResearch.Analysis.ArithmeticWeightedFourierEndpoint
import RiemannResearch.Analysis.PrimeTorusFourierDecay
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Unconditional fractional Wiener estimates for prime-torus FMZ

Ford, Meng and Zaharescu, *Simultaneous distribution of the fractional parts
of Riemann zeta zeros*, Theorem 1 and Corollary 1.1
(https://doi.org/10.1112/blms.12001), give fixed-torus convergence under
coefficient decay of order greater than dimension plus two. For the finite
prime-logarithm torus, interpolation of the total count with the proved
quadratic estimate yields rates on every fractional Wiener class of order
strictly above one. All arithmetic main terms and mixed modes are retained.
-/

noncomputable section
open Filter Zeta23
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- The continuous envelope for the resonant coefficient is
`1 / (π exp(1))`, uniformly in numerator and denominator. -/
theorem rationalLandauMain_le_exp_constant {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n) :
    rationalLandauMain n m ≤ 1 / (Real.pi * Real.exp 1) := by
  rw [rationalLandauMain_eq_vonMangoldt_div_sqrt hm hmn]
  split_ifs with hd
  · have hn : 0 < n := by omega
    have hm0 : (0 : ℝ) < m := by positivity
    let x := (n : ℝ) / (m : ℝ)
    have hx : 0 < x := by dsimp [x]; positivity
    have hs := Real.sqrt_pos.mpr hx
    have hcast : ((n/m : ℕ) : ℝ) = x := Nat.cast_div hd hm0.ne'
    have he := Real.add_one_le_exp (Real.log (Real.sqrt x) - 1)
    rw [sub_add_cancel, Real.exp_sub, Real.exp_log hs] at he
    have hv := ArithmeticFunction.vonMangoldt_le_log (n := n/m)
    rw [hcast] at hv
    rw [Real.log_sqrt hx.le] at he
    change _ / ((2 * Real.pi) * Real.sqrt x) ≤ _
    calc
      _ ≤ (2 * (Real.sqrt x / Real.exp 1)) / ((2 * Real.pi) * Real.sqrt x) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by field_simp [Real.pi_ne_zero, hs.ne']
  · positivity

theorem rationalFMZMain_norm_le_exp_constant {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    ‖rationalFMZMain n m‖ ≤ 1 / (Real.pi * Real.exp 1) := by
  rcases lt_trichotomy m n with h | h | h
  · simpa [rationalFMZMain, h, abs_of_nonneg (rationalLandauMain_nonneg n m)] using
      rationalLandauMain_le_exp_constant hm h
  · subst n
    rw [show rationalFMZMain m m = 0 by simp [rationalFMZMain], norm_zero]
    positivity
  · simpa [rationalFMZMain, h, not_lt_of_gt h, abs_of_nonneg (rationalLandauMain_nonneg m n)] using
      rationalLandauMain_le_exp_constant hn h

/-- Rate after interpolating the count bound and the quadratic mode bound. -/
def fmzWienerRate (s T : ℝ) : ℝ := (Real.log (Real.log T)) ^ s / (Real.log T) ^ (s-1)

theorem tendsto_fmzWienerRate {s : ℝ} (hs : 1 < s) :
    Tendsto (fmzWienerRate s) atTop (𝓝 0) :=
  (isLittleO_log_rpow_rpow_atTop s (sub_pos.mpr hs)).tendsto_div_nhds_zero.comp
    Real.tendsto_log_atTop

theorem eventually_centeredRationalOrdinate_fractional :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ s : ℝ, 0 ≤ s → s ≤ 2 →
      ∀ n m : ℕ, 1 ≤ n → 1 ≤ m →
      ‖centeredRationalOrdinate T n m / (T : ℂ) - rationalFMZMain n m‖ ≤
        (K * fmzWienerRate s T) * rationalModeWeight n m ^ s := by
  obtain ⟨A, hA, hcount⟩ := exists_normalized_ordinate_bound
  obtain ⟨B, hB, hquad⟩ := eventually_centeredRationalOrdinate_remainder_loglog
  let D := 1 / (Real.pi * Real.exp 1)
  let K := max (A+D) B
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hK : 0 < K := hB.trans_le (le_max_right _ _)
  refine ⟨K, hK, ?_⟩
  filter_upwards [hquad, eventually_ge_atTop (9 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with T hQ hT hL1 s hs hs2 n m hn hm
  let L := Real.log T
  let l := Real.log L
  let W := rationalModeWeight n m
  let z := centeredRationalOrdinate T n m / (T : ℂ) - rationalFMZMain n m
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have hl : 0 ≤ l := Real.log_nonneg hL1
  have hW : 0 ≤ W := by dsimp [W, rationalModeWeight]; positivity
  have hraw : ‖centeredRationalOrdinate T n m / (T : ℂ)‖ ≤ A*L := by
    by_cases heq : n=m
    · subst n
      have hm0 : (m : ℝ) ≠ 0 := by positivity
      simpa [centeredRationalOrdinate, hm0] using (mul_nonneg hA.le hL.le)
    · simpa only [centeredRationalOrdinate, if_neg heq, sub_zero] using
        hcount T (Real.log ((n : ℝ)/(m : ℝ))) hT
  have hcrude : ‖z‖ ≤ K*L := by
    apply (norm_sub_le _ _).trans
      ((add_le_add hraw (rationalFMZMain_norm_le_exp_constant hn hm)).trans ?_)
    change A*L+D ≤ K*L
    exact (show A*L+D ≤ (A+D)*L by nlinarith [mul_le_mul_of_nonneg_left hL1 hD]).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hL.le)
  have hfine : ‖z‖ ≤ K*L*(l*W/L)^2 := by
    apply (hQ n m hn hm).trans
    change B*(l^2/L)*W^2 ≤ K*L*(l*W/L)^2
    calc
      _ ≤ K*(l^2/L)*W^2 := by gcongr; exact le_max_right _ _
      _ = _ := by field_simp
  have hsatur : ‖z‖ ≤ K*L*min 1 ((l*W/L)^2) := by
    rw [mul_min_of_nonneg _ _ (mul_nonneg hK.le hL.le), mul_one]
    exact le_min hcrude hfine
  apply hsatur.trans ((mul_le_mul_of_nonneg_left
    (Fourier.min_one_sq_le_rpow (l*W/L) s (by positivity) hs hs2)
    (mul_nonneg hK.le hL.le)).trans_eq ?_)
  change K*L*(l*W/L)^s = (K*(l^s/L^(s-1)))*W^s
  rw [Real.div_rpow (mul_nonneg hl hW) hL.le, Real.mul_rpow hl hW,
    Real.rpow_sub hL, Real.rpow_one]
  field_simp [(Real.rpow_pos_of_pos hL s).ne']

end RiemannResearch.Analysis.ActualZeroOrdinate

namespace RiemannResearch.Analysis.ActualPrimeTorusFMZ
open ActualZeroOrdinate PrimePhaseTorus PrimeTorusHaar

/-- Quantitative synthesis with one constant for all exponents, dimensions,
prime sets and coefficient families. -/
theorem eventually_fourierSeries_remainder_fractional {ι : Type*} :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ s : ℝ, 0 ≤ s → s ≤ 2 →
      ∀ (P : Finset ℕ) (a : ι → ℂ) (k : ι → ℕ → ℤ), (∀ p ∈ P, p.Prime) →
      Summable (fun i => ‖a i‖ * primeModeWeight P (k i) ^ s) →
      ‖(sampleFunctional P T (fourierSeries a (fun i => fun p : P => k i p)) -
          (Ncount 0 T : ℂ) * haarIntegral (fourierSeries a (fun i => fun p : P => k i p))) /
          (T : ℂ) - haarIntegral (fourierSeries a (fun i => fun p : P => k i p) * primeDensity P)‖ ≤
        (K * fmzWienerRate s T) * Fourier.weightedFourierMass a (fun i => primeModeWeight P (k i)^s) := by
  obtain ⟨K, hK, hb⟩ := eventually_centeredRationalOrdinate_fractional
  refine ⟨K, hK, hb.mono ?_⟩
  intro T ht s hs hs2 P a k hP ha
  have ha0 : Summable (fun i => ‖a i‖) := by
    apply ha.of_norm_bounded
    intro i
    simpa only [norm_norm, mul_one] using mul_le_mul_of_nonneg_left
      (Real.one_le_rpow (one_le_primeModeWeight P (k i)) hs) (norm_nonneg (a i))
  let n := fun i => primeNumerator P (k i)
  let m := fun i => primeDenominator P (k i)
  have hn (i : ι) : 1 ≤ n i := primeProduct_pos _ _ hP
  have hm (i : ι) : 1 ≤ m i := primeProduct_pos _ _ hP
  have hmain : Summable (fun i => a i * rationalFMZMain (n i) (m i)) := by
    apply (ha0.mul_right (1 / (Real.pi * Real.exp 1))).of_norm_bounded
    intro i
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (rationalFMZMain_norm_le_exp_constant (hn i) (hm i)) (norm_nonneg _)
  have hmode (i : ι) :
      ‖centeredRationalOrdinate T (n i) (m i) / (T : ℂ) - rationalFMZMain (n i) (m i)‖ ≤
        (K * fmzWienerRate s T) * primeModeWeight P (k i)^s := by
    exact ht s hs hs2 (n i) (m i) (hn i) (hm i)
  rw [fourierSeries_remainder_eq_rationalPairing P a k hP ha0]
  simpa only [div_one] using (Fourier.weightedFourierPairing_remainder_bound_of_limit_summable a
    (fun i => centeredRationalOrdinate T (n i) (m i) / (T : ℂ))
    (fun i => rationalFMZMain (n i) (m i)) (fun i => primeModeWeight P (k i)^s)
    (K * fmzWienerRate s T) 1 hmain ha
    (fun i => by simpa only [div_one] using hmode i)).2

/-- A fractional moment strictly above one suffices for a fixed test. -/
theorem tendsto_centered_fourierSeries_div_poisson_of_fractional {ι : Type*} {s : ℝ}
    (hs : 1 < s) (hs2 : s ≤ 2) (P : Finset ℕ) (a : ι → ℂ) (k : ι → ℕ → ℤ)
    (hP : ∀ p ∈ P, p.Prime)
    (ha : Summable (fun i => ‖a i‖ * primeModeWeight P (k i) ^ s)) :
    Tendsto (fun T : ℝ =>
      (sampleFunctional P T (fourierSeries a (fun i => fun p : P => k i p)) -
        (Ncount 0 T : ℂ) * haarIntegral (fourierSeries a (fun i => fun p : P => k i p))) / (T : ℂ))
      atTop (𝓝 (haarIntegral
        (fourierSeries a (fun i => fun p : P => k i p) * primeDensity P))) := by
  obtain ⟨K, _, hb⟩ := eventually_fourierSeries_remainder_fractional (ι := ι)
  apply tendsto_sub_nhds_zero_iff.1
  have h := ((tendsto_fmzWienerRate hs).const_mul K).mul_const
    (Fourier.weightedFourierMass a (fun i => primeModeWeight P (k i)^s))
  simp only [mul_zero, zero_mul] at h
  exact squeeze_zero_norm' (hb.mono (fun _ ht => ht s (by linarith) hs2 P a k hP ha)) h

/-- Prime-logarithm fractional Wiener mass from coefficient decay on a
finite-dimensional integer lattice. -/
theorem summable_primeModeWeight_rpow_of_fourierDecay {s : ℝ} (hs : 0 ≤ s)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (a : (P → ℤ) → ℂ)
    (C B : ℝ) (hC : 0 ≤ C) (hB : (P.card : ℝ) + s < B)
    (ha : ∀ k, ‖a k‖ ≤ C * (1 + ‖k‖) ^ (-B)) :
    Summable (fun k : P → ℤ => ‖a k‖ * primeModeWeight P (ambientPrimeMode P k)^s) := by
  classical
  let S := ∑ p : P, Real.log (p : ℝ)
  have hlog (p : P) : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (hP p p.property).one_lt.le)
  have hS : 0 ≤ S := Finset.sum_nonneg fun p _ => hlog p
  have hseries := (summable_pi_int_one_add_norm_rpow (ι := P) (s-B)
    (by simpa using (show s-B < -(P.card : ℝ) by linarith))).mul_left (C * (1+S)^s)
  apply hseries.of_norm_bounded
  intro k
  have hkn := norm_nonneg k
  have hw : primeModeWeight P (ambientPrimeMode P k) ≤ (1+S)*(1+‖k‖) := by
    rw [primeModeWeight_eq _ _ hP, ← Finset.sum_coe_sort]
    simp only [ambientPrimeMode_apply]
    have hh := weighted_logheight_le_norm (fun p : P => Real.log (p : ℝ)) hlog k
    change 1 + _ ≤ (1+S)*(1+‖k‖)
    change _ ≤ ‖k‖ * S at hh
    nlinarith
  have hW0 := zero_le_one.trans (one_le_primeModeWeight P (ambientPrimeMode P k))
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hW0 s))]
  apply (mul_le_mul (ha k) (Real.rpow_le_rpow hW0 hw hs) (Real.rpow_nonneg hW0 s)
    (by positivity)).trans_eq
  rw [Real.mul_rpow (by positivity : 0 ≤ 1+S) (by positivity : 0 ≤ 1+‖k‖)]
  have he : (1+‖k‖)^(-B) * (1+‖k‖)^s = (1+‖k‖)^(s-B) := by
    rw [← Real.rpow_add (by positivity)]; congr 1; ring
  calc
    _ = C*(1+S)^s*((1+‖k‖)^(-B)*(1+‖k‖)^s) := by ring
    _ = _ := by rw [he]

end RiemannResearch.Analysis.ActualPrimeTorusFMZ
