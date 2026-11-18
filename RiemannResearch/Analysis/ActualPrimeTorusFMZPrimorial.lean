/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualPrimeTorusFMZPoisson
import RiemannResearch.Analysis.ActualPrimeTorusFMZSeries
import RiemannResearch.Analysis.ActualZeroLoglogRate
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A growing primorial character for the unconditional FMZ estimate

The primes up to (log T)^(1/3) support a single character with exponent one
in every coordinate. The same error bound is uniform over exponents of
absolute value at most one. The all-ones character has zero Haar and
prime-density coefficients once two distinct primes enter the cutoff.

Source: the user-provided cutoff and weight estimate, applied to the
repository's unconditional FMZ rate for centered rational modes.
-/

noncomputable section
open Filter Zeta23
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.ActualPrimeTorusFMZ
open ActualZeroOrdinate PrimePhaseTorus PrimeTorusHaar

/-- The real cutoff for the growing primorial. -/
def primorialCutoff (T : ℝ) : ℝ :=
  Real.log T ^ (1 / 3 : ℝ)

/-- The primes at or below the cutoff, implemented using the natural floor. -/
def primorialPrimes (T : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊primorialCutoff T⌋₊).filter Nat.Prime

theorem mem_primorialPrimes {T : ℝ} {p : ℕ} (hT : 1 < T) :
    p ∈ primorialPrimes T ↔ p.Prime ∧ (p : ℝ) ≤ primorialCutoff T := by
  have hX : 0 ≤ primorialCutoff T := Real.rpow_nonneg (Real.log_pos hT).le _
  simp only [primorialPrimes, Finset.mem_filter, Finset.mem_Icc,
    Nat.le_floor_iff hX]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.one_lt.le, h.2⟩, h.1⟩⟩

private theorem prime_of_mem_primorialPrimes {T : ℝ} {p : ℕ}
    (hp : p ∈ primorialPrimes T) : p.Prime :=
  (Finset.mem_filter.mp hp).2

/-- The single torus character with exponent one in every selected coordinate. -/
def primorialCharacter (T : ℝ) : C(Torus (primorialPrimes T), ℂ) :=
  character (fun _ => 1)

/-- Evaluating the character on actual ordinates gives the sum at the
logarithm of the primorial. -/
theorem primorialCharacter_sample_eq_ordinateSum (T : ℝ) :
    sampleFunctional (primorialPrimes T) T (primorialCharacter T) =
      ordinateSum T (∑ p ∈ primorialPrimes T, Real.log p) := by
  simpa only [primorialCharacter, primeFrequency, Int.cast_one, one_mul] using
    sampleFunctional_character (primorialPrimes T) (fun _ => 1) T

/-- The explicit error scale for the growing-prime FMZ bound. -/
def primorialFMZRate (T : ℝ) : ℝ :=
  Real.log (Real.log T) ^ 4 / primorialCutoff T

/-- The exact norm-square Fourier weight of the all-ones character. -/
theorem primorialCharacter_modeWeight_sq (T : ℝ) :
    primeModeWeight (primorialPrimes T) (fun _ => 1) ^ 2 =
      (1 + ∑ p ∈ primorialPrimes T, Real.log p) ^ 2 := by
  rw [primeModeWeight_eq _ _ (fun _ hp => prime_of_mem_primorialPrimes hp)]
  simp

private theorem primorial_modeWeight_le {T : ℝ} (hT : 1 < T) (hX₁ : 1 ≤ primorialCutoff T)
    (k : ℕ → ℤ) (hk : ∀ p ∈ primorialPrimes T, |(k p : ℝ)| ≤ 1) :
    primeModeWeight (primorialPrimes T) k ≤
      1 + primorialCutoff T * Real.log (primorialCutoff T) := by
  let X := primorialCutoff T
  have hX : 0 ≤ X := Real.rpow_nonneg (Real.log_pos hT).le _
  have hcard : ((primorialPrimes T).card : ℝ) ≤ X := by
    refine le_trans ?_ (Nat.floor_le hX)
    exact_mod_cast (show (primorialPrimes T).card ≤ ⌊X⌋₊ by
      simpa [primorialPrimes, X, Nat.card_Icc] using
        Finset.card_le_card (Finset.filter_subset Nat.Prime (Finset.Icc 1 ⌊X⌋₊)))
  rw [primeModeWeight_eq _ _ (fun _ hp => prime_of_mem_primorialPrimes hp)]
  apply add_le_add_right
  calc
    _ ≤ ∑ _p ∈ primorialPrimes T, Real.log X := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hp', hpX⟩ := (mem_primorialPrimes hT).mp hp
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp'.one_lt.le
      calc
        _ ≤ 1 * Real.log p := mul_le_mul_of_nonneg_right (hk p hp) (Real.log_nonneg hp1)
        _ ≤ Real.log X := by
          rw [one_mul]
          exact Real.log_le_log (by positivity) hpX
    _ = ((primorialPrimes T).card : ℝ) * Real.log X := by simp
    _ ≤ X * Real.log X := mul_le_mul_of_nonneg_right hcard (Real.log_nonneg hX₁)

/-- The elementary square bound for the all-ones Wiener weight. -/
theorem primorialCharacter_modeWeight_sq_le {T : ℝ} (hT : 1 < T) (hX : 1 ≤ primorialCutoff T) :
    primeModeWeight (primorialPrimes T) (fun _ => 1) ^ 2 ≤
      (1 + primorialCutoff T * Real.log (primorialCutoff T)) ^ 2 := by
  exact pow_le_pow_left₀ ((zero_le_one : (0 : ℝ) ≤ 1).trans (one_le_primeModeWeight _ _))
    (primorial_modeWeight_le hT hX _ (by intro p hp; simp)) 2

theorem tendsto_primorialFMZRate : Tendsto primorialFMZRate atTop (𝓝 0) := by
  have hv : Tendsto (fun T : ℝ => Real.log (Real.log T) * (1 / 3 : ℝ)) atTop atTop :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).atTop_mul_const (by norm_num)
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).comp hv).const_mul 81
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0] with T hT
  simp only [Function.comp_def, primorialFMZRate, primorialCutoff,
    Real.rpow_def_of_pos hT, Real.exp_neg, div_eq_mul_inv]
  ring

private theorem eventually_primorial_weight_rate_le :
    ∀ᶠ T : ℝ in atTop, ∀ k : ℕ → ℤ,
      (∀ p ∈ primorialPrimes T, |(k p : ℝ)| ≤ 1) →
      horizontalLogRate T * primeModeWeight (primorialPrimes T) k ^ 2 ≤
        4 * primorialFMZRate T := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1]
    with T hT hL k hk
  let X := primorialCutoff T
  let l := Real.log (Real.log T)
  have hlog := Real.log_pos hT
  have hX : 0 < X := Real.rpow_pos_of_pos hlog _
  have hcube : X ^ 3 = Real.log T := by
    unfold X primorialCutoff
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlog.le]
    norm_num
  have hlogX : Real.log X = l / 3 := by
    simp only [X, primorialCutoff, Real.rpow_def_of_pos hlog, Real.log_exp, l]
    ring
  change 1 ≤ l at hL
  have hX₁ : 1 ≤ X := ((Real.log_pos_iff hX.le).mp (by rw [hlogX]; linarith)).le
  have hW := primorial_modeWeight_le hT hX₁ k hk
  have hb : primeModeWeight (primorialPrimes T) k ≤ 2 * X * l := by
    refine hW.trans ?_
    change 1 + X * Real.log X ≤ 2 * X * l
    rw [hlogX]
    nlinarith only [mul_le_mul_of_nonneg_left hL hX.le, hX₁]
  change l ^ 2 / Real.log T * primeModeWeight (primorialPrimes T) k ^ 2 ≤
    4 * (l ^ 4 / X)
  calc
    _ ≤ l ^ 2 / Real.log T * (2 * X * l) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ ((zero_le_one : (0 : ℝ) ≤ 1).trans (one_le_primeModeWeight _ _)) hb 2
    _ = 4 * (l ^ 4 / X) := by
      rw [← hcube]
      field_simp
      ring

/-- The signed FMZ remainder with both Haar terms retained. -/
def primeCharacterRemainder (P : Finset ℕ) (k : ℕ → ℤ) (T : ℝ) : ℂ :=
  (sampleFunctional P T (character (fun p : P => k p)) -
    (Ncount 0 T : ℂ) * haarIntegral (character (fun p : P => k p))) / (T : ℂ) -
    haarIntegral (character (fun p : P => k p) * primeDensity P)

/-- A uniform unconditional FMZ estimate for the modes with exponents in
{-1, 0, 1} on the growing prime set. -/
theorem eventually_primorial_boundedMode_FMZ :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ k : ℕ → ℤ,
      (∀ p ∈ primorialPrimes T, |(k p : ℝ)| ≤ 1) →
      ‖primeCharacterRemainder (primorialPrimes T) k T‖ ≤ K * primorialFMZRate T := by
  obtain ⟨K, hK, hR⟩ := eventually_centeredRationalOrdinate_remainder_loglog
  refine ⟨4 * K, by positivity, ?_⟩
  filter_upwards [hR, eventually_primorial_weight_rate_le] with T hR hW k hk
  have hP : ∀ p ∈ primorialPrimes T, p.Prime := fun _ hp => prime_of_mem_primorialPrimes hp
  unfold primeCharacterRemainder
  rw [centered_character_eq_rational _ _ hP, haarIntegral_character_primeDensity _ _ hP]
  have hn : 1 ≤ primeNumerator (primorialPrimes T) k := primeProduct_pos _ _ hP
  have hm : 1 ≤ primeDenominator (primorialPrimes T) k := primeProduct_pos _ _ hP
  calc
    _ ≤ (K * horizontalLogRate T) * primeModeWeight (primorialPrimes T) k ^ 2 := hR _ _ hn hm
    _ ≤ _ := by simpa only [mul_assoc, mul_comm 4 K] using
      mul_le_mul_of_nonneg_left (hW k hk) hK.le

theorem eventually_primorialCharacter_remainder_eq_sample :
    ∀ᶠ T : ℝ in atTop,
      primeCharacterRemainder (primorialPrimes T) (fun _ => 1) T =
        sampleFunctional (primorialPrimes T) T (primorialCharacter T) / (T : ℂ) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 27] with T hT h27
  have h3 : 3 ≤ primorialCutoff T := by
    have hroot : (27 : ℝ) ^ (1 / 3 : ℝ) = 3 := by
      rw [show (27 : ℝ) = (3 : ℝ) ^ (3 : ℝ) by norm_num [Real.rpow_natCast],
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
    rw [← hroot]
    exact Real.rpow_le_rpow (by norm_num) h27 (by norm_num)
  have hp₂ : 2 ∈ primorialPrimes T := (mem_primorialPrimes hT).mpr
    ⟨Nat.prime_two, (by norm_num : (2 : ℝ) ≤ 3).trans h3⟩
  have hp₃ : 3 ∈ primorialPrimes T := (mem_primorialPrimes hT).mpr ⟨Nat.prime_three, h3⟩
  have hk : (fun _ : (primorialPrimes T : Finset ℕ) => (1 : ℤ)) ≠ 0 := by
    intro h
    have he := congrFun h (⟨2, hp₂⟩ : primorialPrimes T)
    norm_num at he
  have hP : ∀ p ∈ primorialPrimes T, p.Prime := fun _ hp => prime_of_mem_primorialPrimes hp
  have hmain := rationalFMZMain_prime_eq_zero_of_two_nonzero
    (primorialPrimes T) (fun _ => 1) hP hp₂ hp₃ (by decide) (by decide) (by decide)
  unfold primeCharacterRemainder primorialCharacter
  rw [haarIntegral_character_primeDensity (primorialPrimes T) (fun _ => 1) hP,
    hmain, haarIntegral_character_eq, if_neg hk]
  simp only [mul_zero, sub_zero]

/-- Unconditional quantitative cancellation for the all-ones growing-prime
character on the actual zeta-zero ordinates, counted with multiplicity. -/
theorem primorialCharacter_sample_div_isBigO :
    Asymptotics.IsBigO atTop (fun T =>
      sampleFunctional (primorialPrimes T) T (primorialCharacter T) / (T : ℂ))
      primorialFMZRate := by
  obtain ⟨K, hK, h⟩ := eventually_primorial_boundedMode_FMZ
  refine Asymptotics.IsBigO.of_bound K ?_
  filter_upwards [h, eventually_primorialCharacter_remainder_eq_sample] with T h hT
  rw [← hT]
  have hrate : primorialFMZRate T ≤ ‖primorialFMZRate T‖ := by
    rw [Real.norm_eq_abs]
    exact le_abs_self _
  exact (h (fun _ => 1) (by intro p hp; simp)).trans
    (mul_le_mul_of_nonneg_left hrate hK.le)

theorem tendsto_primorialCharacter_sample_div :
    Tendsto (fun T =>
      sampleFunctional (primorialPrimes T) T (primorialCharacter T) / (T : ℂ)) atTop (𝓝 0) :=
  primorialCharacter_sample_div_isBigO.trans_tendsto tendsto_primorialFMZRate

end RiemannResearch.Analysis.ActualPrimeTorusFMZ

#print axioms RiemannResearch.Analysis.ActualPrimeTorusFMZ.primorialCharacter_sample_div_isBigO
#print axioms RiemannResearch.Analysis.ActualPrimeTorusFMZ.tendsto_primorialCharacter_sample_div
