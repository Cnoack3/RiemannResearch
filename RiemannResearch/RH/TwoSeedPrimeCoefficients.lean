/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.TwoSeedContrastObstruction

/-!
# Prime coefficient recovery for finite two-seed representations

Source: user-provided
RH_Zero_Ordinates_Haar_and_Actual_Residual_Gain_Consolidated_2026-10-11.md,
Section 12.2 (necessary prime coefficient sums).
The complete Pareto energy split and quantitative stability are derived here
from the actual Mobius coordinate and its Riesz representer.
Representations may be dependent; only the sum at a prime is recovered.
Norm convergence is an explicit hypothesis of the limiting theorem.
-/
open Filter
open scoped Topology BigOperators
noncomputable section
namespace RiemannResearch.RH.Pareto.TwoSeedPrimeCoefficients
open AdjacentPacket FiniteTwoSeedCompletion RamanujanLaguerre ContrastObstruction

/-- Arbitrary finite two-seed representation, with no independence assumption. -/
def combination (S : Finset {m : ℕ // 0 < m})
    (a b : {m : ℕ // 0 < m} → ℝ) : ThresholdHilbert :=
  ∑ m ∈ S, (a m • generator 2 m.val (by omega) m.property +
    b m • generator 3 m.val (by omega) m.property)

def coefficientSum (S : Finset {m : ℕ // 0 < m})
    (a b : {m : ℕ // 0 < m} → ℝ) (q : ℕ) (hq : 0 < q) : ℝ :=
  if ⟨q, hq⟩ ∈ S then a ⟨q, hq⟩ + b ⟨q, hq⟩ else 0

theorem prime_coordinate_combination (S : Finset {m : ℕ // 0 < m})
    (a b : {m : ℕ // 0 < m} → ℝ) (q : ℕ)
    (hq : q.Prime) (hq3 : 3 < q) :
    mobiusDifferenceCLM q (combination S a b) =
      (q : ℝ) * coefficientSum S a b q hq.pos := by
  classical
  unfold combination
  rw [map_sum]
  have he : (∑ m ∈ S, mobiusDifferenceCLM q
      (a m • generator 2 m.val (by omega) m.property +
        b m • generator 3 m.val (by omega) m.property)) =
      ∑ m ∈ S, if m = ⟨q, hq.pos⟩ then
        (q : ℝ) * (a m + b m) else 0 := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [map_add, map_smul, map_smul,
      prime_mobius_generator_coordinate q 2 m.val hq hq3 _ _ (Or.inl rfl),
      prime_mobius_generator_coordinate q 3 m.val hq hq3 _ _ (Or.inr rfl)]
    by_cases h : m = ⟨q, hq.pos⟩
    · subst m
      simp
      ring
    · have hn : q ≠ m.val := by
        intro hv
        apply h
        exact Subtype.ext hv.symm
      simp [h, hn]
  rw [he]
  simp [coefficientSum]

theorem prime_coefficient_error_sq (S : Finset {m : ℕ // 0 < m})
    (a b : {m : ℕ // 0 < m} → ℝ) (q : ℕ)
    (hq : q.Prime) (hq3 : 3 < q) :
    ((q : ℝ) * coefficientSum S a b q hq.pos + 1)^2 ≤
      2*((q : ℝ)^2+1) * ‖hilbertOne - combination S a b‖^2 := by
  have hb := (mobiusDifferenceCLM q).le_opNorm (hilbertOne - combination S a b)
  rw [map_sub, prime_coordinate_one q hq, prime_coordinate_combination S a b q hq hq3] at hb
  have hs := mul_self_le_mul_self (norm_nonneg _) hb
  simp only [← pow_two] at hs
  rw [mul_pow, mobiusDifferenceCLM_prime_norm_sq q hq (by omega)] at hs
  simp only [Real.norm_eq_abs, sq_abs] at hs
  nlinarith [hs]

theorem prime_coefficient_sum_tendsto
    (S : ℕ → Finset {m : ℕ // 0 < m})
    (a b : ℕ → {m : ℕ // 0 < m} → ℝ) (q : ℕ)
    (hq : q.Prime) (hq3 : 3 < q)
    (hF : Tendsto (fun n => combination (S n) (a n) (b n)) atTop (𝓝 hilbertOne)) :
    Tendsto (fun n => coefficientSum (S n) (a n) (b n) q hq.pos)
      atTop (𝓝 (-1 / (q : ℝ))) := by
  have ht := ((mobiusDifferenceCLM q).continuous.tendsto hilbertOne).comp hF
  rw [prime_coordinate_one q hq] at ht
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hd := ht.div_const (q : ℝ)
  simpa only [Function.comp_apply,
    prime_coordinate_combination _ _ _ q hq hq3, mul_div_cancel_left₀ _ hqR] using hd

/-- Complete energy split at a prime coordinate; the remainder square is retained. -/
theorem prime_coefficient_error_identity (S : Finset {m : ℕ // 0 < m})
    (a b : {m : ℕ // 0 < m} → ℝ) (q : ℕ)
    (hq : q.Prime) (hq3 : 3 < q) :
    ‖hilbertOne - combination S a b‖^2 =
      ((q : ℝ) * coefficientSum S a b q hq.pos + 1)^2 / (2*((q : ℝ)^2+1)) +
      ‖hilbertOne - combination S a b +
        (((q : ℝ) * coefficientSum S a b q hq.pos + 1)/(2*((q : ℝ)^2+1))) •
          mobiusRieszHilbert q‖^2 := by
  have hi : inner ℝ (hilbertOne - combination S a b) (mobiusRieszHilbert q) =
      -1 - (q : ℝ) * coefficientSum S a b q hq.pos := by
    rw [real_inner_comm, mobiusRieszHilbert_inner, map_sub,
      prime_coordinate_one q hq, prime_coordinate_combination S a b q hq hq3]
  rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_right, hi, mobiusRieszHilbert_norm,
    mobiusDifferenceCLM_prime_norm_sq q hq (by omega)]
  have hn : 2*((q : ℝ)^2+1) ≠ 0 := by positivity
  field_simp [hn]
  ring

theorem prime_coefficient_sum_error_bound (S : Finset {m : ℕ // 0 < m})
    (a b : {m : ℕ // 0 < m} → ℝ) (q : ℕ)
    (hq : q.Prime) (hq3 : 3 < q) :
    (coefficientSum S a b q hq.pos + 1/(q : ℝ))^2 ≤
      (2 + 2/(q : ℝ)^2) * ‖hilbertOne - combination S a b‖^2 := by
  have h := prime_coefficient_error_sq S a b q hq hq3
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have heL :
      (coefficientSum S a b q hq.pos + 1/(q : ℝ))^2 =
        ((q : ℝ) * coefficientSum S a b q hq.pos + 1)^2 / (q : ℝ)^2 := by
    field_simp [hqR]
  have heR :
      (2 + 2/(q : ℝ)^2) * ‖hilbertOne - combination S a b‖^2 =
        (2*((q : ℝ)^2+1) * ‖hilbertOne - combination S a b‖^2) / (q : ℝ)^2 := by
    field_simp [hqR]
  rw [heL, heR]
  exact div_le_div_of_nonneg_right h (sq_nonneg (q : ℝ))

end RiemannResearch.RH.Pareto.TwoSeedPrimeCoefficients
