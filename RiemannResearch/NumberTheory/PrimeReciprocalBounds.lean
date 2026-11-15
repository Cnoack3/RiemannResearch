/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Explicit finite prime reciprocal bounds

The dyadic cardinality lemma is factored from RH/PrimeLogSummability.lean.
Chebyshev's unconditional estimate and a finite harmonic sum give an explicit
O(log log M) bound. No Mertens asymptotic is required.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.NumberTheory.PrimeReciprocalBounds

/-- Exact dyadic cardinality estimate, retaining the natural dyadic index. -/
theorem prime_dyadic_card_mul_le (s : Finset ℕ) (j : ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ 2 ^ j ≤ p ∧ p ≤ 2 ^ (j + 1)) :
    (s.card : ℝ) * j ≤ 4 * (2 : ℝ)^j := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlo : (s.card : ℝ) * ((j : ℝ) * Real.log 2) ≤
      ∑ p ∈ s, Real.log (p : ℝ) := by
    calc
      _ = ∑ _p ∈ s, (j : ℝ) * Real.log 2 := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p hp
        have h := Real.log_le_log (by positivity : 0 < (2 : ℝ)^j)
          (show (2 : ℝ)^j ≤ (p : ℝ) by exact_mod_cast (hs p hp).2.1)
        simpa only [Real.log_pow] using h
  have hsum : (∑ p ∈ s, Real.log (p : ℝ)) ≤
      Chebyshev.theta ((2 ^ (j + 1) : ℕ) : ℝ) := by
    rw [Chebyshev.theta_eq_sum_Icc]
    simp only [Nat.floor_natCast]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, (hs p hp).2.2⟩, (hs p hp).1⟩
    · intro p hp _
      exact Real.log_nonneg (by exact_mod_cast
        (Finset.mem_filter.mp hp).2.one_lt.le)
  have htheta := Chebyshev.theta_le_log4_mul_x
    (by positivity : 0 ≤ ((2 ^ (j + 1) : ℕ) : ℝ))
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  have hall := le_trans hlo (le_trans hsum htheta)
  rw [hlog4] at hall
  push_cast at hall
  rw [pow_succ] at hall
  apply (mul_le_mul_iff_of_pos_right hlog2).mp
  nlinarith


/-- The reciprocal mass in one dyadic prime block. -/
theorem prime_dyadic_reciprocal_sum_le (s : Finset ℕ) (j : ℕ)
    (hj : 0 < j)
    (hs : ∀ p ∈ s, p.Prime ∧ 2 ^ j ≤ p ∧ p ≤ 2 ^ (j + 1)) :
    (∑ p ∈ s, 1 / (p : ℝ)) ≤ 4 / (j : ℝ) := by
  have hjR : 0 < (j : ℝ) := by exact_mod_cast hj
  have h2pow : 0 < (2 : ℝ)^j := by positivity
  calc
    _ ≤ ∑ _p ∈ s, 1 / (2 : ℝ)^j := by
      apply Finset.sum_le_sum
      intro p hp
      exact one_div_le_one_div_of_le h2pow (by exact_mod_cast (hs p hp).2.1)
    _ = (s.card : ℝ) / (2 : ℝ)^j := by simp [div_eq_mul_inv]
    _ ≤ 4 / (j : ℝ) := by
      apply (div_le_div_iff₀ h2pow hjR).mpr
      exact prime_dyadic_card_mul_le s j hs

/-- A uniform, unconditional bound for every finite prime set below M. -/
theorem prime_reciprocal_sum_le (s : Finset ℕ) (M : ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ p ≤ M) :
    (∑ p ∈ s, 1 / (p : ℝ)) ≤
      4 * (1 + Real.log ((Nat.log 2 M : ℝ) + 1)) := by
  classical
  let levels := s.image (Nat.log 2)
  have hmaps : ∀ p ∈ s, Nat.log 2 p ∈ levels :=
    fun p hp => Finset.mem_image_of_mem _ hp
  have hlevel : ∀ j ∈ levels, 0 < j ∧ j ≤ Nat.log 2 M := by
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨p, hp, rfl⟩
    constructor
    · have h := (Nat.le_log_iff_pow_le (by norm_num : 1 < 2)
        (hs p hp).1.ne_zero).2 (by simpa using (hs p hp).1.two_le : 2 ^ 1 ≤ p)
      omega
    · exact Nat.log_mono_right (hs p hp).2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc
    _ ≤ ∑ j ∈ levels, 4 / (j : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      apply prime_dyadic_reciprocal_sum_le _ j (hlevel j hj).1
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hp, hpj⟩
      refine ⟨(hs p hp).1, ?_, ?_⟩
      · simpa [hpj] using Nat.pow_log_le_self 2 (hs p hp).1.ne_zero
      · simpa [hpj, Nat.succ_eq_add_one] using
          (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) p).le
    _ = 4 * ∑ j ∈ levels, 1 / (j : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ 4 * ∑ j ∈ Finset.Icc 1 (Nat.log 2 M + 1), 1 / (j : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        exact Finset.mem_Icc.mpr
          ⟨(hlevel j hj).1, (hlevel j hj).2.trans (Nat.le_succ _)⟩
      · intro j _ _
        positivity
    _ = 4 * (harmonic (Nat.log 2 M + 1) : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast, one_div]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [Nat.cast_add, Nat.cast_one] using
        harmonic_le_one_add_log (Nat.log 2 M + 1)

/-- The subtype form needed by prime-power products. -/
theorem prime_subtype_reciprocal_sum_le (s : Finset Nat.Primes) (M : ℕ)
    (hs : ∀ p ∈ s, p.val ≤ M) :
    (∑ p ∈ s, 1 / (p.val : ℝ)) ≤
      4 * (1 + Real.log ((Nat.log 2 M : ℝ) + 1)) := by
  classical
  have he : (∑ p ∈ s, 1 / (p.val : ℝ)) =
      ∑ p ∈ s.image Subtype.val, 1 / (p : ℝ) :=
    (Finset.sum_image (s := s) (g := fun p : Nat.Primes => p.val)
      (f := fun p : ℕ => 1 / (p : ℝ))
      (fun _ _ _ _ hab => Subtype.ext hab)).symm
  rw [he]
  apply prime_reciprocal_sum_le
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
  exact ⟨q.property, hs q hq⟩

end RiemannResearch.NumberTheory.PrimeReciprocalBounds
