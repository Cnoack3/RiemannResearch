/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.PrimeResamplingCore
import RiemannResearch.RH.PrimeValuationIndependence
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact geometric law and reversibility on arithmetic prime fibers

These probabilities refer to the actual p-adic exponent of a positive
integer under the inverse-square Q law. The complete fiber, including its
infinite tail, is enumerated by replacement of this exponent.
-/

noncomputable section
open scoped BigOperators ENNReal
namespace RiemannResearch.RH.PrimeResampling
open ZetaTwoHilbert ZetaTwoProbability

/-- The probability that a geometric prime valuation is nonzero. -/
def geometricParameter (p : ℕ) : ℝ := 1 / (p : ℝ) ^ 2

/-- The actual independent replacement probability of exponent k. -/
def geometricMass (p k : ℕ) : ℝ :=
  (1 - geometricParameter p) * geometricParameter p ^ k

theorem geometricParameter_nonneg (p : ℕ) : 0 ≤ geometricParameter p := by
  unfold geometricParameter
  positivity

theorem geometricParameter_lt_one (p : ℕ) (hp : p.Prime) :
    geometricParameter p < 1 := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  unfold geometricParameter
  apply (div_lt_one (by positivity : 0 < (p : ℝ) ^ 2)).mpr
  nlinarith

theorem geometricMass_nonneg (p k : ℕ) (hp : p.Prime) :
    0 ≤ geometricMass p k :=
  mul_nonneg (sub_nonneg.mpr (geometricParameter_lt_one p hp).le)
    (pow_nonneg (geometricParameter_nonneg p) k)

theorem geometricMass_eq (p k : ℕ) :
    geometricMass p k = (1 - 1 / (p : ℝ) ^ 2) * (1 / ((p : ℝ) ^ k) ^ 2) := by
  unfold geometricMass geometricParameter
  simp only [div_pow, one_pow, ← pow_mul, Nat.mul_comm]

theorem geometricMass_hasSum (p : ℕ) (hp : p.Prime) :
    HasSum (geometricMass p) 1 := by
  have hs : HasSum (fun k : ℕ => geometricParameter p ^ k)
      ((1 - geometricParameter p)⁻¹) :=
    hasSum_geometric_of_lt_one (geometricParameter_nonneg p) (geometricParameter_lt_one p hp)
  have he : HasSum (fun k : ℕ => (1 - geometricParameter p) * geometricParameter p ^ k)
      ((1 - geometricParameter p) * (1 - geometricParameter p)⁻¹) :=
    hs.mul_left (1 - geometricParameter p)
  have hne : 1 - geometricParameter p ≠ 0 :=
    ne_of_gt (sub_pos.mpr (geometricParameter_lt_one p hp))
  change HasSum (fun k : ℕ => (1 - geometricParameter p) * geometricParameter p ^ k) 1
  simpa only [mul_inv_cancel₀ hne] using he

theorem geometricMass_tsum (p : ℕ) (hp : p.Prime) :
    (∑' k : ℕ, geometricMass p k) = 1 := (geometricMass_hasSum p hp).tsum_eq

theorem geometricMass_tsum_ennreal (p : ℕ) (hp : p.Prime) :
    (∑' k : ℕ, ENNReal.ofReal (geometricMass p k)) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => geometricMass_nonneg p k hp)
    (geometricMass_hasSum p hp).summable, geometricMass_tsum p hp,
    ENNReal.ofReal_one]

/-- The geometric mass after deleting the stationary exponent. -/
def geometricOffDiagonal (p t k : ℕ) : ℝ :=
  if k = t then 0 else geometricMass p k

theorem geometricOffDiagonal_nonneg (p t k : ℕ) (hp : p.Prime) :
    0 ≤ geometricOffDiagonal p t k := by
  unfold geometricOffDiagonal
  split_ifs
  · exact le_rfl
  · exact geometricMass_nonneg p k hp

theorem geometricOffDiagonal_le (p t k : ℕ) (hp : p.Prime) :
    geometricOffDiagonal p t k ≤ geometricMass p k := by
  unfold geometricOffDiagonal
  split_ifs
  · exact geometricMass_nonneg p k hp
  · exact le_rfl

theorem geometricOffDiagonal_summable (p t : ℕ) (hp : p.Prime) :
    Summable (geometricOffDiagonal p t) :=
  Summable.of_nonneg_of_le (fun k => geometricOffDiagonal_nonneg p t k hp)
    (fun k => geometricOffDiagonal_le p t k hp) (geometricMass_hasSum p hp).summable

theorem geometricOffDiagonal_tsum_zero (p : ℕ) (hp : p.Prime) :
    (∑' k : ℕ, geometricOffDiagonal p 0 k) = geometricParameter p := by
  have ht := (geometricMass_hasSum p hp).summable.tsum_eq_zero_add
  rw [geometricMass_tsum p hp] at ht
  have hzero : geometricMass p 0 = 1 - geometricParameter p := by
    simp [geometricMass]
  rw [hzero] at ht
  rw [(geometricOffDiagonal_summable p 0 hp).tsum_eq_zero_add]
  simp only [geometricOffDiagonal, Nat.succ_ne_zero, if_false, if_true, zero_add]
  linarith

/-- The exit probability is at most one on occupied prime coordinates and
at most p^-2 on unoccupied coordinates. -/
theorem geometricOffDiagonal_tsum_le_one (p t : ℕ) (hp : p.Prime) :
    (∑' k : ℕ, geometricOffDiagonal p t k) ≤ 1 := by
  have h := (geometricOffDiagonal_summable p t hp).tsum_le_tsum
    (fun k => geometricOffDiagonal_le p t k hp) (geometricMass_hasSum p hp).summable
  simpa only [geometricMass_tsum p hp] using h

theorem geometricOffDiagonal_tsum_le (p t : ℕ) (hp : p.Prime) :
    (∑' k : ℕ, geometricOffDiagonal p t k) ≤
      (if t = 0 then 0 else 1) + geometricParameter p := by
  by_cases ht : t = 0
  · subst t
    rw [geometricOffDiagonal_tsum_zero p hp]
    simp
  · rw [if_neg ht]
    have h := (geometricOffDiagonal_summable p t hp).tsum_le_tsum
      (fun k => geometricOffDiagonal_le p t k hp) (geometricMass_hasSum p hp).summable
    rw [geometricMass_tsum p hp] at h
    linarith [geometricParameter_nonneg p]

theorem geometricOffDiagonal_tsum_ennreal_le (p t : ℕ) (hp : p.Prime) :
    (∑' k : ℕ, ENNReal.ofReal (geometricOffDiagonal p t k)) ≤
      ENNReal.ofReal ((if t = 0 then 0 else 1) + geometricParameter p) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun k => geometricOffDiagonal_nonneg p t k hp)
    (geometricOffDiagonal_summable p t hp)]
  exact ENNReal.ofReal_le_ofReal (geometricOffDiagonal_tsum_le p t hp)

/-- Geometric masses are exactly the already verified Q valuation law. -/
theorem geometricMass_eq_valuation_probability (p k : ℕ) (hp : p.Prime) :
    Q {n : ℕ+ | primeValuation p n = k} = ENNReal.ofReal (geometricMass p k) := by
  rw [measure_primeValuation_eq p k hp, geometricMass_eq]

/-- Complete fiber reindexing, including totalized sums. -/
theorem tsum_primeFiber_subtype (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0)
    (F : ℕ → ℝ) :
    (∑' m : {m : ℕ // primeCore p m = primeCore p n}, F m.val) =
      ∑' k : ℕ, F (replaceValuation p n k) := by
  exact ((primeFiberEquiv p n hp hn).tsum_eq (fun m => F m.val)).symm

/-- Indicator form of the complete arithmetic fiber reindexing. -/
theorem tsum_primeFiber (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0)
    (F : ℕ → ℝ) :
    (∑' m : ℕ, if primeCore p m = primeCore p n then F m else 0) =
      ∑' k : ℕ, F (replaceValuation p n k) := by
  classical
  calc
    _ = ∑' m : ℕ, ({m : ℕ | primeCore p m = primeCore p n} : Set ℕ).indicator F m := by
      apply tsum_congr
      intro m
      by_cases h : primeCore p m = primeCore p n <;> simp [Set.indicator, h]
    _ = ∑' m : {m : ℕ // primeCore p m = primeCore p n}, F m.val :=
      (tsum_subtype {m : ℕ | primeCore p m = primeCore p n} F).symm
    _ = _ := tsum_primeFiber_subtype p n hp hn F

theorem tsum_primeFiber_ennreal (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0)
    (F : ℕ → ℝ≥0∞) :
    (∑' m : ℕ, if primeCore p m = primeCore p n then F m else 0) =
      ∑' k : ℕ, F (replaceValuation p n k) := by
  classical
  calc
    _ = ∑' m : ℕ, ({m : ℕ | primeCore p m = primeCore p n} : Set ℕ).indicator F m := by
      apply tsum_congr
      intro m
      by_cases h : primeCore p m = primeCore p n <;> simp [Set.indicator, h]
    _ = ∑' m : {m : ℕ // primeCore p m = primeCore p n}, F m.val :=
      (tsum_subtype {m : ℕ | primeCore p m = primeCore p n} F).symm
    _ = _ := ((primeFiberEquiv p n hp hn).tsum_eq (fun m => F m.val)).symm

theorem summable_replaceValuation (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0)
    (F : ℕ → ℝ) (hF : Summable F) :
    Summable (fun k : ℕ => F (replaceValuation p n k)) :=
  hF.comp_injective (replaceValuation_injective p n hp hn)

/-- The inverse-square weight splits exactly into core weight and prime factor. -/
theorem positiveQWeight_replaceValuation (p n k : ℕ) :
    positiveQWeight (replaceValuation p n k) =
      positiveQWeight (primeCore p n) * geometricParameter p ^ k := by
  unfold positiveQWeight replaceValuation geometricParameter
  simp only [Nat.cast_mul, Nat.cast_pow, mul_pow, div_pow, one_pow, ← pow_mul,
    Nat.mul_comm]
  ring

/-- The complete Q mass of one p-free fiber. -/
def primeFiberMass (p n : ℕ) : ℝ :=
  positiveQWeight (primeCore p n) / (1 - geometricParameter p)

theorem primeFiberMass_pos (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    0 < primeFiberMass p n := by
  have hz := zetaTwo_pos
  have hc : (0 : ℝ) < primeCore p n := by
    exact_mod_cast primeCore_pos p n (Nat.pos_of_ne_zero hn)
  unfold primeFiberMass positiveQWeight
  exact div_pos (by positivity) (sub_pos.mpr (geometricParameter_lt_one p hp))

theorem positiveQWeight_eq_fiberMass_mul_geometricMass
    (p n k : ℕ) (hp : p.Prime) :
    positiveQWeight (replaceValuation p n k) =
      primeFiberMass p n * geometricMass p k := by
  rw [positiveQWeight_replaceValuation]
  unfold primeFiberMass geometricMass
  have hne : 1 - geometricParameter p ≠ 0 :=
    ne_of_gt (sub_pos.mpr (geometricParameter_lt_one p hp))
  field_simp

theorem primeFiberMass_tsum (p n : ℕ) (hp : p.Prime) :
    (∑' k : ℕ, positiveQWeight (replaceValuation p n k)) = primeFiberMass p n := by
  simp_rw [positiveQWeight_eq_fiberMass_mul_geometricMass p n _ hp]
  rw [tsum_mul_left, geometricMass_tsum p hp, mul_one]

/-- Detailed balance for actual integers in the same prime fiber. -/
theorem geometric_detailed_balance (p n m : ℕ)
    (hcore : primeCore p n = primeCore p m) :
    positiveQWeight n * geometricMass p (m.factorization p) =
      positiveQWeight m * geometricMass p (n.factorization p) := by
  have hn := positiveQWeight_replaceValuation p n (n.factorization p)
  have hm := positiveQWeight_replaceValuation p m (m.factorization p)
  rw [replaceValuation_self] at hn hm
  rw [hn, hm, hcore]
  unfold geometricMass
  ring

end RiemannResearch.RH.PrimeResampling
