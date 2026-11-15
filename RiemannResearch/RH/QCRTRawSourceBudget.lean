/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCRTNestedCutoffs
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Finite budgets for unnormalized canonical difference-test sources

Source: `CanonicalPrimePowerUpdatesResearch20261107.md`, Section 2.
The bounds are for raw test rows. They do not control the nonsymmetric
collocation inverse or the physical canonical-update norm.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.QCRTRawSourceBudget
open ZetaTwoHilbert ZetaTwoProbability QCRTFiniteCollocation QCRTNestedCutoffs
open QPhysicalDifference QDivisibilityDensity

/-- Every finite inverse-square row budget lies below the complete zeta sum.
The zero index, if present, contributes zero. -/
theorem sum_inverse_sq_le_zetaTwo (s : Finset ℕ) :
    (∑ e ∈ s, 1 / (e : ℝ) ^ 2) ≤ zetaTwo := by
  rw [zetaTwo_eq_nat_sum]
  exact Summable.sum_le_tsum s (fun _ _ => by positivity)
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))

/-- The exact signed new-row sum before estimating its mixed correlations.
`hrows` is the finite arithmetic admission condition `lcm(L,a*e)=M`. -/
theorem sum_new_difference_source_sq_exact (L M a : ℕ) (hL : 2 ≤ L)
    (hM : 0 < M) (s : Finset ℕ)
    (hrows : ∀ e ∈ s, 2 ≤ a * e ∧ a * e ∣ M ∧ Nat.lcm L (a * e) = M) :
    (∑ e ∈ s,
      (inner ℝ (target M - canonical L hL)
        (differenceCLM (qResidue (a * e)))) ^ 2) =
    ∑ e ∈ s,
      ((1 / ((a * e : ℕ) : ℝ)) *
        (1 / (L : ℝ) ^ 2 - 1 / (M : ℝ) ^ 2) +
        inner ℝ (leakageVector L hL) (qDivisor (a * e))) ^ 2 := by
  apply Finset.sum_congr rfl
  intro e he
  rw [signed_difference_update_source_new L M (a * e) hL hM
    (hrows e he).1 (hrows e he).2.1 (hrows e he).2.2]

/-- Finite unnormalized row budget. The complete leakage energy remains;
normalization of the divisor tests removes the apparent depth gain. -/
theorem sum_new_difference_source_sq_le (L M a : ℕ) (hL : 2 ≤ L)
    (hM : 0 < M) (ha : 0 < a) (s : Finset ℕ)
    (hrows : ∀ e ∈ s, 2 ≤ a * e ∧ a * e ∣ M ∧ Nat.lcm L (a * e) = M) :
    (∑ e ∈ s,
      (inner ℝ (target M - canonical L hL)
        (differenceCLM (qResidue (a * e)))) ^ 2) ≤
      (2 * zetaTwo / (a : ℝ) ^ 2) *
        ((1 / (L : ℝ) ^ 2 - 1 / (M : ℝ) ^ 2) ^ 2 + leakage L hL) := by
  let δ : ℝ := 1 / (L : ℝ) ^ 2 - 1 / (M : ℝ) ^ 2
  have hpos : (0 : ℝ) < a := by exact_mod_cast ha
  have hb : 0 ≤ δ ^ 2 + leakage L hL := by
    exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hpoint : ∀ e ∈ s,
      (inner ℝ (target M - canonical L hL)
        (differenceCLM (qResidue (a * e)))) ^ 2 ≤
        (2 * (δ ^ 2 + leakage L hL) / (a : ℝ) ^ 2) *
          (1 / (e : ℝ) ^ 2) := by
    intro e he
    have hae : 0 < a * e := lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ)) (hrows e he).1
    have hepos : 0 < e := by
      by_contra hh
      have he0 : e = 0 := Nat.eq_zero_of_not_pos hh
      simp [he0] at hae
    have heR : (0 : ℝ) < e := by exact_mod_cast hepos
    have hq := leakage_divisor_moment_sq_le L (a * e) hL hae
    rw [signed_difference_update_source_new L M (a * e) hL hM
      (hrows e he).1 (hrows e he).2.1 (hrows e he).2.2]
    change ((1 / ((a * e : ℕ) : ℝ)) * δ +
      inner ℝ (leakageVector L hL) (qDivisor (a * e))) ^ 2 ≤ _
    have hs :
        ((1 / ((a * e : ℕ) : ℝ)) * δ +
          inner ℝ (leakageVector L hL) (qDivisor (a * e))) ^ 2 ≤
        2 * (δ ^ 2 + leakage L hL) / ((a * e : ℕ) : ℝ) ^ 2 := by
      have hu : ((1 / ((a * e : ℕ) : ℝ)) * δ) ^ 2 =
          δ ^ 2 / ((a * e : ℕ) : ℝ) ^ 2 := by
        simp only [mul_pow, div_pow, one_pow]
        ring
      have hcross := sq_nonneg
        ((1 / ((a * e : ℕ) : ℝ)) * δ -
          inner ℝ (leakageVector L hL) (qDivisor (a * e)))
      calc
        _ ≤ 2 * (((1 / ((a * e : ℕ) : ℝ)) * δ) ^ 2 +
            (inner ℝ (leakageVector L hL) (qDivisor (a * e))) ^ 2) := by
          nlinarith
        _ ≤ 2 * (δ ^ 2 / ((a * e : ℕ) : ℝ) ^ 2 +
            leakage L hL / ((a * e : ℕ) : ℝ) ^ 2) := by
          rw [hu]
          linarith
        _ = _ := by ring
    calc
      _ ≤ 2 * (δ ^ 2 + leakage L hL) / ((a * e : ℕ) : ℝ) ^ 2 := hs
      _ = _ := by
        push_cast
        field_simp [ne_of_gt hpos, ne_of_gt heR]
  calc
    _ ≤ ∑ e ∈ s, (2 * (δ ^ 2 + leakage L hL) / (a : ℝ) ^ 2) *
        (1 / (e : ℝ) ^ 2) := Finset.sum_le_sum hpoint
    _ = (2 * (δ ^ 2 + leakage L hL) / (a : ℝ) ^ 2) *
        (∑ e ∈ s, 1 / (e : ℝ) ^ 2) := by rw [Finset.mul_sum]
    _ ≤ (2 * (δ ^ 2 + leakage L hL) / (a : ℝ) ^ 2) * zetaTwo :=
      mul_le_mul_of_nonneg_left (sum_inverse_sq_le_zetaTwo s) (by positivity)
    _ = _ := by ring

end RiemannResearch.RH.QCRTRawSourceBudget
