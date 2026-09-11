/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoProgressionTaylor
import Mathlib.Analysis.SumOverResidueClass

/-!
# Actual residue-weight estimates for reflection conditioning

Source: the user's law-of-total-variance discussion, 11 September 2026.
The weights are the complete Pareto progression masses, including the
infinite tail. These estimates support the reflection-pair variance split.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

/-- Every positive representative at most Q has full residue mass at least
Q^-2. This is stronger than bounding the first atom alone. -/
theorem progressionWeight_ge_inv_sq (Q r : ℕ) (hQ : 0 < Q)
    (hr : 0 < r) (hrQ : r ≤ Q) :
    1 / (Q : ℝ)^2 ≤ progressionWeight Q r := by
  calc
    _ ≤ 1 / ((Q : ℝ) * (r : ℝ)) := by
      apply one_div_le_one_div_of_le (by positivity)
      have hrQ' : (r : ℝ) ≤ Q := by exact_mod_cast hrQ
      simpa only [pow_two] using
        mul_le_mul_of_nonneg_left hrQ' (Nat.cast_nonneg (α := ℝ) Q)
    _ ≤ _ := progressionWeight_lower Q r hQ hr

/-- The odd part of the Basel series is summable. -/
theorem odd_reciprocal_square_summable :
    Summable (fun j : ℕ => 1 / (2 * (j : ℝ) + 1)^2) := by
  have hs := hasSum_zeta_two.summable.comp_injective
    (show Function.Injective (fun j : ℕ => 2*j+1) from by
      intro i j hij
      change 2*i+1 = 2*j+1 at hij
      omega)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one] using hs

/-- Exact odd Basel sum; this supplies the constant in the upper-half bound. -/
theorem odd_reciprocal_square_tsum :
    (∑' j : ℕ, 1 / (2 * (j : ℝ) + 1)^2) = Real.pi^2 / 8 := by
  have heven : (∑' j : ℕ, 1 / ((2*j : ℕ) : ℝ)^2) =
      (1/4 : ℝ) * (Real.pi^2/6) := by
    calc
      _ = ∑' j : ℕ, (1/4 : ℝ) * (1 / (j : ℝ)^2) := by
        apply tsum_congr
        intro j
        simp only [Nat.cast_mul, Nat.cast_ofNat, mul_pow]
        rw [← one_div_mul_one_div]
        norm_num
      _ = _ := by rw [tsum_mul_left, hasSum_zeta_two.tsum_eq]
  have hraw : (∑' j : ℕ, 1 / (j : ℝ)^2) =
      ∑ r : Fin 2, ∑' j : ℕ, 1 / (((r.val+2*j : ℕ) : ℝ))^2 :=
    Nat.sumByResidueClasses hasSum_zeta_two.summable 2
  have hsplit : (∑' j : ℕ, 1 / (j : ℝ)^2) =
      (∑' j : ℕ, 1 / ((2*j : ℕ) : ℝ)^2) +
        (∑' j : ℕ, 1 / ((2*j+1 : ℕ) : ℝ)^2) := by
    simpa [Fin.sum_univ_succ, Nat.add_comm] using hraw
  rw [heven, hasSum_zeta_two.tsum_eq] at hsplit
  have hodd : (∑' j : ℕ, 1 / ((2*j+1 : ℕ) : ℝ)^2) =
      ∑' j : ℕ, 1 / (2 * (j : ℝ) + 1)^2 := by
    apply tsum_congr
    intro j
    push_cast
    rfl
  rw [hodd] at hsplit
  linarith

private theorem progression_atom_le_half_series (Q r j : ℕ)
    (hQ : 0 < Q) (hr : 0 < r) (hhalf : Q ≤ 2*r) :
    positiveWeight (r + Q*j) ≤
      (4 / (Q : ℝ)^2) * (1 / (2 * (j : ℝ) + 1)^2) := by
  have hq : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hh : (Q : ℝ) ≤ 2*(r : ℝ) := by exact_mod_cast hhalf
  have hj : (0 : ℝ) ≤ j := by positivity
  have hbase : (Q : ℝ)*((j : ℝ)+1/2) ≤ (r : ℝ)+Q*j := by nlinarith
  have hbase0 : 0 < (Q : ℝ)*((j : ℝ)+1/2) := by positivity
  have hsquare : ((Q : ℝ)*((j : ℝ)+1/2))^2 ≤ ((r : ℝ)+Q*j)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hbase)
      (show 0 ≤ ((r : ℝ)+Q*j) + ((Q : ℝ)*((j : ℝ)+1/2)) by positivity)]
  calc
    _ ≤ 1 / ((Q : ℝ)*((j : ℝ)+1/2))^2 := by
      unfold positiveWeight
      push_cast
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    _ = _ := by
      have hodd : 2*(j : ℝ)+1 ≠ 0 := by positivity
      have hmid : (j : ℝ)+1/2 ≠ 0 := by positivity
      field_simp
      <;> ring

/-- A residue in the upper half of the period has mass at most pi^2/(2Q^2).
No parity hypothesis on Q is needed for this local estimate. -/
theorem progressionWeight_upper_half (Q r : ℕ) (hQ : 0 < Q)
    (hr : 0 < r) (hhalf : Q ≤ 2*r) :
    progressionWeight Q r ≤ Real.pi^2 / (2*(Q : ℝ)^2) := by
  calc
    _ ≤ ∑' j : ℕ, (4 / (Q : ℝ)^2) * (1 / (2*(j : ℝ)+1)^2) := by
      exact Summable.tsum_le_tsum (fun j => progression_atom_le_half_series Q r j hQ hr hhalf)
        (progressionWeight_summable Q r hQ)
        (odd_reciprocal_square_summable.mul_left _)
    _ = (4 / (Q : ℝ)^2) * (Real.pi^2/8) := by
      rw [tsum_mul_left, odd_reciprocal_square_tsum]
    _ = _ := by ring

end
end RiemannResearch.RH.Pareto
