/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Complete reciprocal Bessel budget

Source: direct Hilbert-space continuation of the user's squarefree moment
budget request. The exact diagonal square sum of B is zeta(2)-1; no physical
tail is omitted. Its consumer is QSmoothedResponseVariation.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QShiftedReciprocal
open ZetaTwoHilbert ZetaTwoProbability

/-- Bessel's inequality in the actual normalized Q coordinates. -/
theorem orthonormal_coordinate_square_sum_le_one {ι : Type*}
    (u : ι → QHilbert) (hu : Orthonormal ℝ u) (s : Finset ι) (n : ℕ) :
    (∑ i ∈ s, (u i n)^2) ≤ 1 := by
  classical
  let e : QHilbert := lp.single 2 n (1 : ℝ)
  have he : ‖e‖^2 = 1 := by
    dsimp only [e]
    rw [lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
    norm_num
  have hi (i : ι) : inner ℝ (u i) e = u i n := by
    dsimp only [e]
    rw [lp.inner_single_right]
    change (1 : ℝ) * u i n = u i n
    ring
  calc
    (∑ i ∈ s, (u i n)^2) = ∑ i ∈ s, ‖inner ℝ (u i) e‖^2 := by
      apply Finset.sum_congr rfl
      intro i hi'
      rw [hi, Real.norm_eq_abs, sq_abs]
    _ ≤ ‖e‖^2 := hu.sum_inner_products_le e
    _ = 1 := he

theorem shifted_reciprocal_square_summable :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 2)^2) := by
  have h := Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))
  simpa only [Nat.cast_add, Nat.cast_ofNat] using (summable_nat_add_iff 2).mpr h

/-- The complete Hilbert--Schmidt budget, without truncating physical sites. -/
theorem shifted_reciprocal_square_tsum :
    (∑' n : ℕ, 1 / ((n : ℝ) + 2)^2) = zetaTwo - 1 := by
  have h0 := Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))
  have h1 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)^2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr h0
  have hz : zetaTwo = ∑' n : ℕ, 1 / ((n : ℝ) + 1)^2 := by
    rw [zetaTwo_eq_nat_sum, h0.tsum_eq_zero_add]
    norm_num
  have ht : (∑' n : ℕ, 1 / ((n : ℝ) + 1)^2) =
      1 + ∑' n : ℕ, 1 / ((n : ℝ) + 2)^2 := by
    rw [h1.tsum_eq_zero_add]
    norm_num only [Nat.cast_zero, zero_add, one_pow, div_one]
    congr 1
    apply tsum_congr
    intro n
    push_cast
    congr 2
    ring
  rw [ht] at hz
  linarith

/-- The shifted reciprocal has one common square-energy budget on every
finite orthonormal family. All complete physical tails are included. -/
theorem orthonormal_B_norm_sq_sum_le {ι : Type*}
    (u : ι → QHilbert) (hu : Orthonormal ℝ u) (s : Finset ι) :
    (∑ i ∈ s, ‖B (u i)‖^2) ≤ zetaTwo - 1 := by
  classical
  have hbound (n : ℕ) :
      (∑ i ∈ s, (B (u i) n)^2) ≤ 1 / ((n : ℝ) + 2)^2 := by
    simp only [B_apply, div_pow]
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right
      (orthonormal_coordinate_square_sum_le_one u hu s n) (sq_nonneg _)
  have hsum : Summable (fun n : ℕ => ∑ i ∈ s, (B (u i) n)^2) := by
    apply Summable.of_nonneg_of_le _ hbound shifted_reciprocal_square_summable
    intro n
    exact Finset.sum_nonneg (fun i hi => sq_nonneg _)
  calc
    (∑ i ∈ s, ‖B (u i)‖^2) = ∑' n : ℕ, ∑ i ∈ s, (B (u i) n)^2 := by
      simp_rw [qNorm_sq]
      exact (Summable.tsum_finsetSum
        (fun i (_ : i ∈ s) => qCoordinate_square_summable (B (u i)))).symm
    _ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 2)^2 :=
      Summable.tsum_le_tsum hbound hsum shifted_reciprocal_square_summable
    _ = zetaTwo - 1 := shifted_reciprocal_square_tsum

theorem orthonormal_B_norm_sq_summable {ι : Type*}
    (u : ι → QHilbert) (hu : Orthonormal ℝ u) :
    Summable (fun i => ‖B (u i)‖^2) := by
  apply summable_of_sum_le (c := zetaTwo - 1) (fun i => sq_nonneg _)
  intro s
  exact orthonormal_B_norm_sq_sum_le u hu s

theorem orthonormal_B_norm_sq_tsum_le {ι : Type*}
    (u : ι → QHilbert) (hu : Orthonormal ℝ u) :
    (∑' i, ‖B (u i)‖^2) ≤ zetaTwo - 1 := by
  have hz : 0 ≤ zetaTwo - 1 := by
    simpa using orthonormal_B_norm_sq_sum_le u hu (∅ : Finset ι)
  exact tsum_le_of_sum_le' hz (orthonormal_B_norm_sq_sum_le u hu)

end RiemannResearch.RH.QShiftedReciprocal
