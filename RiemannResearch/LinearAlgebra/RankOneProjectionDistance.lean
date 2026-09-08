import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw

/-!
# Exact finite rank-one projection distance

Source: user-provided `RH_Two_Seed_Threshold.tex`, September 8, 2026,
Section 11.2, proof of the affine phase-constant identity.

This module proves the finite real coordinate identity that underlies the
Hilbert--Schmidt calculation on each affine block. It does not identify
the infinite Hilbert--Schmidt norm or justify passage to the limit.
-/

open scoped BigOperators

namespace Real

/-- The exact sum of all squared entries in the difference of two rank-one
matrices. No mixed coordinate is discarded. -/
theorem rankOne_difference_sum_sq {ι : Type*} (s : Finset ι) (u v : ι → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, (u i * u j - v i * v j) ^ 2) =
      (∑ i ∈ s, u i ^ 2) ^ 2 + (∑ i ∈ s, v i ^ 2) ^ 2 -
        2 * (∑ i ∈ s, u i * v i) ^ 2 := by
  have factor (f g : ι → ℝ) :
      (∑ i ∈ s, ∑ j ∈ s, f i * g j) =
        (∑ i ∈ s, f i) * (∑ j ∈ s, g j) := by
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
  calc
    _ = ∑ i ∈ s, ∑ j ∈ s,
        (u i ^ 2 * u j ^ 2 + v i ^ 2 * v j ^ 2 -
          (2 * (u i * v i)) * (u j * v j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (∑ i ∈ s, ∑ j ∈ s, u i ^ 2 * u j ^ 2) +
        (∑ i ∈ s, ∑ j ∈ s, v i ^ 2 * v j ^ 2) -
        (∑ i ∈ s, ∑ j ∈ s, (2 * (u i * v i)) * (u j * v j)) := by
      simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ = _ := by
      rw [factor, factor, factor, ← Finset.mul_sum]
      ring

/-- For unit columns the squared Hilbert--Schmidt distance of their real
rank-one matrices is exactly twice one minus their squared overlap. -/
theorem unit_rankOne_difference_sum_sq {ι : Type*} (s : Finset ι)
    (u v : ι → ℝ) (hu : (∑ i ∈ s, u i ^ 2) = 1)
    (hv : (∑ i ∈ s, v i ^ 2) = 1) :
    (∑ i ∈ s, ∑ j ∈ s, (u i * u j - v i * v j) ^ 2) =
      2 * (1 - (∑ i ∈ s, u i * v i) ^ 2) := by
  rw [rankOne_difference_sum_sq, hu, hv]
  ring

end Real
