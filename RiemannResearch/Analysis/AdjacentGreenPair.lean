/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.LinearAlgebra.FinitePairVariance
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Adjacent-pair completion for the Pareto Green energy

Source: user-provided argument, 14 September 2026.  The source has compulsory
unit jumps at odd rough integers.  Legal cumulative columns have zero jump
there.  Disjoint neighboring coordinate pairs therefore have the exact
orthogonal splitting below.  This module supplies the local and finite-sum
identities, and a uniform cubic tail bound for replacing the optimal local
profile by its symmetric counterpart.  It does not assert decay of the
remaining distance to the legal-column span.

The general two-weight variance identity is already in `FinitePairVariance`.
The formulas here evaluate its coefficients at the actual Pareto weights.
The two arrays in `pairedEnergy` are the two coordinates of each pair, so that
the represented coordinate space is a disjoint union of two-point pairs.
-/

open scoped BigOperators

namespace RiemannResearch.Analysis.AdjacentGreenPair

noncomputable section

/-- Energy on the physical coordinates `n - 1` and `n`. -/
def pairEnergy (n a b : ℝ) : ℝ :=
  a ^ 2 / ((n - 1) * n) + b ^ 2 / (n * (n + 1))

/-- Left coordinate of the least-energy profile with prescribed jump `j`. -/
def localLeft (n j : ℝ) : ℝ := -(n - 1) * j / (2 * n)

/-- Right coordinate of the least-energy profile with prescribed jump `j`. -/
def localRight (n j : ℝ) : ℝ := (n + 1) * j / (2 * n)

/-- Squared Green distance from the optimal unit-jump profile to `(-1/2,1/2)`. -/
def unitCorrection (n : ℝ) : ℝ := 1 / (2 * n ^ 2 * (n ^ 2 - 1))

theorem pairEnergy_nonneg (n a b : ℝ) (hn : 1 < n) :
    0 ≤ pairEnergy n a b := by
  have h0 : 0 < n := by linarith
  have h1 : 0 < n - 1 := by linarith
  have h2 : 0 < n + 1 := by linarith
  unfold pairEnergy
  positivity

/-- Exact square completion; in particular the local floor is `j²/(2n²)`. -/
theorem pairEnergy_completion (n a j : ℝ) (hn : 1 < n) :
    pairEnergy n a (a + j) =
      j ^ 2 / (2 * n ^ 2) +
        2 / (n ^ 2 - 1) * (a + (n - 1) * j / (2 * n)) ^ 2 := by
  have h0 : n ≠ 0 := by linarith
  have h1 : n - 1 ≠ 0 := by linarith
  have h2 : n + 1 ≠ 0 := by linarith
  have h3 : n ^ 2 - 1 ≠ 0 := by nlinarith [sq_nonneg (n - 1)]
  unfold pairEnergy
  field_simp [h0, h1, h2, h3]
  ring

theorem localRight_sub_localLeft (n j : ℝ) (hn : 1 < n) :
    localRight n j - localLeft n j = j := by
  have h0 : n ≠ 0 := by linarith
  unfold localRight localLeft
  field_simp [h0]
  ring

/-- The signed cross term vanishes exactly for the optimal compulsory jump. -/
theorem pairEnergy_pythagoras (n a b j : ℝ) (hn : 1 < n)
    (hjump : b - a = j) :
    pairEnergy n a b = j ^ 2 / (2 * n ^ 2) +
      pairEnergy n (a - localLeft n j) (b - localRight n j) := by
  have h0 : n ≠ 0 := by linarith
  have h1 : n - 1 ≠ 0 := by linarith
  have h2 : n + 1 ≠ 0 := by linarith
  have hb : b = a + j := by linarith
  rw [hb]
  unfold pairEnergy localLeft localRight
  field_simp [h0, h1, h2]
  ring

theorem local_floor_le_pairEnergy (n a b j : ℝ) (hn : 1 < n)
    (hjump : b - a = j) :
    j ^ 2 / (2 * n ^ 2) ≤ pairEnergy n a b := by
  rw [pairEnergy_pythagoras n a b j hn hjump]
  exact le_add_of_nonneg_right (pairEnergy_nonneg n _ _ hn)

/-- Subtracting the optimal compulsory profile removes the jump exactly. -/
theorem repaired_pair_equal (n a b j : ℝ) (hn : 1 < n)
    (hjump : b - a = j) :
    a - localLeft n j = b - localRight n j := by
  have h := localRight_sub_localLeft n j hn
  linarith

/-- The exact discrepancy created by using symmetric neighboring marks. -/
theorem symmetric_profile_correction (n j : ℝ) (hn : 1 < n) :
    pairEnergy n (localLeft n j + j / 2) (localRight n j - j / 2) =
      j ^ 2 * unitCorrection n := by
  have h0 : n ≠ 0 := by linarith
  have h1 : n - 1 ≠ 0 := by linarith
  have h2 : n + 1 ≠ 0 := by linarith
  have h3 : n ^ 2 - 1 ≠ 0 := by nlinarith [sq_nonneg (n - 1)]
  unfold pairEnergy localLeft localRight unitCorrection
  field_simp [h0, h1, h2, h3]
  ring

variable {ι : Type*}

/-- Weighted energy on a finite disjoint union of neighboring pairs. -/
def pairedEnergy (s : Finset ι) (n a b : ι → ℝ) : ℝ :=
  ∑ i ∈ s, pairEnergy (n i) (a i) (b i)

/-- The full compulsory local energy, with arbitrary signed prescribed jumps. -/
def localFloor (s : Finset ι) (n j : ι → ℝ) : ℝ :=
  ∑ i ∈ s, (j i) ^ 2 / (2 * (n i) ^ 2)

theorem pairedEnergy_pythagoras (s : Finset ι) (n a b j : ι → ℝ)
    (hn : ∀ i ∈ s, 1 < n i) (hjump : ∀ i ∈ s, b i - a i = j i) :
    pairedEnergy s n a b = localFloor s n j +
      pairedEnergy s n
        (fun i => a i - localLeft (n i) (j i))
        (fun i => b i - localRight (n i) (j i)) := by
  unfold pairedEnergy localFloor
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i hi =>
    pairEnergy_pythagoras (n i) (a i) (b i) (j i) (hn i hi) (hjump i hi)

/-- Legal columns have equal cumulative values across each compulsory pair. -/
theorem legal_residual_pythagoras
    (s : Finset ι) (n fL fR uL uR : ι → ℝ)
    (hn : ∀ i ∈ s, 1 < n i) (hu : ∀ i ∈ s, uR i = uL i) :
    pairedEnergy s n (fun i => fL i - uL i) (fun i => fR i - uR i) =
      localFloor s n (fun i => fR i - fL i) +
        pairedEnergy s n
          (fun i => (fL i - uL i) - localLeft (n i) (fR i - fL i))
          (fun i => (fR i - uR i) - localRight (n i) (fR i - fL i)) := by
  apply pairedEnergy_pythagoras s n _ _ _ hn
  intro i hi
  rw [hu i hi]
  ring

theorem finite_symmetric_correction (s : Finset ι) (n j : ι → ℝ)
    (hn : ∀ i ∈ s, 1 < n i) :
    pairedEnergy s n
      (fun i => localLeft (n i) (j i) + j i / 2)
      (fun i => localRight (n i) (j i) - j i / 2) =
      ∑ i ∈ s, (j i) ^ 2 * unitCorrection (n i) := by
  unfold pairedEnergy
  exact Finset.sum_congr rfl fun i hi =>
    symmetric_profile_correction (n i) (j i) (hn i hi)

/-- An elementary summable majorant, retaining the sharp cubic leading scale. -/
theorem unitCorrection_le_telescope (n : ℝ) (hn : 1 < n) :
    unitCorrection n ≤ (1 / 6 : ℝ) * (1 / (n - 1) ^ 3 - 1 / n ^ 3) := by
  have h0 : 0 < n := by linarith
  have h1 : 0 < n - 1 := by linarith
  have h2 : 0 < n + 1 := by linarith
  have h3 : 0 < n ^ 2 - 1 := by nlinarith [sq_nonneg (n - 1)]
  have h4 : 0 < 3 * n - 1 := by linarith
  have h5 : 0 < 2 * n - 1 := by linarith
  have hid :
      (1 / 6 : ℝ) * (1 / (n - 1) ^ 3 - 1 / n ^ 3) - unitCorrection n =
        (3 * n - 1) * (2 * n - 1) /
          (6 * n ^ 3 * (n - 1) ^ 3 * (n + 1)) := by
    unfold unitCorrection
    field_simp [ne_of_gt h0, ne_of_gt h1, ne_of_gt h2, ne_of_gt h3]
    ring
  have hnonneg : 0 ≤ (3 * n - 1) * (2 * n - 1) /
      (6 * n ^ 3 * (n - 1) ^ 3 * (n + 1)) := by positivity
  linarith

/-- A uniform finite correction estimate; no prime-counting input is needed. -/
theorem sum_unitCorrection_le (X : ℝ) (hX : 1 ≤ X) (N : ℕ) :
    (∑ k ∈ Finset.range N, unitCorrection (X + (k : ℝ) + 1)) ≤
      (1 / 6 : ℝ) * (1 / X ^ 3 - 1 / (X + (N : ℝ)) ^ 3) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
      have hc := unitCorrection_le_telescope (X + (N : ℝ) + 1) (by linarith)
      have he : X + (N : ℝ) + 1 - 1 = X + (N : ℝ) := by ring
      rw [he] at hc
      rw [Finset.sum_range_succ]
      calc
        _ ≤ (1 / 6 : ℝ) * (1 / X ^ 3 - 1 / (X + (N : ℝ)) ^ 3) +
            (1 / 6 : ℝ) *
              (1 / (X + (N : ℝ)) ^ 3 - 1 / (X + (N : ℝ) + 1) ^ 3) :=
          add_le_add ih hc
        _ = _ := by simp only [Nat.cast_add, Nat.cast_one]; ring

/-- Every finite terminal budget has the same `1/(6X³)` correction bound. -/
theorem sum_unitCorrection_le_cubic (X : ℝ) (hX : 1 ≤ X) (N : ℕ) :
    (∑ k ∈ Finset.range N, unitCorrection (X + (k : ℝ) + 1)) ≤
      1 / (6 * X ^ 3) := by
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hpos : 0 < X + (N : ℝ) := by linarith
  have hnonneg : 0 ≤ 1 / (X + (N : ℝ)) ^ 3 := by positivity
  calc
    _ ≤ (1 / 6 : ℝ) * (1 / X ^ 3 - 1 / (X + (N : ℝ)) ^ 3) :=
      sum_unitCorrection_le X hX N
    _ ≤ (1 / 6 : ℝ) * (1 / X ^ 3) := by linarith
    _ = _ := by ring

theorem unitCorrection_nonneg (n : ℝ) (hn : 1 < n) :
    0 ≤ unitCorrection n := by
  have h0 : 0 < n := by linarith
  have h1 : 0 < n ^ 2 - 1 := by nlinarith [sq_nonneg (n - 1)]
  unfold unitCorrection
  positivity

/-- The same uniform bound applies to any selected set of interior indices. -/
theorem sum_subset_unitCorrection_le_cubic (X : ℝ) (hX : 1 ≤ X)
    (N : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range N) :
    (∑ k ∈ S, unitCorrection (X + (k : ℝ) + 1)) ≤ 1 / (6 * X ^ 3) := by
  apply le_trans _ (sum_unitCorrection_le_cubic X hX N)
  apply Finset.sum_le_sum_of_subset_of_nonneg hS
  intro k _ _
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  exact unitCorrection_nonneg (X + (k : ℝ) + 1) (by linarith)

/-- Bounded signed marks cost no more than the unit-mark correction. -/
theorem sum_marked_subset_correction_le_cubic (X : ℝ) (hX : 1 ≤ X)
    (N : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range N) (j : ℕ → ℝ)
    (hj : ∀ k ∈ S, (j k) ^ 2 ≤ 1) :
    (∑ k ∈ S, (j k) ^ 2 * unitCorrection (X + (k : ℝ) + 1)) ≤
      1 / (6 * X ^ 3) := by
  apply le_trans _ (sum_subset_unitCorrection_le_cubic X hX N S hS)
  apply Finset.sum_le_sum
  intro k hk
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hc := unitCorrection_nonneg (X + (k : ℝ) + 1) (by linarith)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hj k hk) hc

end

end RiemannResearch.Analysis.AdjacentGreenPair
