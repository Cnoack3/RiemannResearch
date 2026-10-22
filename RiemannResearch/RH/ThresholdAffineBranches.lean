import Mathlib.Algebra.BigOperators.Field
import RiemannResearch.RH.ThresholdDilationAlgebra
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Concrete arithmetic branches in the two-seed affine calculus

Source: user-provided `RH_Two_Seed_Threshold.tex`, September 8, 2026,
Section 11.1--11.2. The reference supplies the branch maps and weighting.

This file proves the positive-index arithmetic behind the branch relations:
composition, injectivity, disjointness, the missing finite head, and the
exact normalization of the original Pareto branch weights. Every positive
integer scale remains available. It does not construct the Cuntz algebra,
prove its simplicity, or formalize the Hilbert--Schmidt limiting argument.
-/

open scoped BigOperators

namespace RiemannResearch.RH.Pareto

/-- The arithmetic map underlying the affine branch `S_{m,r}`. -/
def affineBranch (m r j : ℕ) : ℕ := m * j + r

theorem affineBranch_comp (m n r t j : ℕ) :
    affineBranch m r (affineBranch n t j) =
      affineBranch (m * n) (m * t + r) j := by
  unfold affineBranch
  ring

theorem affineBranch_one (j : ℕ) : affineBranch 1 0 j = j := by
  simp [affineBranch]

/-- The composed residue remains in the full set of `m*n` branches. -/
theorem affineBranch_comp_residue_lt {m n r t : ℕ} (hr : r < m) (ht : t < n) :
    m * t + r < m * n := by
  calc
    m * t + r < m * t + m := Nat.add_lt_add_left hr _
    _ = m * (t + 1) := by ring
    _ ≤ m * n := Nat.mul_le_mul_left m (by omega)

theorem affineBranch_injective {m : ℕ} (hm : 0 < m) (r : ℕ) :
    Function.Injective (affineBranch m r) := by
  intro j k h
  unfold affineBranch at h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hjk | hkj
  · have := Nat.mul_lt_mul_of_pos_left hjk hm
    omega
  · have := Nat.mul_lt_mul_of_pos_left hkj hm
    omega

theorem affineBranch_mod {m r : ℕ} (hr : r < m) (j : ℕ) :
    affineBranch m r j % m = r := by
  simp [affineBranch, Nat.add_mod, Nat.mod_eq_of_lt hr]

/-- Different residues give disjoint branch ranges before any completion. -/
theorem affineBranch_disjoint {m r t : ℕ} (hr : r < m) (ht : t < m)
    (hrt : r ≠ t) (j k : ℕ) : affineBranch m r j ≠ affineBranch m t k := by
  intro h
  have hmod := congrArg (fun x => x % m) h
  rw [affineBranch_mod hr, affineBranch_mod ht] at hmod
  exact hrt hmod

theorem affineBranch_positive {m j : ℕ} (hm : 0 < m) (hj : 0 < j) (r : ℕ) :
    0 < affineBranch m r j := by
  have := Nat.mul_pos hm hj
  unfold affineBranch
  omega

/-- On positive input indices, the union of branch ranges misses exactly
the coordinates `1,...,m-1` (and the auxiliary zero index). -/
theorem affineBranch_positive_partition {m k : ℕ} (hm : 0 < m) :
    (∃ r < m, ∃ j, 0 < j ∧ affineBranch m r j = k) ↔ m ≤ k := by
  constructor
  · rintro ⟨r, hr, j, hj, rfl⟩
    have hmul : m ≤ m * j := by
      simpa using Nat.mul_le_mul_left m (show 1 ≤ j by omega)
    unfold affineBranch
    omega
  · intro hmk
    refine ⟨k % m, Nat.mod_lt k hm, k / m, ?_, ?_⟩
    · have : 1 ≤ k / m := (Nat.le_div_iff_mul_le hm).mpr (by simpa using hmk)
      omega
    · simpa [affineBranch, Nat.add_comm, Nat.mul_comm] using Nat.mod_add_div k m

/-- Uniqueness is exact in both the residue and positive source index. -/
theorem affineBranch_unique {m r t j k : ℕ} (hr : r < m) (ht : t < m)
    (h : affineBranch m r j = affineBranch m t k) : r = t ∧ j = k := by
  have hrt : r = t := by
    have hmod := congrArg (fun x => x % m) h
    simpa only [affineBranch_mod hr, affineBranch_mod ht] using hmod
  refine ⟨hrt, ?_⟩
  subst t
  exact affineBranch_injective (by omega) r h

/-- Squared coefficient of the true weighted isometric dilation on a branch.
The index `j=0` is deliberately excluded from the normalization theorem. -/
noncomputable def affineBranchWeight (m r j : ℕ) : ℝ :=
  (m : ℝ) * positiveWeight (affineBranch m r j) / positiveWeight j

theorem affineBranchWeight_nonneg (m r j : ℕ) : 0 ≤ affineBranchWeight m r j := by
  unfold affineBranchWeight
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg m)
    (positiveWeight_nonneg _)) (positiveWeight_nonneg j)

/-- Exact finite normalization, using the original weight rather than Haar
weights. This is the diagonal content of `sum_r A_{m,r}^2 = I`. -/
theorem affineBranchWeight_sum (m j : ℕ) (hm : 0 < m) (hj : 0 < j) :
    (∑ r ∈ Finset.range m, affineBranchWeight m r j) = 1 := by
  have hb := positiveWeight_block m j hm hj
  rw [Finset.sum_Ico_eq_sum_range] at hb
  have hb' : (∑ r ∈ Finset.range m, positiveWeight (affineBranch m r j)) =
      positiveWeight j / m := by
    simpa [affineBranch, Nat.mul_add, Nat.add_sub_cancel_left] using hb
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hw0 : positiveWeight j ≠ 0 := by
    unfold positiveWeight
    positivity
  simp only [affineBranchWeight, ← Finset.sum_div, ← Finset.mul_sum]
  rw [hb']
  field_simp

/-- Actual nonnegative branch coefficient of the weighted dilation. -/
noncomputable def affineBranchCoefficient (m r j : ℕ) : ℝ :=
  Real.sqrt (affineBranchWeight m r j)

theorem affineBranchCoefficient_sq (m r j : ℕ) :
    affineBranchCoefficient m r j ^ 2 = affineBranchWeight m r j :=
  Real.sq_sqrt (affineBranchWeight_nonneg m r j)

/-- The weighted branch column is a unit vector at every positive input. -/
theorem affineBranchCoefficient_sq_sum (m j : ℕ) (hm : 0 < m) (hj : 0 < j) :
    (∑ r ∈ Finset.range m, affineBranchCoefficient m r j ^ 2) = 1 := by
  simp only [affineBranchCoefficient_sq]
  exact affineBranchWeight_sum m j hm hj

/-- Exact squared distance between the true weighted branch column and its
uniform affine comparison. This retains the complete mixed inner product. -/
theorem affineBranchCoefficient_uniform_defect (m j : ℕ) (hm : 0 < m)
    (hj : 0 < j) :
    (∑ r ∈ Finset.range m,
      (affineBranchCoefficient m r j - 1 / Real.sqrt m) ^ 2) =
      2 * (1 - (1 / Real.sqrt m) *
        ∑ r ∈ Finset.range m, affineBranchCoefficient m r j) := by
  have hsqrt2 : Real.sqrt (m : ℝ) ^ 2 = m := Real.sq_sqrt (Nat.cast_nonneg m)
  have hu : (m : ℝ) * (1 / Real.sqrt m) ^ 2 = 1 := by
    rw [div_pow, one_pow, hsqrt2]
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    field_simp
  calc
    _ = ∑ r ∈ Finset.range m, (affineBranchCoefficient m r j ^ 2 -
        (2 * (1 / Real.sqrt m)) * affineBranchCoefficient m r j +
        (1 / Real.sqrt m) ^ 2) := by
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ = (∑ r ∈ Finset.range m, affineBranchCoefficient m r j ^ 2) -
        2 * (1 / Real.sqrt m) *
          (∑ r ∈ Finset.range m, affineBranchCoefficient m r j) +
        (m : ℝ) * (1 / Real.sqrt m) ^ 2 := by
      simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = _ := by rw [affineBranchCoefficient_sq_sum m j hm hj, hu]; ring

end RiemannResearch.RH.Pareto
