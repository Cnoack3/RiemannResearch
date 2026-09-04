/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.FiniteSlopeCompression

/-!
# Entries of the finite centered slope matrix

This module evaluates the centered curvature-to-slope matrix on the standard
curvature basis. Its two branches exhibit the exact normalization and the
rank-one centering correction, uniformly in the finite dimension.

Source: user-provided argument,
RH_Proof_First_Continuation_2026-09-04.md, Section 5. The source supports the
finite curvature-to-slope coordinates. This module does not define a concrete
Weil kernel, establish positivity or density, or prove RH.
-/

namespace RiemannResearch.RH.PrimeGapCurvature

noncomputable section

open scoped BigOperators

/-- The prefix slope of a standard curvature vector is its step function. -/
lemma slopePrefix_finStandardBasis
    (n : ℕ) (i : Fin n) (j : Fin (n + 1)) :
    slopePrefix (finStandardBasis n i) j =
      if i.val < j.val then 1 else 0 := by
  classical
  unfold slopePrefix
  by_cases hij : i.val < j.val
  · rw [if_pos hij]
    rw [Finset.sum_eq_single i.val]
    · simp [finiteCurvatureGet, finStandardBasis, i.isLt]
    · intro b hb hbi
      by_cases hbn : b < n
      · have hfin : (⟨b, hbn⟩ : Fin n) ≠ i := by
          intro heq
          apply hbi
          simpa using congrArg Fin.val heq
        simp [finiteCurvatureGet, hbn, finStandardBasis, hfin]
      · simp [finiteCurvatureGet, hbn]
    · simp only [Finset.mem_range]
      omega
  · rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro b hb
    have hbj : b < j.val := Finset.mem_range.mp hb
    have hji : j.val ≤ i.val := Nat.le_of_not_gt hij
    have hbn : b < n := by omega
    have hbi : b ≠ i.val := by omega
    simp [finiteCurvatureGet, hbn, finStandardBasis, Fin.ext_iff, hbi]

/-- The total of the standard-basis prefix slope is the number of its
post-curvature coordinates. -/
lemma sum_slopePrefix_finStandardBasis
    (n : ℕ) (i : Fin n) :
    (∑ j : Fin (n + 1), slopePrefix (finStandardBasis n i) j) =
      ((n - i.val : ℕ) : ℝ) := by
  classical
  calc
    (∑ j : Fin (n + 1), slopePrefix (finStandardBasis n i) j) =
        ∑ j : Fin (n + 1), if i.val < j.val then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [slopePrefix_finStandardBasis]
    _ = ∑ k ∈ Finset.range (n + 1),
        if i.val < k then (1 : ℝ) else 0 := by
      exact Fin.sum_univ_eq_sum_range
        (fun k => if i.val < k then (1 : ℝ) else 0) (n + 1)
    _ = (({k ∈ Finset.range (n + 1) | i.val < k}.card : ℕ) : ℝ) := by
      rw [Finset.sum_boole]
    _ = ((n - i.val : ℕ) : ℝ) := by
      congr 1
      have hfilter :
          {k ∈ Finset.range (n + 1) | i.val < k} =
            Finset.Ico (i.val + 1) (n + 1) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        omega
      rw [hfilter, Nat.card_Ico]
      omega

/-- The centered slope matrix has a constant negative branch through its
curvature coordinate and a constant positive branch after it. -/
theorem finiteCenteredSlopeMatrix_apply
    (n : ℕ) (j : Fin (n + 1)) (i : Fin n) :
    finiteCenteredSlopeMatrix n j i =
      if j.val ≤ i.val then
        -((n - i.val : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)
      else
        ((i.val + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) := by
  classical
  simp only [finiteCenteredSlopeMatrix, centeredSlopePrefixLinearMap_apply,
    centeredSlopePrefix]
  rw [slopePrefix_finStandardBasis, sum_slopePrefix_finStandardBasis]
  by_cases hji : j.val ≤ i.val
  · simp only [if_pos hji]
    have hij : ¬ i.val < j.val := by omega
    simp only [if_neg hij]
    ring
  · simp only [if_neg hji]
    have hij : i.val < j.val := by omega
    rw [if_pos hij]
    have hi : i.val ≤ n := Nat.le_of_lt i.isLt
    push_cast [Nat.cast_sub hi]
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hn]
    ring

/-- The negative branch of the centered slope matrix. -/
theorem finiteCenteredSlopeMatrix_apply_of_le
    (n : ℕ) (j : Fin (n + 1)) (i : Fin n)
    (hji : j.val ≤ i.val) :
    finiteCenteredSlopeMatrix n j i =
      -((n - i.val : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) := by
  rw [finiteCenteredSlopeMatrix_apply, if_pos hji]

/-- The positive branch of the centered slope matrix. -/
theorem finiteCenteredSlopeMatrix_apply_of_lt
    (n : ℕ) (j : Fin (n + 1)) (i : Fin n)
    (hij : i.val < j.val) :
    finiteCenteredSlopeMatrix n j i =
      ((i.val + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) := by
  rw [finiteCenteredSlopeMatrix_apply]
  rw [if_neg (by omega)]

end

end RiemannResearch.RH.PrimeGapCurvature
