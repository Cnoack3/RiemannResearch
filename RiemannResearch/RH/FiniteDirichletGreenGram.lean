/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.FiniteDirichletGreenEnergy

/-!
# Gram factorization of the finite Dirichlet Green matrix

This module polarizes the finite Dirichlet Green energy identity, realizes the
centered-slope map by an explicit rectangular matrix, and proves that the Green
matrix is the negative Gram matrix of that slope transform. All statements are
uniform in the dimension, including dimension zero.

Source: user-provided argument,
RH_Proof_First_Continuation_2026-09-04.md, Section 5. The source supports the
finite curvature-to-slope transform; the exact bilinear and Gram identities are
finite-algebra consequences of the previously verified coordinate chain. This
does not establish dyadic density, identify a Weil form, or prove RH.
-/

namespace RiemannResearch.RH.PrimeGapCurvature

noncomputable section

open scoped BigOperators

/-- The mixed Green bilinear form is the negative centered-slope inner
product. -/
theorem finiteDirichletGreenMatrix_bilinear_eq_neg_slopeInner
    (n : ℕ) (c d : Fin n → ℝ) :
    (∑ r, c r * (finiteDirichletGreenMatrix n).mulVec d r) =
      -(∑ j,
        centeredSlopePrefixLinearMap n c j *
        centeredSlopePrefixLinearMap n d j) := by
  let s : Fin (n + 1) → ℝ := centeredSlopePrefixLinearMap n c
  let z : Fin (n + 2) → ℝ := centeredProfileSectionLinearMap n d
  have hdiff (j : Fin (n + 1)) :
      z j.succ - z j.castSucc =
        centeredSlopePrefixLinearMap n d j := by
    change
      slopeProfilePrefix (centeredSlopePrefixLinearMap n d) j.succ -
          slopeProfilePrefix (centeredSlopePrefixLinearMap n d) j.castSucc =
        centeredSlopePrefixLinearMap n d j
    exact slopeProfilePrefix_succ_sub
      (centeredSlopePrefixLinearMap n d) j
  calc
    (∑ r, c r * (finiteDirichletGreenMatrix n).mulVec d r) =
        ∑ r : Fin n,
          (s r.succ - s r.castSucc) * z r.succ.castSucc := by
      apply Finset.sum_congr rfl
      intro r _
      rw [finiteDirichletGreenMatrix_mulVec]
      change c r * z r.succ.castSucc =
        (s r.succ - s r.castSucc) * z r.succ.castSucc
      rw [show s r.succ - s r.castSucc = c r by
        exact finiteSlopeDifference_centeredSlopePrefix_apply n c r]
    _ = -(∑ j : Fin (n + 1),
          s j * (z j.succ - z j.castSucc)) -
          s 0 * z 0 +
          s (Fin.last n) * z (Fin.last (n + 1)) :=
      finiteSlopeProfile_summation_by_parts n s z
    _ = -(∑ j,
          centeredSlopePrefixLinearMap n c j *
          centeredSlopePrefixLinearMap n d j) := by
      simp_rw [hdiff]
      simp only [z, centeredProfileSection_zero,
        centeredProfileSection_last, mul_zero, sub_zero, add_zero]
      simp only [s]

/-- The matrix whose columns are the centered slopes of the standard
curvature vectors. -/
def finiteCenteredSlopeMatrix (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin n) ℝ :=
  fun j i =>
    centeredSlopePrefixLinearMap n (finStandardBasis n i) j

/-- Matrix multiplication by the slope matrix is exactly the centered-prefix
linear map. -/
theorem finiteCenteredSlopeMatrix_mulVec
    (n : ℕ) (c : Fin n → ℝ) :
    (finiteCenteredSlopeMatrix n).mulVec c =
      centeredSlopePrefixLinearMap n c := by
  have hdecomp : (∑ i, c i • finStandardBasis n i) = c := by
    funext r
    simp [finStandardBasis, Pi.smul_apply, smul_eq_mul]
  funext j
  calc
    (finiteCenteredSlopeMatrix n).mulVec c j =
        ∑ i, c i *
          centeredSlopePrefixLinearMap n (finStandardBasis n i) j := by
      rw [Matrix.mulVec_apply_eq_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [finiteCenteredSlopeMatrix]
      ring
    _ = centeredSlopePrefixLinearMap n
          (∑ i, c i • finStandardBasis n i) j := by
      simp only [map_sum, Finset.sum_apply, map_smul,
        Pi.smul_apply, smul_eq_mul]
    _ = centeredSlopePrefixLinearMap n c j := by
      rw [hdecomp]

/-- The finite Dirichlet Green matrix is the negative Gram matrix of the
centered-slope transform. -/
theorem finiteDirichletGreenMatrix_eq_neg_gram (n : ℕ) :
    finiteDirichletGreenMatrix n =
      -((finiteCenteredSlopeMatrix n).transpose *
        finiteCenteredSlopeMatrix n) := by
  ext r i
  have h :=
    finiteDirichletGreenMatrix_bilinear_eq_neg_slopeInner n
      (finStandardBasis n r) (finStandardBasis n i)
  simpa [Matrix.mul_apply, Matrix.mulVec_apply_eq_sum,
    finiteCenteredSlopeMatrix, finStandardBasis] using h

end

end RiemannResearch.RH.PrimeGapCurvature
