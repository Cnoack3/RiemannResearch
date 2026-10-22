/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.FiniteDirichletGreenGram
import Mathlib.LinearAlgebra.Basis.Cardinality

/-!
# Finite slope-kernel compression

This module pulls an arbitrary real finite slope-space kernel back through the
centered curvature-to-slope transform. It proves the exact mixed bilinear
identity and preservation of symmetry, uniformly including dimension zero.
It also proves exact congruence under any zero-sum slope family and equivalence
of quadratic-form nonnegativity in curvature and any full slope basis.
No nonnegativity hypothesis for a concrete kernel is discharged.

Source: user-provided argument,
RH_Proof_First_Continuation_2026-09-04.md, Section 5. The source supports the
finite curvature-to-slope congruence. This module does not identify the kernel
with a Weil form, assert positivity for an arithmetic kernel, establish density,
or prove RH.
-/

namespace RiemannResearch.RH.PrimeGapCurvature

noncomputable section

open scoped BigOperators

/-- Pull back a slope-space kernel along the centered curvature-to-slope
matrix. -/
def finiteSlopeCompression
    (n : ℕ)
    (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (finiteCenteredSlopeMatrix n).transpose *
    K * finiteCenteredSlopeMatrix n

/-- The mixed bilinear form of the compressed kernel is the mixed bilinear
form of the slope-space kernel evaluated on the centered slopes. -/
theorem finiteSlopeCompression_bilinear
    (n : ℕ)
    (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (c d : Fin n → ℝ) :
    (∑ r, c r * (finiteSlopeCompression n K).mulVec d r) =
      ∑ j, centeredSlopePrefixLinearMap n c j *
        (K.mulVec (centeredSlopePrefixLinearMap n d)) j := by
  change dotProduct c ((finiteSlopeCompression n K).mulVec d) =
    dotProduct (centeredSlopePrefixLinearMap n c)
      (K.mulVec (centeredSlopePrefixLinearMap n d))
  simp only [finiteSlopeCompression]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
  rw [finiteCenteredSlopeMatrix_mulVec, finiteCenteredSlopeMatrix_mulVec]

/-- Symmetry of a slope-space kernel is preserved by finite slope
compression. -/
theorem finiteSlopeCompression_symm
    (n : ℕ)
    {K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hK : K.IsSymm) :
    (finiteSlopeCompression n K).IsSymm := by
  change (finiteSlopeCompression n K).transpose = finiteSlopeCompression n K
  simp [finiteSlopeCompression, hK.eq, Matrix.mul_assoc]

variable {ι : Type*}

def finiteSlopeFamilyMatrix (n : ℕ) (s : ι → meanZeroSlopeSubmodule n) :
    Matrix (Fin (n + 1)) ι ℝ := fun j i => (s i).val j

def finiteCurvatureFamilyMatrix (n : ℕ) (s : ι → meanZeroSlopeSubmodule n) :
    Matrix (Fin n) ι ℝ := fun r i => finiteSlopeDifferenceMap n (s i).val r

theorem finiteCenteredSlopeMatrix_mul_curvatureFamily
    (n : ℕ) (s : ι → meanZeroSlopeSubmodule n) :
    finiteCenteredSlopeMatrix n * finiteCurvatureFamilyMatrix n s =
      finiteSlopeFamilyMatrix n s := by
  ext j i
  change (finiteCenteredSlopeMatrix n).mulVec
    (finiteSlopeDifferenceMap n (s i).val) j = (s i).val j
  rw [finiteCenteredSlopeMatrix_mulVec]
  have hs : finiteSlopeSumMap n (s i).val = 0 := (LinearMap.mem_ker).mp (s i).property
  rw [centeredSlopePrefix_difference_of_sum_eq_zero n (s i).val hs]

theorem finiteSlopeCompression_family_congruence
    (n : ℕ) (s : ι → meanZeroSlopeSubmodule n)
    (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (finiteCurvatureFamilyMatrix n s).transpose *
      finiteSlopeCompression n K * finiteCurvatureFamilyMatrix n s =
    (finiteSlopeFamilyMatrix n s).transpose * K * finiteSlopeFamilyMatrix n s := by
  unfold finiteSlopeCompression
  have h := finiteCenteredSlopeMatrix_mul_curvatureFamily n s
  calc
    _ = (finiteCenteredSlopeMatrix n * finiteCurvatureFamilyMatrix n s).transpose *
        K * (finiteCenteredSlopeMatrix n * finiteCurvatureFamilyMatrix n s) := by
      simp only [Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [h]

theorem finiteSlopeCompression_nonneg_iff_meanZero
    (n : ℕ) (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (∀ c : Fin n → ℝ, 0 ≤ ∑ r, c r * (finiteSlopeCompression n K).mulVec c r) ↔
    (∀ s : meanZeroSlopeSubmodule n, 0 ≤ ∑ j, s.val j * (K.mulVec s.val) j) := by
  constructor
  · intro h s
    have hc := h ((curvatureMeanZeroSlopeEquiv n).symm s)
    rw [finiteSlopeCompression_bilinear] at hc
    have he : centeredSlopePrefixLinearMap n ((curvatureMeanZeroSlopeEquiv n).symm s) =
        s.val := by
      exact congrArg Subtype.val ((curvatureMeanZeroSlopeEquiv n).apply_symm_apply s)
    simpa only [he] using hc
  · intro h c
    rw [finiteSlopeCompression_bilinear]
    exact h (curvatureMeanZeroSlopeEquiv n c)


theorem finiteSlopeFamilyMatrix_mulVec_basis [Fintype ι]
    (n : ℕ) (b : Module.Basis ι ℝ (meanZeroSlopeSubmodule n)) (a : ι → ℝ) :
    (finiteSlopeFamilyMatrix n b).mulVec a = (b.equivFun.symm a).val := by
  rw [b.equivFun_symm_apply]
  ext j
  simp [finiteSlopeFamilyMatrix, Matrix.mulVec, dotProduct, Finset.sum_apply,
    smul_eq_mul, mul_comm]

theorem finiteSlopeFamilyMatrix_bilinear [Fintype ι]
    (n : ℕ) (s : ι → meanZeroSlopeSubmodule n)
    (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (a b : ι → ℝ) :
    dotProduct a (((finiteSlopeFamilyMatrix n s).transpose * K *
      finiteSlopeFamilyMatrix n s).mulVec b) =
    dotProduct ((finiteSlopeFamilyMatrix n s).mulVec a)
      (K.mulVec ((finiteSlopeFamilyMatrix n s).mulVec b)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

theorem finiteSlopeCompression_nonneg_iff_basis [Fintype ι]
    (n : ℕ) (b : Module.Basis ι ℝ (meanZeroSlopeSubmodule n))
    (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (∀ c : Fin n → ℝ, 0 ≤ dotProduct c ((finiteSlopeCompression n K).mulVec c)) ↔
    (∀ a : ι → ℝ, 0 ≤ dotProduct a
      (((finiteSlopeFamilyMatrix n b).transpose * K *
        finiteSlopeFamilyMatrix n b).mulVec a)) := by
  change (∀ c : Fin n → ℝ, 0 ≤ ∑ r, c r * (finiteSlopeCompression n K).mulVec c r) ↔ _
  rw [finiteSlopeCompression_nonneg_iff_meanZero]
  constructor
  · intro h a
    rw [finiteSlopeFamilyMatrix_bilinear, finiteSlopeFamilyMatrix_mulVec_basis]
    exact h (b.equivFun.symm a)
  · intro h s
    have ha := h (b.equivFun s)
    rw [finiteSlopeFamilyMatrix_bilinear, finiteSlopeFamilyMatrix_mulVec_basis,
      b.equivFun.symm_apply_apply] at ha
    exact ha


end

end RiemannResearch.RH.PrimeGapCurvature
