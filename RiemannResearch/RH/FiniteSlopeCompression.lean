/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.FiniteDirichletGreenGram

/-!
# Finite slope-kernel compression

This module pulls an arbitrary real finite slope-space kernel back through the
centered curvature-to-slope transform. It proves the exact mixed bilinear
identity and preservation of symmetry, uniformly including dimension zero.

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

end

end RiemannResearch.RH.PrimeGapCurvature
