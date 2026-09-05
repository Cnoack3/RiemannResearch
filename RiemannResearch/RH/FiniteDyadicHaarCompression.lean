/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.FiniteDyadicHaarBasis
import RiemannResearch.RH.FiniteSlopeCompression

/-!
# Exact Haar conjugation of finite slope-kernel compressions

K has literal index Fin (2 ^ m). This module constructs H from the actual Haar
atoms and proves Cᵀ (Tᵀ K T) C = Hᵀ K H, after the explicit dimension cast,
where C consists of adjacent differences of the atoms. The full basis
theorem makes nonnegativity in the two coordinate systems equivalent.

Source: user-provided argument, RH_Proof_First_Continuation_2026-09-04.md,
Section 5, and the dyadic/Haar continuation queue in canonical handoff v14.
The source supports the congruence strategy. The result is an exact finite
coordinate theorem for an arbitrary real K. It does not construct the
completed arithmetic Weil kernel or discharge its positivity.
-/

namespace RiemannResearch.RH.PrimeGapCurvature

noncomputable section

open scoped BigOperators


/-- Interpret a literal dyadic kernel on the dimension-cast slope index. -/
def finiteDyadicCastSlopeKernel (m : ℕ)
    (K : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℝ) :
    Matrix (Fin (2 ^ m - 1 + 1)) (Fin (2 ^ m - 1 + 1)) ℝ :=
  fun j k => K (Fin.cast (dyadicDimension_eq m) j) (Fin.cast (dyadicDimension_eq m) k)

/-- The unnormalized Haar atoms as columns on the literal dyadic grid. -/
def finiteDyadicHaarMatrix (m : ℕ) :
    Matrix (Fin (2 ^ m)) (FiniteDyadicHaarIndex m) ℝ :=
  fun j i => finiteDyadicHaarAtom m i.1.val i.2 j

/-- The literal finite slope kernel in dyadic Haar coordinates. -/
def finiteDyadicHaarCompression (m : ℕ)
    (K : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℝ) :
    Matrix (FiniteDyadicHaarIndex m) (FiniteDyadicHaarIndex m) ℝ :=
  (finiteDyadicHaarMatrix m).transpose * K * finiteDyadicHaarMatrix m

theorem finiteDyadicCastSlopeKernel_mulVec (m : ℕ)
    (K : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℝ) (v : Fin (2 ^ m) → ℝ)
    (j : Fin (2 ^ m - 1 + 1)) :
    (finiteDyadicCastSlopeKernel m K).mulVec
      (fun k => v (Fin.cast (dyadicDimension_eq m) k)) j =
    (K.mulVec v) (Fin.cast (dyadicDimension_eq m) j) := by
  change (∑ k : Fin (2 ^ m - 1 + 1),
    K (Fin.cast (dyadicDimension_eq m) j) (Fin.cast (dyadicDimension_eq m) k) *
      v (Fin.cast (dyadicDimension_eq m) k)) =
    ∑ k : Fin (2 ^ m), K (Fin.cast (dyadicDimension_eq m) j) k * v k
  exact (Fin.castOrderIso (dyadicDimension_eq m)).toEquiv.sum_comp
    (fun k => K (Fin.cast (dyadicDimension_eq m) j) k * v k)

theorem finiteDyadicHaarCompression_apply (m : ℕ)
    (K : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℝ) (i k : FiniteDyadicHaarIndex m) :
    finiteDyadicHaarCompression m K i k =
    ∑ j, finiteDyadicHaarAtom m i.1.val i.2 j *
      (K.mulVec (finiteDyadicHaarAtom m k.1.val k.2)) j := by
  change (((finiteDyadicHaarMatrix m).transpose * K).mulVec
    (finiteDyadicHaarAtom m k.1.val k.2)) i = _
  rw [← Matrix.mulVec_mulVec]
  rfl

theorem finiteDyadicHaarFamilyGram_eq_literal (m : ℕ)
    (K : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℝ) :
    (finiteSlopeFamilyMatrix (2 ^ m - 1) (finiteDyadicHaarSlope m)).transpose *
      finiteDyadicCastSlopeKernel m K *
        finiteSlopeFamilyMatrix (2 ^ m - 1) (finiteDyadicHaarSlope m) =
      finiteDyadicHaarCompression m K := by
  ext i k
  change (((finiteSlopeFamilyMatrix (2 ^ m - 1) (finiteDyadicHaarSlope m)).transpose *
      finiteDyadicCastSlopeKernel m K).mulVec
        (finiteDyadicHaarSlope m k).val) i = _
  rw [← Matrix.mulVec_mulVec]
  change (∑ j : Fin (2 ^ m - 1 + 1),
    finiteDyadicHaarAtom m i.1.val i.2 (Fin.cast (dyadicDimension_eq m) j) *
      ((finiteDyadicCastSlopeKernel m K).mulVec
        (fun t => finiteDyadicHaarAtom m k.1.val k.2
          (Fin.cast (dyadicDimension_eq m) t))) j) = _
  simp_rw [finiteDyadicCastSlopeKernel_mulVec]
  rw [finiteDyadicHaarCompression_apply]
  exact (Fin.castOrderIso (dyadicDimension_eq m)).toEquiv.sum_comp
    (fun j => finiteDyadicHaarAtom m i.1.val i.2 j *
      (K.mulVec (finiteDyadicHaarAtom m k.1.val k.2)) j)

theorem finiteDyadicHaarCompression_curvature_congruence (m : ℕ)
    (K : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℝ) :
    (finiteCurvatureFamilyMatrix (2 ^ m - 1) (finiteDyadicHaarSlope m)).transpose *
      finiteSlopeCompression (2 ^ m - 1) (finiteDyadicCastSlopeKernel m K) *
        finiteCurvatureFamilyMatrix (2 ^ m - 1) (finiteDyadicHaarSlope m) =
      finiteDyadicHaarCompression m K := by
  rw [finiteSlopeCompression_family_congruence, finiteDyadicHaarFamilyGram_eq_literal]

theorem finiteDyadicHaarCompression_nonneg_iff (m : ℕ)
    (K : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℝ) :
    (∀ c : Fin (2 ^ m - 1) → ℝ,
      0 ≤ dotProduct c ((finiteSlopeCompression (2 ^ m - 1)
        (finiteDyadicCastSlopeKernel m K)).mulVec c)) ↔
    (∀ a : FiniteDyadicHaarIndex m → ℝ,
      0 ≤ dotProduct a ((finiteDyadicHaarCompression m K).mulVec a)) := by
  have h := finiteSlopeCompression_nonneg_iff_basis (2 ^ m - 1)
    (finiteDyadicHaarBasis m) (finiteDyadicCastSlopeKernel m K)
  have he : (finiteDyadicHaarBasis m : FiniteDyadicHaarIndex m →
      meanZeroSlopeSubmodule (2 ^ m - 1)) = finiteDyadicHaarSlope m := by
    funext i
    exact finiteDyadicHaarBasis_apply m i
  rw [he, finiteDyadicHaarFamilyGram_eq_literal] at h
  exact h

theorem finiteDyadicHaarCompression_symm (m : ℕ)
    {K : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℝ} (hK : K.IsSymm) :
    (finiteDyadicHaarCompression m K).IsSymm := by
  change (finiteDyadicHaarCompression m K).transpose = finiteDyadicHaarCompression m K
  simp [finiteDyadicHaarCompression, hK.eq, Matrix.mul_assoc]


end

end RiemannResearch.RH.PrimeGapCurvature
