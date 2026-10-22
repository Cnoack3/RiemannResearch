import RiemannResearch.LinearAlgebra.FiniteConstrainedMatrixMinimum

/-!
# Literal matrix-inverse notation for the constrained minimum

Source: `ArithmeticVariationalProof.md`, Section 6. This identifies the
constructed inverse equivalences with Mathlib's actual matrix inverses.
-/

noncomputable section
namespace RiemannResearch.LinearAlgebra.FiniteConstrainedMatrix
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem gramEquiv_symm_eq_inv_mulVec (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (b : ι → ℝ) : (gramEquiv G hG).symm b = G⁻¹.mulVec b := by
  apply (gramEquiv G hG).injective
  rw [LinearEquiv.apply_symm_apply]
  change b = G.mulVec (G⁻¹.mulVec b)
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G
    ((Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit), Matrix.one_mulVec]

theorem compressedMap_eq_matrix_mulVec (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (A : Matrix κ ι ℝ) (x : κ → ℝ) :
    compressedMap G hG A x = (A * G⁻¹ * A.transpose).mulVec x := by
  change A.mulVec ((gramEquiv G hG).symm (A.transpose.mulVec x)) = _
  rw [gramEquiv_symm_eq_inv_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

theorem compressedMatrix_posDef (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (A : Matrix κ ι ℝ) (hA : Function.Surjective A.mulVec) :
    (A * G⁻¹ * A.transpose).PosDef := by
  have hp := hG.inv.conjTranspose_mul_mul_same
    (transpose_mulVec_injective_of_surjective A hA)
  have ht : A.transpose.conjTranspose = A := by ext i j; rfl
  rw [ht] at hp
  exact hp

theorem multiplier_eq_inverse_matrix (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (A : Matrix κ ι ℝ) (hA : Function.Surjective A.mulVec) (b : κ → ℝ) :
    multiplier G hG A hA b = (A * G⁻¹ * A.transpose)⁻¹.mulVec b := by
  apply (compressedEquiv G hG A hA).injective
  change (compressedEquiv G hG A hA) ((compressedEquiv G hG A hA).symm b) = _
  rw [LinearEquiv.apply_symm_apply]
  change b = compressedMap G hG A ((A * G⁻¹ * A.transpose)⁻¹.mulVec b)
  rw [compressedMap_eq_matrix_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv (A * G⁻¹ * A.transpose)
      ((Matrix.isUnit_iff_isUnit_det _).mp (compressedMatrix_posDef G hG A hA).isUnit),
    Matrix.one_mulVec]

theorem minimumCoefficients_eq_inverse_matrix (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (A : Matrix κ ι ℝ) (hA : Function.Surjective A.mulVec) (b : κ → ℝ) :
    minimumCoefficients G hG A hA b =
      (G⁻¹ * A.transpose * (A * G⁻¹ * A.transpose)⁻¹).mulVec b := by
  rw [minimumCoefficients, gramEquiv_symm_eq_inv_mulVec, multiplier_eq_inverse_matrix,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem inverseMatrix_isLeast (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (A : Matrix κ ι ℝ) (hA : Function.Surjective A.mulVec) (b : κ → ℝ) :
    IsLeast {E : ℝ | ∃ c : ι → ℝ, A.mulVec c = b ∧ dotProduct c (G.mulVec c) = E}
      (dotProduct b ((A * G⁻¹ * A.transpose)⁻¹.mulVec b)) := by
  simpa only [multiplier_eq_inverse_matrix] using inverseCompressed_isLeast G hG A hA b

end RiemannResearch.LinearAlgebra.FiniteConstrainedMatrix
