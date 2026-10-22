import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# Signed finite quadratic completion
Source: user-provided Conditional_IID_Cesaro_Mathematical_Completion_2026-09-17.md,
Section 11. Exact matrix algebra for its concrete Cesaro-tail application.
Inverse existence is not asserted by the completion lemma.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteSignedQuadratic
def quadratic {D : ℕ} (T : Matrix (Fin D) (Fin D) ℝ) (c : Fin D → ℝ) : ℝ :=
  ∑ d, ∑ e, c d * T d e * c e


def correctionMatrix {D r : ℕ} (T : Matrix (Fin D) (Fin D) ℝ)
    (N : Matrix (Fin D) (Fin r) ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  N.transpose * T * N


def correlation {D r : ℕ} (T : Matrix (Fin D) (Fin D) ℝ)
    (N : Matrix (Fin D) (Fin r) ℝ) (c : Fin D → ℝ) : Fin r → ℝ :=
  N.transpose.mulVec (T.mulVec c)


theorem quadratic_add {D : ℕ} (T : Matrix (Fin D) (Fin D) ℝ)
    (hT : ∀ i j, T i j = T j i) (c z : Fin D → ℝ) :
    quadratic T (c + z) = quadratic T c +
      2 * (∑ i, ∑ j, z i * T i j * c j) + quadratic T z := by
  have hc : (∑ i, ∑ j, c i * T i j * z j) = ∑ i, ∑ j, z i * T i j * c j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hT j i]
    ring
  unfold quadratic
  simp only [Pi.add_apply]
  simp_rw [show ∀ i j, (c i + z i) * T i j * (c j + z j) =
    c i * T i j * c j + c i * T i j * z j +
      z i * T i j * c j + z i * T i j * z j by intros; ring]
  simp only [Finset.sum_add_distrib]
  rw [hc]
  ring


/-- Exact signed Schur square completion for an invertible correction Gram.
All assumptions are finite algebra: symmetry and the displayed normal equation. -/
theorem schur_completion {r : ℕ} (S : Matrix (Fin r) (Fin r) ℝ)
    (hS : ∀ i j, S i j = S j i) (h x z : Fin r → ℝ)
    (hx : S.mulVec x = h) (a : ℝ) :
    a + 2 * (∑ i, z i * h i) + quadratic S z =
      a - (∑ i, x i * h i) + quadratic S (z + x) := by
  have hcross (v : Fin r → ℝ) :
      (∑ i, ∑ j, v i * S i j * x j) = ∑ i, v i * h i := by
    apply Finset.sum_congr rfl
    intro i _
    have hn := congrFun hx i
    change (∑ j, S i j * x j) = h i at hn
    rw [← hn, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hq : quadratic S x = ∑ i, x i * h i := hcross x
  have hc := quadratic_add S hS x z
  rw [hcross z, hq, add_comm x z] at hc
  linarith


/-- A genuine two-sided inverse supplies the normal equation; no inverse is
silently assumed to exist for a singular matrix. -/
theorem schur_completion_of_inverse {r : ℕ}
    (S B : Matrix (Fin r) (Fin r) ℝ)
    (hS : ∀ i j, S i j = S j i) (hSB : S * B = 1)
    (h z : Fin r → ℝ) (a : ℝ) :
    a + 2 * (∑ i, z i * h i) + quadratic S z =
      a - (∑ i, B.mulVec h i * h i) + quadratic S (z + B.mulVec h) := by
  apply schur_completion S hS h (B.mulVec h) z
  rw [Matrix.mulVec_mulVec, hSB, Matrix.one_mulVec]



theorem quadratic_mulVec {D : ℕ} (T : Matrix (Fin D) (Fin D) ℝ) (c : Fin D → ℝ) :
    quadratic T c = ∑ i, c i * T.mulVec c i := by
  unfold quadratic Matrix.mulVec dotProduct
  simp only [Finset.mul_sum, mul_assoc]


theorem transpose_pairing {D r : ℕ} (N : Matrix (Fin D) (Fin r) ℝ)
    (z : Fin r → ℝ) (v : Fin D → ℝ) :
    (∑ i, N.mulVec z i * v i) = ∑ j, z j * N.transpose.mulVec v j := by
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum,
    Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring


theorem correction_quadratic {D r : ℕ} (T : Matrix (Fin D) (Fin D) ℝ)
    (N : Matrix (Fin D) (Fin r) ℝ) (z : Fin r → ℝ) :
    quadratic T (N.mulVec z) = quadratic (correctionMatrix T N) z := by
  rw [quadratic_mulVec, transpose_pairing, quadratic_mulVec]
  simp only [correctionMatrix, Matrix.mulVec_mulVec, Matrix.mul_assoc]

end RiemannResearch.Analysis.FiniteSignedQuadratic
