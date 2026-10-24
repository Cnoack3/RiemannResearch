import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Exact inverse Cauchy capacity product

Source: user-requested third Ramanujan development, 23 October 2026.
The finite product strategy is motivated by J.-F. Burnol,
https://arxiv.org/abs/math/9910055. The result here is a finite exact
matrix identity and its complete Ramanujan remainder, not an infinite
Hardy-space factorization assertion.
-/

noncomputable section
open scoped BigOperators Matrix
namespace RiemannResearch.LinearAlgebra.CauchyProduct
variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

theorem det_sub_outer (A : Matrix ι ι K) (hA : IsUnit A.det) (u v : ι → K) :
    (A - Matrix.vecMulVec u v).det = A.det * (1 - v ⬝ᵥ (A⁻¹ *ᵥ u)) := by
  have hout : Matrix.replicateCol Unit (-u) * Matrix.replicateRow Unit v =
      -Matrix.vecMulVec u v := by
    ext i j
    simp [Matrix.mul_apply, Matrix.replicateCol, Matrix.replicateRow, Matrix.vecMulVec]
  have h := Matrix.det_add_replicateCol_mul_replicateRow (ι := Unit) hA (-u) v
  rw [hout, ← sub_eq_add_neg, Matrix.det_unique (n := Unit)] at h
  convert h using 2
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply,
    Matrix.replicateRow_apply, Matrix.replicateCol_apply, Pi.neg_apply,
    Finset.sum_mul, Matrix.mulVec, dotProduct, mul_neg, Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  simp only [sub_eq_add_neg, Finset.mul_sum, mul_assoc]

def cauchy (x y : ι → K) : Matrix ι ι K := fun i j => 1 / (x i + y j - 1)

theorem cauchy_sub_outer (x y : ι → K)
    (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0)
    (hxy : ∀ i j, x i + y j - 1 ≠ 0) :
    cauchy x y - Matrix.vecMulVec (fun i => 1 / x i) (fun j => 1 / y j) =
      Matrix.diagonal (fun i => (x i - 1) / x i) * cauchy x y *
        Matrix.diagonal (fun j => (y j - 1) / y j) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.vecMulVec, Matrix.of_apply, Matrix.diagonal_mul,
    Matrix.mul_diagonal, cauchy]
  field_simp [hx i, hy j, hxy i j]
  <;> ring

/-- Every mixed inverse source value has the exact finite product. -/
theorem cauchy_inverse_pairing_product (x y : ι → K)
    (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0)
    (hxy : ∀ i j, x i + y j - 1 ≠ 0)
    (hdet : (cauchy x y).det ≠ 0) :
    (fun j => 1 / y j) ⬝ᵥ ((cauchy x y)⁻¹ *ᵥ (fun i => 1 / x i)) =
      1 - (∏ i, (x i - 1) / x i) * (∏ j, (y j - 1) / y j) := by
  have h := congrArg Matrix.det (cauchy_sub_outer x y hx hy hxy)
  rw [det_sub_outer _ (isUnit_iff_ne_zero.mpr hdet),
    Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal] at h
  have he : 1 - (fun j => 1 / y j) ⬝ᵥ ((cauchy x y)⁻¹ *ᵥ (fun i => 1 / x i)) =
      (∏ i, (x i - 1) / x i) * (∏ j, (y j - 1) / y j) := by
    apply mul_left_cancel₀ hdet
    calc
      _ = _ := h
      _ = _ := by ring
  linear_combination -he

end RiemannResearch.LinearAlgebra.CauchyProduct
