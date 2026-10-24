import RiemannResearch.LinearAlgebra.CauchyNonsingular
import RiemannResearch.LinearAlgebra.CauchyInverseProduct
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Centered mixed inverse Cauchy products

Source: user-requested fourth Ramanujan development, October 2026.
The rank-one determinant proof extends the exact finite Cauchy identity to
two independent centers. The multiplicative identity remains valid when the
sum of the centers is zero; only the divided version excludes that case.
-/

noncomputable section
open scoped BigOperators Matrix

namespace RiemannResearch.LinearAlgebra.CauchyProduct
open RiemannResearch.LinearAlgebra
variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

theorem cauchy_centered_sub_outer (x y : ι → K) (u v : K)
    (hxy : ∀ i j, x i + y j ≠ 0)
    (hxv : ∀ i, x i + v ≠ 0) (huy : ∀ j, u + y j ≠ 0) :
    cauchyMatrix x y - (u + v) •
      Matrix.vecMulVec (fun i => 1 / (x i + v)) (fun j => 1 / (u + y j)) =
      Matrix.diagonal (fun i => (x i - u) / (x i + v)) * cauchyMatrix x y *
        Matrix.diagonal (fun j => (y j - v) / (u + y j)) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec, Matrix.of_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    cauchyMatrix]
  field_simp [hxy i j, hxv i, huy j] <;> ring

/-- The weighted inverse-pairing identity includes the zero sum of centers. -/
theorem cauchy_centered_inverse_pairing_mul (x y : ι → K) (u v : K)
    (hxy : ∀ i j, x i + y j ≠ 0)
    (hxv : ∀ i, x i + v ≠ 0) (huy : ∀ j, u + y j ≠ 0)
    (hdet : (cauchyMatrix x y).det ≠ 0) :
    (u + v) * ((fun j => 1 / (u + y j)) ⬝ᵥ
      ((cauchyMatrix x y)⁻¹ *ᵥ (fun i => 1 / (x i + v)))) =
      1 - (∏ i, (x i - u) / (x i + v)) *
        (∏ j, (y j - v) / (u + y j)) := by
  have hout : (u + v) •
      Matrix.vecMulVec (fun i => 1 / (x i + v)) (fun j => 1 / (u + y j)) =
      Matrix.vecMulVec (fun i => (u + v) * (1 / (x i + v)))
        (fun j => 1 / (u + y j)) := by
    ext i j
    simp [Matrix.vecMulVec, Matrix.smul_apply, smul_eq_mul, mul_assoc]
  have hscale : (fun j => 1 / (u + y j)) ⬝ᵥ
      ((cauchyMatrix x y)⁻¹ *ᵥ (fun i => (u + v) * (1 / (x i + v)))) =
      (u + v) * ((fun j => 1 / (u + y j)) ⬝ᵥ
        ((cauchyMatrix x y)⁻¹ *ᵥ (fun i => 1 / (x i + v)))) := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h := congrArg Matrix.det (cauchy_centered_sub_outer x y u v hxy hxv huy)
  rw [hout, det_sub_outer _ (isUnit_iff_ne_zero.mpr hdet), hscale,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal] at h
  have he : 1 - (u + v) * ((fun j => 1 / (u + y j)) ⬝ᵥ
      ((cauchyMatrix x y)⁻¹ *ᵥ (fun i => 1 / (x i + v)))) =
      (∏ i, (x i - u) / (x i + v)) *
        (∏ j, (y j - v) / (u + y j)) := by
    apply mul_left_cancel₀ hdet
    calc
      _ = _ := h
      _ = _ := by ring
  linear_combination -he

theorem cauchy_centered_inverse_pairing_product (x y : ι → K) (u v : K)
    (hxy : ∀ i j, x i + y j ≠ 0)
    (hxv : ∀ i, x i + v ≠ 0) (huy : ∀ j, u + y j ≠ 0)
    (hdet : (cauchyMatrix x y).det ≠ 0) (huv : u + v ≠ 0) :
    (fun j => 1 / (u + y j)) ⬝ᵥ
      ((cauchyMatrix x y)⁻¹ *ᵥ (fun i => 1 / (x i + v))) =
      (1 - (∏ i, (x i - u) / (x i + v)) *
        (∏ j, (y j - v) / (u + y j))) / (u + v) := by
  have h := cauchy_centered_inverse_pairing_mul x y u v hxy hxv huy hdet
  field_simp [huv]
  linear_combination h

end RiemannResearch.LinearAlgebra.CauchyProduct
