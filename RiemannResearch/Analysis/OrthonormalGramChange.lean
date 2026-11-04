/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# Exact finite orthonormal Gram change of coordinates

Source: the user's triangular-matrix request, 4 November 2026.
Columns synthesize orthonormal vectors from a linearly independent dictionary.
The identities use the actual complete Hilbert inner product.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.OrthonormalGramChange
open RiemannResearch.Analysis.FiniteHilbertGram

variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def coefficients {v : ι → H} (hv : LinearIndependent ℝ v) (e : ι → H) :
    Matrix ι ι ℝ := fun i j => inverseCoeff hv (e j) i

def crossMatrix (v e : ι → H) : Matrix ι ι ℝ :=
  fun i j => inner ℝ (e i) (v j)

theorem column_synthesis {v : ι → H} (hv : LinearIndependent ℝ v) (e : ι → H)
    (hmem : ∀ j, e j ∈ synthesisSpan v) (j : ι) :
    (∑ i, coefficients hv e i j • v i) = e j := by
  have h := synthesis_inverseCoeff_eq_projection hv (e j)
  rw [Submodule.starProjection_eq_self_iff.mpr (hmem j)] at h
  exact h

theorem cross_mul_coefficients {v : ι → H} (hv : LinearIndependent ℝ v)
    {e : ι → H} (he : Orthonormal ℝ e)
    (hmem : ∀ j, e j ∈ synthesisSpan v) :
    crossMatrix v e * coefficients hv e = 1 := by
  ext i j
  calc
    _ = inner ℝ (e i) (e j) := by
      rw [← column_synthesis hv e hmem j]
      simp only [Matrix.mul_apply, crossMatrix, inner_sum, real_inner_smul_right]
      apply Finset.sum_congr rfl
      intro k _
      exact mul_comm _ _
    _ = (1 : Matrix ι ι ℝ) i j := by
      by_cases hij : i = j
      · subst j
        simp only [Matrix.one_apply_eq, real_inner_self_eq_norm_sq, he.1, one_pow]
      · simp only [Matrix.one_apply_ne hij, he.2 hij]

theorem coefficients_mul_cross {v : ι → H} (hv : LinearIndependent ℝ v)
    {e : ι → H} (he : Orthonormal ℝ e)
    (hmem : ∀ j, e j ∈ synthesisSpan v) :
    coefficients hv e * crossMatrix v e = 1 := by
  have h := cross_mul_coefficients hv he hmem
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at hd
  have hu : IsUnit (crossMatrix v e).det := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    rw [hz, zero_mul] at hd
    exact zero_ne_one hd
  rw [← Matrix.inv_eq_right_inv h]
  exact Matrix.nonsing_inv_mul _ hu

theorem coefficients_inverse {v : ι → H} (hv : LinearIndependent ℝ v)
    {e : ι → H} (he : Orthonormal ℝ e)
    (hmem : ∀ j, e j ∈ synthesisSpan v) :
    (coefficients hv e)⁻¹ = crossMatrix v e :=
  Matrix.inv_eq_left_inv (cross_mul_coefficients hv he hmem)

theorem cross_inverse {v : ι → H} (hv : LinearIndependent ℝ v)
    {e : ι → H} (he : Orthonormal ℝ e)
    (hmem : ∀ j, e j ∈ synthesisSpan v) :
    (crossMatrix v e)⁻¹ = coefficients hv e :=
  Matrix.inv_eq_right_inv (cross_mul_coefficients hv he hmem)

theorem transpose_coefficients_mul_gram {v : ι → H}
    (hv : LinearIndependent ℝ v) (e : ι → H)
    (hmem : ∀ j, e j ∈ synthesisSpan v) :
    (coefficients hv e).transpose * gramMatrix v = crossMatrix v e := by
  ext i j
  have h := congrArg (fun x => inner ℝ x (v j)) (column_synthesis hv e hmem i)
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, gramMatrix,
    crossMatrix, sum_inner, real_inner_smul_left] using h

theorem orthonormal_gram_identity {v : ι → H} (hv : LinearIndependent ℝ v)
    {e : ι → H} (he : Orthonormal ℝ e)
    (hmem : ∀ j, e j ∈ synthesisSpan v) :
    (coefficients hv e).transpose * gramMatrix v * coefficients hv e = 1 := by
  rw [transpose_coefficients_mul_gram hv e hmem, cross_mul_coefficients hv he hmem]

theorem gram_eq_transpose_cross_mul_cross {v : ι → H}
    (hv : LinearIndependent ℝ v) {e : ι → H} (he : Orthonormal ℝ e)
    (hmem : ∀ j, e j ∈ synthesisSpan v) :
    gramMatrix v = (crossMatrix v e).transpose * crossMatrix v e := by
  calc
    _ = ((crossMatrix v e).transpose * (coefficients hv e).transpose) * gramMatrix v := by
      rw [← Matrix.transpose_mul, coefficients_mul_cross hv he hmem,
        Matrix.transpose_one, Matrix.one_mul]
    _ = (crossMatrix v e).transpose *
        ((coefficients hv e).transpose * gramMatrix v) := Matrix.mul_assoc _ _ _
    _ = _ := by rw [transpose_coefficients_mul_gram hv e hmem]

theorem coefficients_eq_inverse_gram_mul_transpose_cross {v : ι → H}
    (hv : LinearIndependent ℝ v) (e : ι → H) :
    coefficients hv e = (gramMatrix v)⁻¹ * (crossMatrix v e).transpose := by
  ext i j
  simp only [coefficients, inverseCoeff_eq_inv_mulVec,
    Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply,
    cross, crossMatrix, real_inner_comm]

end RiemannResearch.Analysis.OrthonormalGramChange
