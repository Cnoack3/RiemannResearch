/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Exact Gram–Schmidt cofactor coordinates

Source: the user's triangular-matrix request, 4 November 2026. These are
finite Hilbert-space identities, generalized from the project's
RH/ResidueGramCofactors.lean. Mathlib supplies Gram–Schmidt, adjugates, and
orthogonal projection; no limiting density or constant-membership statement
is assumed.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.GramSchmidtCofactors
open InnerProductSpace
open RiemannResearch.Analysis.FiniteHilbertGram

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def initialFamily (v : ℕ → H) (n : ℕ) : Fin n → H := fun i => v i.val

def gram (v : ℕ → H) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  gramMatrix (initialFamily v n)

def mode (v : ℕ → H) (j : ℕ) : H := gramSchmidtNormed ℝ v j

def scale (v : ℕ → H) (j : ℕ) : ℝ := ‖gramSchmidt ℝ v j‖

/-- Column j contains j+1 coefficients, indexed from zero. -/
def coefficient (v : ℕ → H) (j : ℕ) (i : Fin (j + 1)) : ℝ :=
  (gram v (j + 1))⁻¹ i (Fin.last j) * scale v j

theorem prefix_independent {v : ℕ → H} (hv : LinearIndependent ℝ v) (n : ℕ) :
    LinearIndependent ℝ (initialFamily v n) :=
  hv.comp (fun i : Fin n => i.val) Fin.val_injective

theorem gram_det_pos {v : ℕ → H} (hv : LinearIndependent ℝ v) (n : ℕ) :
    0 < (gram v n).det :=
  gramMatrix_det_pos (prefix_independent hv n)

theorem scale_pos {v : ℕ → H} (hv : LinearIndependent ℝ v) (j : ℕ) :
    0 < scale v j :=
  norm_pos_iff.mpr (gramSchmidt_ne_zero j hv)

theorem mode_orthonormal {v : ℕ → H} (hv : LinearIndependent ℝ v) :
    Orthonormal ℝ (mode v) :=
  gramSchmidtNormed_orthonormal hv

theorem mode_mem_prefix_span (v : ℕ → H) (j : ℕ) :
    mode v j ∈ synthesisSpan (initialFamily v (j + 1)) := by
  change (scale v j)⁻¹ • gramSchmidt ℝ v j ∈
    Submodule.span ℝ (Set.range (initialFamily v (j + 1)))
  apply Submodule.smul_mem
  apply Submodule.span_mono _ (gramSchmidt_mem_span ℝ v (le_refl j))
  rintro x ⟨i, hi, rfl⟩
  exact ⟨⟨i, by change i ≤ j at hi; omega⟩, rfl⟩

theorem gramSchmidt_inner_self (v : ℕ → H) (j : ℕ) :
    inner ℝ (gramSchmidt ℝ v j) (v j) = (scale v j)^2 := by
  rw [gramSchmidt_def'' ℝ v j, inner_add_right, inner_sum,
    real_inner_self_eq_norm_sq]
  calc
    _ = (scale v j)^2 + 0 := by
      congr 1
      apply Finset.sum_eq_zero
      intro k hk
      rw [inner_smul_right,
        gramSchmidt_orthogonal ℝ v (Nat.ne_of_gt (Finset.mem_Iio.mp hk)), mul_zero]
    _ = _ := add_zero _

theorem atom_inner_mode {v : ℕ → H} (hv : LinearIndependent ℝ v)
    (j i : ℕ) (hij : i ≤ j) :
    inner ℝ (v i) (mode v j) = if i = j then scale v j else 0 := by
  by_cases he : i = j
  · subst i
    rw [if_pos rfl, real_inner_comm]
    change inner ℝ ((scale v j)⁻¹ • gramSchmidt ℝ v j) (v j) = _
    rw [real_inner_smul_left, gramSchmidt_inner_self]
    field_simp [ne_of_gt (scale_pos hv j)]
  · rw [if_neg he, real_inner_comm]
    change inner ℝ ((scale v j)⁻¹ • gramSchmidt ℝ v j) (v i) = 0
    rw [real_inner_smul_left, gramSchmidt_inv_triangular ℝ v
      (lt_of_le_of_ne hij he), mul_zero]

theorem mode_cross_single {v : ℕ → H} (hv : LinearIndependent ℝ v) (j : ℕ) :
    cross (initialFamily v (j + 1)) (mode v j) =
      Pi.single (Fin.last j) (scale v j) := by
  funext i
  rw [cross, initialFamily, atom_inner_mode hv j i.val (by omega)]
  simp [Pi.single_apply, Fin.ext_iff, eq_comm]

theorem coefficient_eq_inverseCoeff {v : ℕ → H} (hv : LinearIndependent ℝ v)
    (j : ℕ) :
    coefficient v j = inverseCoeff (prefix_independent hv (j + 1)) (mode v j) := by
  rw [inverseCoeff_eq_inv_mulVec, mode_cross_single hv]
  funext i
  simp [coefficient, gram, Matrix.mulVec, dotProduct, Pi.single_apply]

/-- The cofactor column is the actual normalized Gram–Schmidt vector. -/
theorem coefficient_synthesis {v : ℕ → H} (hv : LinearIndependent ℝ v) (j : ℕ) :
    (∑ i : Fin (j + 1), coefficient v j i • v i.val) = mode v j := by
  have h := synthesis_inverseCoeff_eq_projection
    (prefix_independent hv (j + 1)) (mode v j)
  rw [Submodule.starProjection_eq_self_iff.mpr (mode_mem_prefix_span v j)] at h
  simpa only [← coefficient_eq_inverseCoeff hv j,
    Fintype.linearCombination_apply, initialFamily] using h

theorem coefficient_unique {v : ℕ → H} (hv : LinearIndependent ℝ v) (j : ℕ)
    (c : Fin (j + 1) → ℝ)
    (hc : (∑ i : Fin (j + 1), c i • v i.val) = mode v j) :
    c = coefficient v j := by
  apply (prefix_independent hv (j + 1)).fintypeLinearCombination_injective
  change (∑ i : Fin (j + 1), c i • v i.val) =
    ∑ i : Fin (j + 1), coefficient v j i • v i.val
  exact hc.trans (coefficient_synthesis hv j).symm

theorem coefficient_diagonal_mul_scale {v : ℕ → H}
    (hv : LinearIndependent ℝ v) (j : ℕ) :
    coefficient v j (Fin.last j) * scale v j = 1 := by
  have he := congrArg (fun x => inner ℝ x (mode v j)) (coefficient_synthesis hv j)
  have hu : inner ℝ (mode v j) (mode v j) = 1 := by
    rw [real_inner_self_eq_norm_sq, (mode_orthonormal hv).1 j]
    norm_num
  rw [hu, sum_inner] at he
  simp only [real_inner_smul_left] at he
  have hs : (∑ k : Fin (j + 1),
      coefficient v j k * inner ℝ (v k.val) (mode v j)) =
      coefficient v j (Fin.last j) * scale v j := by
    rw [Finset.sum_eq_single (Fin.last j)]
    · simp [atom_inner_mode hv]
    · intro k hk hkj
      rw [atom_inner_mode hv j k.val (by omega), if_neg, mul_zero]
      exact fun h => hkj (Fin.ext h)
    · simp
  exact hs.symm.trans he

theorem coefficient_diagonal_pos {v : ℕ → H} (hv : LinearIndependent ℝ v)
    (j : ℕ) : 0 < coefficient v j (Fin.last j) := by
  have h := coefficient_diagonal_mul_scale hv j
  have hs := scale_pos hv j
  nlinarith

theorem coefficient_eq_adjugate (v : ℕ → H) (j : ℕ) (i : Fin (j + 1)) :
    coefficient v j i =
      (gram v (j + 1)).adjugate i (Fin.last j) * scale v j /
        (gram v (j + 1)).det := by
  rw [coefficient, Matrix.inv_def, Ring.inverse_eq_inv]
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

theorem gram_last_adjugate (v : ℕ → H) (j : ℕ) :
    (gram v (j + 1)).adjugate (Fin.last j) (Fin.last j) = (gram v j).det := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  have hm : (gram v (j + 1)).submatrix
      (Fin.last j).succAbove (Fin.last j).succAbove = gram v j := by
    ext i k
    simp [gram, initialFamily, gramMatrix, Matrix.submatrix_apply]
  rw [hm]
  simp [pow_add, ← mul_pow]

theorem scale_sq_mul_det {v : ℕ → H} (hv : LinearIndependent ℝ v) (j : ℕ) :
    (scale v j)^2 * (gram v j).det = (gram v (j + 1)).det := by
  have h := coefficient_diagonal_mul_scale hv j
  rw [coefficient_eq_adjugate, gram_last_adjugate] at h
  have hd : (gram v (j + 1)).det ≠ 0 := ne_of_gt (gram_det_pos hv (j + 1))
  field_simp [hd] at h
  nlinarith

theorem scale_eq_sqrt_det_ratio {v : ℕ → H} (hv : LinearIndependent ℝ v)
    (j : ℕ) :
    scale v j = Real.sqrt ((gram v (j + 1)).det / (gram v j).det) := by
  have hb : (gram v j).det ≠ 0 := ne_of_gt (gram_det_pos hv j)
  have hs : (scale v j)^2 = (gram v (j + 1)).det / (gram v j).det :=
    (eq_div_iff hb).mpr (scale_sq_mul_det hv j)
  rw [← hs, Real.sqrt_sq (le_of_lt (scale_pos hv j))]

theorem coefficient_diagonal_eq_sqrt_det_ratio {v : ℕ → H}
    (hv : LinearIndependent ℝ v) (j : ℕ) :
    coefficient v j (Fin.last j) =
      Real.sqrt ((gram v j).det / (gram v (j + 1)).det) := by
  have hc : (coefficient v j (Fin.last j))^2 * (gram v (j + 1)).det =
      (gram v j).det := by
    rw [← scale_sq_mul_det hv j]
    calc
      _ = (coefficient v j (Fin.last j) * scale v j)^2 * (gram v j).det := by ring
      _ = _ := by rw [coefficient_diagonal_mul_scale hv j]; simp
  have hs : (coefficient v j (Fin.last j))^2 =
      (gram v j).det / (gram v (j + 1)).det :=
    (eq_div_iff (ne_of_gt (gram_det_pos hv (j + 1)))).mpr hc
  rw [← hs, Real.sqrt_sq (le_of_lt (coefficient_diagonal_pos hv j))]

theorem coefficient_eq_normalized_adjugate {v : ℕ → H}
    (hv : LinearIndependent ℝ v) (j : ℕ) (i : Fin (j + 1)) :
    coefficient v j i =
      (gram v (j + 1)).adjugate i (Fin.last j) /
        Real.sqrt ((gram v j).det * (gram v (j + 1)).det) := by
  have hb := gram_det_pos hv j
  have hs := scale_pos hv j
  have hd := scale_sq_mul_det hv j
  have hr : Real.sqrt ((gram v j).det * (gram v (j + 1)).det) =
      scale v j * (gram v j).det := by
    rw [← hd]
    have he : (gram v j).det * ((scale v j)^2 * (gram v j).det) =
        (scale v j * (gram v j).det)^2 := by ring
    rw [he, Real.sqrt_sq (mul_nonneg hs.le hb.le)]
  rw [coefficient_eq_adjugate, hr, ← hd]
  field_simp [ne_of_gt hb, ne_of_gt hs]

/-- Delete the last row and the requested coefficient column. -/
theorem coefficient_eq_cofactor {v : ℕ → H}
    (hv : LinearIndependent ℝ v) (j : ℕ) (i : Fin (j + 1)) :
    coefficient v j i =
      (-1 : ℝ)^(j + i.val) *
        ((gram v (j + 1)).submatrix (Fin.last j).succAbove i.succAbove).det /
          Real.sqrt ((gram v j).det * (gram v (j + 1)).det) := by
  rw [coefficient_eq_normalized_adjugate hv,
    Matrix.adjugate_fin_succ_eq_det_submatrix]
  rfl

end RiemannResearch.Analysis.GramSchmidtCofactors
