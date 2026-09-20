import RiemannResearch.RH.ResidueOrthonormalCoordinates
import RiemannResearch.RH.IntegerDPPGramDeterminant

/-!
# Exact cofactor coefficients of the residue Gram--Schmidt system

Source: user-provided orthonormal/Gram conversation, 20 September 2026,
for the requested coefficient formulas. The finite inverse and adjugate
identities use Mathlib. All Gram entries are full Pareto inner products.
No limiting Parseval saturation or RH converse is assumed here.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.Analysis.FiniteHilbertGram
open TailCapacity IntegerDPP

/-- The positive normalization factor before the j-th Gram--Schmidt mode. -/
def residueModeScale (j : ℕ) : ℝ :=
  ‖InnerProductSpace.gramSchmidt ℝ residueAtom j‖

theorem residueModeScale_pos (j : ℕ) : 0 < residueModeScale j :=
  norm_pos_iff.mpr (InnerProductSpace.gramSchmidt_ne_zero j residueAtom_linearIndependent)

/-- Exact coordinates of any finite orthogonal projection. -/
theorem projection_coefficient_eq_inverseGram (n : ℕ) (x : ThresholdHilbert)
    (i : Fin n) :
    coefficientCLM (i.val + 2) ((finiteSpace n).starProjection x) =
      ((fullGram n)⁻¹.mulVec (cross (fun k : Fin n => residueAtom k.val) x)) i := by
  have hs := synthesis_inverseCoeff_eq_projection (finiteAtom_independent n) x
  change Fintype.linearCombination ℝ (fun k : Fin n => residueAtom k.val)
    (inverseCoeff (finiteAtom_independent n) x) =
      (finiteSpace n).starProjection x at hs
  rw [← hs, Fintype.linearCombination_apply,
    coefficient_finite_sum, fullGram, gramMatrix_inverseSource (finiteAtom_independent n)]
  rfl

theorem modeCoefficient_eq_inverseGram (j : ℕ) (i : Fin (j + 1)) :
    modeCoefficient (i.val + 2) j =
      ((fullGram (j + 1))⁻¹.mulVec
        (cross (fun k : Fin (j + 1) => residueAtom k.val) (residueMode j))) i := by
  have hm : residueMode j ∈ finiteSpace (j + 1) := by
    rw [← residueMode_finiteSpace]
    exact Submodule.subset_span ⟨Fin.last j, rfl⟩
  simpa only [Submodule.starProjection_eq_self_iff.mpr hm, modeCoefficient] using
    projection_coefficient_eq_inverseGram (j + 1) (residueMode j) i

private theorem gramSchmidt_inner_atom_self (j : ℕ) :
    inner ℝ (InnerProductSpace.gramSchmidt ℝ residueAtom j) (residueAtom j) =
      (residueModeScale j) ^ 2 := by
  rw [InnerProductSpace.gramSchmidt_def'' ℝ residueAtom j,
    inner_add_right, inner_sum, real_inner_self_eq_norm_sq]
  calc
    _ = (residueModeScale j)^2 + 0 := by
      congr 1
      apply Finset.sum_eq_zero
      intro k hk
      rw [inner_smul_right,
        InnerProductSpace.gramSchmidt_orthogonal ℝ residueAtom
          (Nat.ne_of_gt (Finset.mem_Iio.mp hk)), mul_zero]
    _ = _ := add_zero _

theorem residueAtom_inner_mode (j i : ℕ) (hij : i ≤ j) :
    inner ℝ (residueAtom i) (residueMode j) =
      if i = j then residueModeScale j else 0 := by
  by_cases he : i = j
  · subst i
    rw [if_pos rfl, real_inner_comm]
    change inner ℝ
      ((residueModeScale j)⁻¹ • InnerProductSpace.gramSchmidt ℝ residueAtom j)
      (residueAtom j) = _
    rw [real_inner_smul_left, gramSchmidt_inner_atom_self]
    field_simp [ne_of_gt (residueModeScale_pos j)]
  · rw [if_neg he, real_inner_comm]
    change inner ℝ
      ((residueModeScale j)⁻¹ • InnerProductSpace.gramSchmidt ℝ residueAtom j)
      (residueAtom i) = 0
    rw [real_inner_smul_left,
      InnerProductSpace.gramSchmidt_inv_triangular ℝ residueAtom
        (lt_of_le_of_ne hij he), mul_zero]

private theorem mode_cross_single (j : ℕ) :
    cross (fun k : Fin (j + 1) => residueAtom k.val) (residueMode j) =
      Pi.single (Fin.last j) (residueModeScale j) := by
  funext i
  rw [cross, residueAtom_inner_mode j i.val (by omega)]
  simp [Pi.single_apply, Fin.ext_iff, eq_comm]

theorem modeCoefficient_eq_scaled_inverseGram (j : ℕ) (i : Fin (j + 1)) :
    modeCoefficient (i.val + 2) j =
      (fullGram (j + 1))⁻¹ i (Fin.last j) * residueModeScale j := by
  rw [modeCoefficient_eq_inverseGram, mode_cross_single]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem modeCoefficient_mul_scale (j : ℕ) :
    modeCoefficient (j + 2) j * residueModeScale j = 1 := by
  have he := congrArg (fun x => inner ℝ x (residueMode j)) (residueMode_expansion j)
  have hu : inner ℝ (residueMode j) (residueMode j) = 1 := by
    rw [real_inner_self_eq_norm_sq, residueMode_orthonormal.1 j]
    norm_num
  rw [hu, sum_inner] at he
  simp only [real_inner_smul_left] at he
  have hs : (∑ k : Fin (j + 1), modeCoefficient (k.val + 2) j *
      inner ℝ (residueAtom k.val) (residueMode j)) =
        modeCoefficient (j + 2) j * residueModeScale j := by
    rw [Finset.sum_eq_single (Fin.last j)]
    · simp [residueAtom_inner_mode]
    · intro k hk hkj
      rw [residueAtom_inner_mode j k.val (by omega), if_neg, mul_zero]
      exact fun h => hkj (Fin.ext h)
    · simp
  exact (he.trans hs).symm

theorem modeCoefficient_diagonal_pos (j : ℕ) : 0 < modeCoefficient (j + 2) j := by
  have h := modeCoefficient_mul_scale j
  have hs := residueModeScale_pos j
  nlinarith

theorem modeCoefficient_eq_adjugate (j : ℕ) (i : Fin (j + 1)) :
    modeCoefficient (i.val + 2) j =
      (fullGram (j + 1)).adjugate i (Fin.last j) * residueModeScale j /
        (fullGram (j + 1)).det := by
  rw [modeCoefficient_eq_scaled_inverseGram, Matrix.inv_def, Ring.inverse_eq_inv]
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

theorem fullGram_last_adjugate (j : ℕ) :
    (fullGram (j + 1)).adjugate (Fin.last j) (Fin.last j) = (fullGram j).det := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  have hm : (fullGram (j + 1)).submatrix (Fin.last j).succAbove
      (Fin.last j).succAbove = fullGram j := by
    ext i k
    simp [fullGram, gramMatrix, Matrix.submatrix_apply]
  rw [hm]
  simp [pow_add, ← mul_pow]

theorem residueModeScale_sq_mul_det (j : ℕ) :
    (residueModeScale j) ^ 2 * (fullGram j).det = (fullGram (j + 1)).det := by
  have h := modeCoefficient_mul_scale j
  change modeCoefficient ((Fin.last j).val + 2) j * residueModeScale j = 1 at h
  rw [modeCoefficient_eq_adjugate j (Fin.last j), fullGram_last_adjugate] at h
  have hd : (fullGram (j + 1)).det ≠ 0 := ne_of_gt (fullGram_det_pos (j + 1))
  field_simp [hd] at h
  nlinarith

/-- The nonzero Gram--Schmidt normalization is the positive determinant ratio. -/
theorem residueModeScale_eq_sqrt_det_ratio (j : ℕ) :
    residueModeScale j = Real.sqrt ((fullGram (j + 1)).det / (fullGram j).det) := by
  have hb : (fullGram j).det ≠ 0 := ne_of_gt (fullGram_det_pos j)
  have hs : (residueModeScale j) ^ 2 =
      (fullGram (j + 1)).det / (fullGram j).det :=
    (eq_div_iff hb).mpr (residueModeScale_sq_mul_det j)
  rw [← hs, Real.sqrt_sq (le_of_lt (residueModeScale_pos j))]

/-- The positive leading coefficient is sqrt(Δ_previous / Δ_current). -/
theorem modeCoefficient_diagonal_eq_sqrt_det_ratio (j : ℕ) :
    modeCoefficient (j + 2) j =
      Real.sqrt ((fullGram j).det / (fullGram (j + 1)).det) := by
  have hc : (modeCoefficient (j + 2) j)^2 * (fullGram (j + 1)).det =
      (fullGram j).det := by
    rw [← residueModeScale_sq_mul_det]
    calc
      _ = (modeCoefficient (j + 2) j * residueModeScale j)^2 *
          (fullGram j).det := by ring
      _ = _ := by rw [modeCoefficient_mul_scale]; simp
  have hs : (modeCoefficient (j + 2) j)^2 =
      (fullGram j).det / (fullGram (j + 1)).det :=
    (eq_div_iff (ne_of_gt (fullGram_det_pos (j + 1)))).mpr hc
  rw [← hs, Real.sqrt_sq (le_of_lt (modeCoefficient_diagonal_pos j))]

/-- The normalized Gram cofactor formula, before expanding the cofactor sign. -/
theorem modeCoefficient_eq_normalized_adjugate (j : ℕ) (i : Fin (j + 1)) :
    modeCoefficient (i.val + 2) j =
      (fullGram (j + 1)).adjugate i (Fin.last j) /
        Real.sqrt ((fullGram j).det * (fullGram (j + 1)).det) := by
  have hb := fullGram_det_pos j
  have hs := residueModeScale_pos j
  have hd := residueModeScale_sq_mul_det j
  have hr : Real.sqrt ((fullGram j).det * (fullGram (j + 1)).det) =
      residueModeScale j * (fullGram j).det := by
    rw [← hd]
    have he : (fullGram j).det * ((residueModeScale j)^2 * (fullGram j).det) =
        (residueModeScale j * (fullGram j).det)^2 := by ring
    rw [he, Real.sqrt_sq (mul_nonneg hs.le hb.le)]
  rw [modeCoefficient_eq_adjugate, hr, ← hd]
  field_simp [ne_of_gt hb, ne_of_gt hs]

/-- Exact signed minors: delete the last row and column i, in increasing order. -/
theorem modeCoefficient_eq_cofactor (j : ℕ) (i : Fin (j + 1)) :
    modeCoefficient (i.val + 2) j =
      (-1 : ℝ) ^ (j + i.val) *
        ((fullGram (j + 1)).submatrix (Fin.last j).succAbove i.succAbove).det /
          Real.sqrt ((fullGram j).det * (fullGram (j + 1)).det) := by
  rw [modeCoefficient_eq_normalized_adjugate,
    Matrix.adjugate_fin_succ_eq_det_submatrix]
  rfl

end RiemannResearch.RH.Pareto.CoefficientStabilization
