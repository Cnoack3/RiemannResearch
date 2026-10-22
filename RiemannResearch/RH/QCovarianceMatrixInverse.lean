import RiemannResearch.RH.QCovarianceInvertibility

/-!
# Full Sherman--Morrison inverse for the actual Q residue covariance

Source: the user's exact inverse-Gram computation and the standard
Sherman--Morrison identity. All matrix inverses here are genuine: positivity
has already been proved for every distinct family of conductors greater
than one. The proof applies both inverse matrices to arbitrary source
vectors and then extracts their columns.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCovarianceMatrixInverse

open RiemannResearch.LinearAlgebra.CenteredNormalEquations
open RiemannResearch.RH.QCovarianceInverse
open RiemannResearch.RH.QCovarianceInvertibility

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem covarianceInverse_mulVec_normal (d : ι → ℕ)
    (hd : ∀ i, 1 < d i) (hinj : Function.Injective d) (y : ι → ℝ) (i : ι) :
    action (qCov d) ((residueCovarianceMatrix d)⁻¹.mulVec y) i = y i := by
  have hdet : IsUnit (residueCovarianceMatrix d).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (qCov_posDef d hd hinj).det_pos)
  have hh : (residueCovarianceMatrix d).mulVec
      ((residueCovarianceMatrix d)⁻¹.mulVec y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  exact congrFun hh i

/-- The full inverse action for every right-hand side, not only the mean vector. -/
theorem gramInverse_mulVec_eq_rankOne (d : ι → ℕ)
    (hd : ∀ i, 1 < d i) (hinj : Function.Injective d) (y : ι → ℝ) :
    (residueGramMatrix d)⁻¹.mulVec y =
      fun i => (residueCovarianceMatrix d)⁻¹.mulVec y i -
        (dot y (covarianceInverseSource d) / (1 + covarianceInformation d)) *
          covarianceInverseSource d i := by
  let u := covarianceInverseSource d
  let w := (residueCovarianceMatrix d)⁻¹.mulVec y
  let a := dot y u / (1 + covarianceInformation d)
  let c : ι → ℝ := fun i => w i - a * u i
  have hu : ∀ i, action (qCov d) u i = qMean d i :=
    covarianceInverseSource_normal d hd hinj
  have hw : ∀ i, action (qCov d) w i = y i :=
    covarianceInverse_mulVec_normal d hd hinj y
  have hbw : dot (qMean d) w = dot y u :=
    solve_reciprocity (qCov d) (qMean d) y u w (qCov_symmetric d) hu hw
  have hden : 1 + covarianceInformation d ≠ 0 := by
    have h := qInformation_nonneg d u hu
    change 0 ≤ covarianceInformation d at h
    linarith
  have hc (i : ι) : action (qGram d) c i = y i := by
    change action (qGram d) (fun j => w j - a * u j) i = y i
    rw [qGram_rankOne, action_rankOneAdd, action_sub_smul, hw, hu,
      dot_sub_smul_right, hbw]
    change y i - a * qMean d i + qMean d i *
      (dot y u - a * covarianceInformation d) = y i
    dsimp only [a]
    field_simp [hden]
    <;> ring
  have hcM : (residueGramMatrix d).mulVec c = y := funext hc
  have hdet : IsUnit (residueGramMatrix d).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (qGram_posDef d hd hinj).det_pos)
  change (residueGramMatrix d)⁻¹.mulVec y = c
  rw [← hcM, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

theorem gramInverse_entry (d : ι → ℕ)
    (hd : ∀ i, 1 < d i) (hinj : Function.Injective d) (i j : ι) :
    (residueGramMatrix d)⁻¹ i j = (residueCovarianceMatrix d)⁻¹ i j -
      covarianceInverseSource d i * covarianceInverseSource d j /
        (1 + covarianceInformation d) := by
  have h := congrFun
    (gramInverse_mulVec_eq_rankOne d hd hinj (Pi.single j 1)) i
  have h' : (residueGramMatrix d)⁻¹ i j = (residueCovarianceMatrix d)⁻¹ i j -
      (covarianceInverseSource d j / (1 + covarianceInformation d)) *
        covarianceInverseSource d i := by
    simpa [Matrix.mulVec, dotProduct, dot, Pi.single_apply] using h
  rw [h']
  ring

/-- The complete literal inverse matrix, with all off-diagonal entries retained. -/
theorem gramInverse_eq_covarianceInverse_sub_rankOne (d : ι → ℕ)
    (hd : ∀ i, 1 < d i) (hinj : Function.Injective d) :
    (residueGramMatrix d)⁻¹ = (residueCovarianceMatrix d)⁻¹ -
      (1 / (1 + covarianceInformation d)) •
        Matrix.vecMulVec (covarianceInverseSource d) (covarianceInverseSource d) := by
  ext i j
  change (residueGramMatrix d)⁻¹ i j = (residueCovarianceMatrix d)⁻¹ i j -
    (1 / (1 + covarianceInformation d)) *
      (covarianceInverseSource d i * covarianceInverseSource d j)
  rw [gramInverse_entry d hd hinj]
  ring

end RiemannResearch.RH.QCovarianceMatrixInverse
