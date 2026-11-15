/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact inverse-Gram Euclidean norm from the actual least eigenvalue

Source: the reciprocal-head investigation, 7 November 2026, Section 4.
The least eigenvalue is the finite minimum of the actual Hermitian spectral
values. Positivity and inverse eigenvector action follow from positive
definiteness and the genuine nonsingular matrix inverse.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.PositiveGramMinimumEigenvalue
variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The actual least Hermitian eigenvalue, not a reciprocal definition. -/
def leastEigenvalue {A : Matrix ι ι ℝ} (hA : A.PosDef) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty hA.isHermitian.eigenvalues

theorem leastEigenvalue_le {A : Matrix ι ι ℝ} (hA : A.PosDef) (i : ι) :
    leastEigenvalue hA ≤ hA.isHermitian.eigenvalues i := by
  exact Finset.inf'_le _ (Finset.mem_univ i)

theorem leastEigenvalue_attained {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    ∃ i : ι, leastEigenvalue hA = hA.isHermitian.eigenvalues i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty hA.isHermitian.eigenvalues
  exact ⟨i, hi⟩

theorem leastEigenvalue_pos {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    0 < leastEigenvalue hA := by
  obtain ⟨i, hi⟩ := leastEigenvalue_attained hA
  rw [hi]
  exact hA.eigenvalues_pos i

/-- The actual inverse sends each eigenvector to the reciprocal eigenvalue. -/
theorem inverse_eigenvector {A : Matrix ι ι ℝ} (hA : A.PosDef) (i : ι) :
    Matrix.toEuclideanLin A⁻¹ (hA.isHermitian.eigenvectorBasis i) =
      (hA.isHermitian.eigenvalues i)⁻¹ • hA.isHermitian.eigenvectorBasis i := by
  have he := hA.isHermitian.mulVec_eigenvectorBasis i
  have hc := congrArg (fun v : ι → ℝ => A⁻¹.mulVec v) he
  rw [Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr (ne_of_gt hA.det_pos)),
    Matrix.one_mulVec, Matrix.mulVec_smul] at hc
  have hi : A⁻¹.mulVec (hA.isHermitian.eigenvectorBasis i).ofLp =
      (hA.isHermitian.eigenvalues i)⁻¹ • (hA.isHermitian.eigenvectorBasis i).ofLp := by
    calc
      _ = (hA.isHermitian.eigenvalues i)⁻¹ •
          (hA.isHermitian.eigenvalues i •
            A⁻¹.mulVec (hA.isHermitian.eigenvectorBasis i).ofLp) := by
        rw [smul_smul, inv_mul_cancel₀ (ne_of_gt (hA.eigenvalues_pos i)), one_smul]
      _ = _ := by rw [← hc]
  apply (WithLp.linearEquiv 2 ℝ (ι → ℝ)).injective
  rw [map_smul]
  change (Matrix.toEuclideanLin A⁻¹ (hA.isHermitian.eigenvectorBasis i)).ofLp = _
  rw [Matrix.ofLp_toEuclideanLin_apply]
  exact hi

private theorem diagonal_inner
    (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι))
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) (eigenvalues : ι → ℝ)
    (hL : ∀ i, L (b i) = eigenvalues i • b i) (x : EuclideanSpace ℝ ι) :
    inner ℝ (L x) x = ∑ i, (inner ℝ (b i) x) ^ 2 * eigenvalues i := by
  calc
    _ = inner ℝ (L (∑ i, inner ℝ (b i) x • b i)) x := by rw [b.sum_repr' x]
    _ = _ := by
      simp only [map_sum, map_smul, sum_inner, real_inner_smul_left, hL]
      apply Finset.sum_congr rfl
      intro i hi
      ring

private theorem basis_parseval
    (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)) (x : EuclideanSpace ℝ ι) :
    ‖x‖ ^ 2 = ∑ i, (inner ℝ (b i) x) ^ 2 := by
  have h := diagonal_inner b LinearMap.id (fun _ => 1) (by intro i; simp) x
  simpa only [LinearMap.id_apply, real_inner_self_eq_norm_sq, mul_one] using h

/-- No cross terms are dropped: they vanish in the actual orthonormal eigenbasis. -/
theorem inverse_quadratic_spectral {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (x : EuclideanSpace ℝ ι) :
    inner ℝ (Matrix.toEuclideanLin A⁻¹ x) x =
      ∑ i, (inner ℝ (hA.isHermitian.eigenvectorBasis i) x) ^ 2 *
        (hA.isHermitian.eigenvalues i)⁻¹ :=
  diagonal_inner hA.isHermitian.eigenvectorBasis (Matrix.toEuclideanLin A⁻¹)
    (fun i => (hA.isHermitian.eigenvalues i)⁻¹) (inverse_eigenvector hA) x

theorem inverse_quadratic_le {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (x : EuclideanSpace ℝ ι) :
    inner ℝ (Matrix.toEuclideanLin A⁻¹ x) x ≤
      (1 / leastEigenvalue hA) * ‖x‖ ^ 2 := by
  rw [inverse_quadratic_spectral hA, basis_parseval hA.isHermitian.eigenvectorBasis,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hl := one_div_le_one_div_of_le (leastEigenvalue_pos hA) (leastEigenvalue_le hA i)
  simpa only [one_div, mul_comm] using
    mul_le_mul_of_nonneg_left hl (sq_nonneg (inner ℝ (hA.isHermitian.eigenvectorBasis i) x))

/-- The complete normalized Euclidean minimum-repair operator has squared norm
exactly the reciprocal of the actual least Gram eigenvalue. -/
theorem norm_sq_eq_reciprocal_leastEigenvalue
    {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (T : EuclideanSpace ℝ ι →L[ℝ] H)
    (henergy : ∀ x, ‖T x‖ ^ 2 = inner ℝ (Matrix.toEuclideanLin A⁻¹ x) x) :
    ‖T‖ ^ 2 = 1 / leastEigenvalue hA := by
  have hp : 0 ≤ 1 / leastEigenvalue hA := (one_div_pos.mpr (leastEigenvalue_pos hA)).le
  have hupper : ‖T‖ ^ 2 ≤ 1 / leastEigenvalue hA := by
    have hn : ‖T‖ ≤ Real.sqrt (1 / leastEigenvalue hA) := by
      apply ContinuousLinearMap.opNorm_le_of_unit_norm (Real.sqrt_nonneg _)
      intro x hx
      have h := inverse_quadratic_le hA x
      rw [← henergy, hx, one_pow, mul_one] at h
      have hs := Real.sq_sqrt hp
      nlinarith [norm_nonneg (T x), Real.sqrt_nonneg (1 / leastEigenvalue hA)]
    have hs := (sq_le_sq₀ (norm_nonneg T) (Real.sqrt_nonneg (1 / leastEigenvalue hA))).mpr hn
    rwa [Real.sq_sqrt hp] at hs
  have hlower : 1 / leastEigenvalue hA ≤ ‖T‖ ^ 2 := by
    obtain ⟨i, hi⟩ := leastEigenvalue_attained hA
    let x := hA.isHermitian.eigenvectorBasis i
    have hx : ‖x‖ = 1 := hA.isHermitian.eigenvectorBasis.orthonormal.norm_eq_one i
    have he : ‖T x‖ ^ 2 = 1 / leastEigenvalue hA := by
      rw [henergy, inverse_eigenvector hA, real_inner_smul_left,
        real_inner_self_eq_norm_sq, hx, one_pow, mul_one, hi, one_div]
    have hn := T.le_opNorm x
    rw [hx, mul_one] at hn
    have hs := (sq_le_sq₀ (norm_nonneg (T x)) (norm_nonneg T)).mpr hn
    rwa [he] at hs
  exact le_antisymm hupper hlower

end RiemannResearch.Analysis.PositiveGramMinimumEigenvalue
