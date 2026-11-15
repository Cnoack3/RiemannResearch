/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.LinearAlgebra.RationalPositiveDefiniteCertificate
import Mathlib.Data.Matrix.Mul

/-!
# Staged rational interval matrix certificates

Source: the complete-Q spectral calculations in the user's reciprocal-head
review. Intermediate interval matrices are untrusted witnesses. Proved
entrywise multiplication enclosures retain every signed summand while avoiding
repeated expansion of a four-index congruence in each numerical certificate.
-/

noncomputable section
open scoped BigOperators
open Matrix WithLp
namespace RiemannResearch.RatInterval
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def pointMatrix (A : Matrix ι ι ℚ) : Matrix ι ι RatInterval :=
  fun i j => point (A i j)

theorem pointMatrix_contains (A : Matrix ι ι ℚ) (i j : ι) :
    (pointMatrix A i j).Contains (A i j : ℝ) := contains_point _

def matrixProduct (A B : Matrix ι ι RatInterval) : Matrix ι ι RatInterval :=
  fun i j => sum Finset.univ (fun k => mul (A i k) (B k j))

theorem matrixProduct_contains
    (AI BI : Matrix ι ι RatInterval) (A B : Matrix ι ι ℝ)
    (hA : ∀ i j, (AI i j).Contains (A i j))
    (hB : ∀ i j, (BI i j).Contains (B i j)) (i j : ι) :
    (matrixProduct AI BI i j).Contains ((A * B) i j) := by
  apply contains_sum
  intro k _
  exact contains_mul (hA i k) (hB k j)

def leftCongruence (AI : Matrix ι ι RatInterval) (T : Matrix ι ι ℚ) :
    Matrix ι ι RatInterval := matrixProduct (pointMatrix T) AI

def rightCongruence (LI : Matrix ι ι RatInterval) (T : Matrix ι ι ℚ) :
    Matrix ι ι RatInterval := matrixProduct LI (pointMatrix T.transpose)

/-- Soundness of two separately rounded matrix products. -/
theorem stagedCongruence_contains
    (AI LI BI : Matrix ι ι RatInterval) (A : Matrix ι ι ℝ) (T : Matrix ι ι ℚ)
    (hA : ∀ i j, (AI i j).Contains (A i j))
    (hleft : ∀ i j, (LI i j).lo ≤ (leftCongruence AI T i j).lo ∧
      (leftCongruence AI T i j).hi ≤ (LI i j).hi)
    (hright : ∀ i j, (BI i j).lo ≤ (rightCongruence LI T i j).lo ∧
      (rightCongruence LI T i j).hi ≤ (BI i j).hi) (i j : ι) :
    (BI i j).Contains
      (((Matrix.of fun i j => (T i j : ℝ)) * A * star (Matrix.of fun i j => (T i j : ℝ))) i j) := by
  let T' : Matrix ι ι ℝ := Matrix.of fun i j => (T i j : ℝ)
  have hL : ∀ i j, (LI i j).Contains ((T' * A) i j) := by
    intro i j
    exact contains_weaken (matrixProduct_contains (pointMatrix T) AI T' A
      (pointMatrix_contains T) hA i j) (hleft i j).1 (hleft i j).2
  have hT : ∀ i j, (pointMatrix T.transpose i j).Contains (star T' i j) := by
    intro i j
    simpa only [T', Matrix.star_apply, star_trivial, Matrix.transpose_apply, Matrix.of_apply] using
      pointMatrix_contains T.transpose i j
  exact contains_weaken (matrixProduct_contains LI (pointMatrix T.transpose) (T' * A)
    (star T') hL hT i j) (hright i j).1 (hright i j).2

/-- Strict diagonal dominance of a proved interval enclosure certifies
positive definiteness of the actual Hermitian matrix. -/
theorem posDef_of_dominant_enclosure
    (AI : Matrix ι ι RatInterval) (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (hAI : ∀ i j, (AI i j).Contains (A i j))
    (hcert : ∀ i, (∑ j ∈ Finset.univ.erase i, absBound (AI i j)) < (AI i i).lo) :
    A.PosDef := by
  rw [hA.posDef_iff_eigenvalues_pos]
  intro i
  have hEig : Module.End.HasEigenvalue (Matrix.toLin' A) (hA.eigenvalues i) := by
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨by
        rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
        exact hA.mulVec_eigenvectorBasis i,
       (ofLp_eq_zero 2).ne.2 <| hA.eigenvectorBasis.orthonormal.ne_zero i⟩
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball hEig
  rw [mem_closedBall_iff_norm'] at hk
  have habs : |A k k - hA.eigenvalues i| ≤
      ∑ j ∈ Finset.univ.erase k, ‖A k j‖ := by
    simpa only [Real.norm_eq_abs] using hk
  have hrow : (∑ j ∈ Finset.univ.erase k, ‖A k j‖) ≤
      ∑ j ∈ Finset.univ.erase k, (absBound (AI k j) : ℝ) := by
    apply Finset.sum_le_sum
    intro j _
    simpa only [Real.norm_eq_abs] using abs_le_absBound (hAI k j)
  have hcertR : (∑ j ∈ Finset.univ.erase k, (absBound (AI k j) : ℝ)) <
      ((AI k k).lo : ℝ) := by exact_mod_cast hcert k
  have hdiag : ((AI k k).lo : ℝ) ≤ A k k := (hAI k k).1
  linarith [(abs_le.mp habs).2]

/-- The congruence enclosure may be checked in successive matrix products.
The rational right inverse prevents singular congruences from hiding a kernel. -/
theorem posDef_of_congruence_enclosure
    (BI : Matrix ι ι RatInterval) (A : Matrix ι ι ℝ)
    (T S : Matrix ι ι ℚ) (hA : A.IsHermitian)
    (hBI : ∀ i j, (BI i j).Contains
      (((Matrix.of fun i j => (T i j : ℝ)) * A * star (Matrix.of fun i j => (T i j : ℝ))) i j))
    (hTS : T * S = 1)
    (hcert : ∀ i, (∑ j ∈ Finset.univ.erase i, absBound (BI i j)) < (BI i i).lo) :
    A.PosDef := by
  let T' : Matrix ι ι ℝ := Matrix.of fun i j => (T i j : ℝ)
  have hT : IsUnit T' := cast_matrix_isUnit_of_right_inverse T S hTS
  apply (hT.posDef_star_right_conjugate_iff).1
  exact posDef_of_dominant_enclosure BI _
    (by simpa only [Matrix.star_eq_conjTranspose] using
      Matrix.isHermitian_mul_mul_conjTranspose T' hA) hBI hcert

end RiemannResearch.RatInterval
