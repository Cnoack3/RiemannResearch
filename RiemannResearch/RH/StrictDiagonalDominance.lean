/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Gershgorin

/-!
# Strict diagonal-dominance certificates for real Hermitian matrices

This module supplies the proof kernel used by the repaired finite-dimensional
`L = log 3` positivity certificate. A real Hermitian matrix whose positive
diagonal strictly dominates every absolute off-diagonal row sum is positive
definite. The proof uses the spectral theorem and Gershgorin's theorem.
-/

namespace RiemannResearch.RH.StrictDiagonalDominance

open scoped BigOperators
open Matrix WithLp

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The sum of absolute values outside the diagonal in row `i`. -/
def offDiagonalRowSum (A : Matrix n n ℝ) (i : n) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, ‖A i j‖

/-- Strict row diagonal dominance with a positive, rather than absolute-valued,
diagonal. -/
def StrictlyRowDiagonallyDominant (A : Matrix n n ℝ) : Prop :=
  ∀ i, offDiagonalRowSum A i < A i i

/-- Every eigenvalue of a real Hermitian, strictly row-diagonally-dominant
matrix is positive. -/
theorem eigenvalues_pos_of_strictlyRowDiagonallyDominant
    {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (hdom : StrictlyRowDiagonallyDominant A) :
    ∀ i, 0 < hA.eigenvalues i := by
  intro i
  have hEig : Module.End.HasEigenvalue (Matrix.toLin' A) (hA.eigenvalues i) := by
    apply Module.End.hasEigenvalue_of_hasEigenvector
    refine ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
      exact hA.mulVec_eigenvectorBasis i
    · exact (ofLp_eq_zero 2).ne.2 <| hA.eigenvectorBasis.orthonormal.ne_zero i
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball hEig
  rw [mem_closedBall_iff_norm'] at hk
  have habs : |A k k - hA.eigenvalues i| ≤ offDiagonalRowSum A k := by
    simpa [offDiagonalRowSum, Real.norm_eq_abs] using hk
  have hright : A k k - hA.eigenvalues i ≤ offDiagonalRowSum A k :=
    (abs_le.mp habs).2
  linarith [hdom k]

/-- A real Hermitian matrix is positive definite when every diagonal entry
strictly dominates the absolute off-diagonal row sum. -/
theorem posDef_of_strictlyRowDiagonallyDominant
    {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (hdom : StrictlyRowDiagonallyDominant A) :
    A.PosDef := by
  rw [hA.posDef_iff_eigenvalues_pos]
  exact eigenvalues_pos_of_strictlyRowDiagonallyDominant hA hdom

/-- A convenient interval form: lower diagonal bounds and upper absolute
bounds imply positive definiteness once every certified lower diagonal is
larger than the certified off-diagonal row sum. -/
theorem posDef_of_entrywise_interval_certificate
    {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (diagLower absUpper : Matrix n n ℝ)
    (hdiag : ∀ i, diagLower i i ≤ A i i)
    (hoff : ∀ i j, i ≠ j → ‖A i j‖ ≤ absUpper i j)
    (hcert : ∀ i, ∑ j ∈ Finset.univ.erase i, absUpper i j < diagLower i i) :
    A.PosDef := by
  apply posDef_of_strictlyRowDiagonallyDominant hA
  intro i
  calc
    offDiagonalRowSum A i
        ≤ ∑ j ∈ Finset.univ.erase i, absUpper i j := by
          apply Finset.sum_le_sum
          intro j hj
          exact hoff i j (Finset.ne_of_mem_erase hj)
    _ < diagLower i i := hcert i
    _ ≤ A i i := hdiag i

end RiemannResearch.RH.StrictDiagonalDominance
