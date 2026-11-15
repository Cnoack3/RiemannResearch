/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.LinearAlgebra.RationalLinearSolveCertificate
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Linarith

/-!
# Sound rational congruence certificates for positive definiteness

Source: numerical spectral certificates in the user's reciprocal-head review.
The proof strategy is the repository's strict diagonal-dominance/Gershgorin
argument, after an independently supplied rational invertible congruence.
Any external factorization proposes witnesses only. A rational right inverse
and all interval row inequalities are checked by the Lean kernel.
-/

noncomputable section
open scoped BigOperators
open Matrix WithLp

namespace RiemannResearch.RatInterval
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def congruence (A : Matrix ι ι RatInterval) (T : Matrix ι ι ℚ) (i j : ι) :
    RatInterval :=
  sum Finset.univ (fun k => sum Finset.univ
    (fun l => mul (mul (point (T i k)) (A k l)) (point (T j l))))

theorem congruence_contains
    (AI : Matrix ι ι RatInterval) (A : Matrix ι ι ℝ) (T : Matrix ι ι ℚ)
    (hA : ∀ i j, (AI i j).Contains (A i j)) (i j : ι) :
    (congruence AI T i j).Contains
      (((Matrix.of fun i j => (T i j : ℝ)) * A * star (Matrix.of fun i j => (T i j : ℝ))) i j) := by
  have hc : (congruence AI T i j).Contains
      (∑ k, ∑ l, (T i k : ℝ) * A k l * (T j l : ℝ)) := by
    apply contains_sum
    intro k _
    apply contains_sum
    intro l _
    exact contains_mul (contains_mul (contains_point _) (hA k l)) (contains_point _)
  have he : (((Matrix.of fun i j => (T i j : ℝ)) * A *
      star (Matrix.of fun i j => (T i j : ℝ))) i j) =
      ∑ k, ∑ l, (T i k : ℝ) * A k l * (T j l : ℝ) := by
    simp only [Matrix.mul_apply, Matrix.star_apply, star_trivial, Finset.sum_mul]
    exact Finset.sum_comm
  rw [he]
  exact hc

/-- A rational right inverse is a fully checkable witness of invertibility
of the actual real congruence matrix. -/
theorem cast_matrix_isUnit_of_right_inverse
    (T S : Matrix ι ι ℚ) (hTS : T * S = 1) :
    IsUnit (Matrix.of fun i j => (T i j : ℝ)) := by
  let T' : Matrix ι ι ℝ := Matrix.of fun i j => (T i j : ℝ)
  let S' : Matrix ι ι ℝ := Matrix.of fun i j => (S i j : ℝ)
  have hTS' : T' * S' = 1 := by
    ext i j
    have he := congrArg (fun M : Matrix ι ι ℚ => (M i j : ℝ)) hTS
    simp only [Matrix.mul_apply, Matrix.one_apply] at he ⊢
    push_cast at he
    simpa [T', S', apply_ite] using he
  exact (Matrix.isUnit_iff_isUnit_det T').mpr
    (Matrix.isUnit_det_of_right_inverse hTS')

/-- The exact finite rational acceptance predicate. -/
def CongruenceDominates (AI : Matrix ι ι RatInterval) (T : Matrix ι ι ℚ) : Prop :=
  ∀ i, (∑ j ∈ Finset.univ.erase i, absBound (congruence AI T i j)) <
    (congruence AI T i i).lo

/-- Positive-definiteness from actual entry enclosures, a rational invertible
congruence, and kernel-checkable strict row-dominance inequalities. -/
theorem posDef_of_congruence_certificate
    (AI : Matrix ι ι RatInterval) (A : Matrix ι ι ℝ)
    (T S : Matrix ι ι ℚ) (hA : A.IsHermitian)
    (hAI : ∀ i j, (AI i j).Contains (A i j))
    (hTS : T * S = 1) (hcert : CongruenceDominates AI T) : A.PosDef := by
  let T' : Matrix ι ι ℝ := Matrix.of fun i j => (T i j : ℝ)
  let B : Matrix ι ι ℝ := T' * A * star T'
  have hT : IsUnit T' := cast_matrix_isUnit_of_right_inverse T S hTS
  apply (hT.posDef_star_right_conjugate_iff).1
  have hB : B.IsHermitian := by
    simpa only [B, Matrix.star_eq_conjTranspose] using
      Matrix.isHermitian_mul_mul_conjTranspose T' hA
  change B.PosDef
  rw [hB.posDef_iff_eigenvalues_pos]
  intro i
  have hEig : Module.End.HasEigenvalue (Matrix.toLin' B) (hB.eigenvalues i) := by
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨by
        rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
        exact hB.mulVec_eigenvectorBasis i,
       (ofLp_eq_zero 2).ne.2 <| hB.eigenvectorBasis.orthonormal.ne_zero i⟩
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball hEig
  rw [mem_closedBall_iff_norm'] at hk
  have habs : |B k k - hB.eigenvalues i| ≤
      ∑ j ∈ Finset.univ.erase k, ‖B k j‖ := by
    simpa only [Real.norm_eq_abs] using hk
  have hrow : (∑ j ∈ Finset.univ.erase k, ‖B k j‖) ≤
      ∑ j ∈ Finset.univ.erase k, (absBound (congruence AI T k j) : ℝ) := by
    apply Finset.sum_le_sum
    intro j _
    simpa [B, T', Real.norm_eq_abs] using
      abs_le_absBound (congruence_contains AI A T hAI k j)
  have hcertR : (∑ j ∈ Finset.univ.erase k,
      (absBound (congruence AI T k j) : ℝ)) <
      ((congruence AI T k k).lo : ℝ) := by
    exact_mod_cast hcert k
  have hdiag : ((congruence AI T k k).lo : ℝ) ≤ B k k :=
    (congruence_contains AI A T hAI k k).1
  linarith [(abs_le.mp habs).2]

end RiemannResearch.RatInterval
