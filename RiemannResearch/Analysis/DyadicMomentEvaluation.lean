import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

/-!
# Finite polynomial evaluation for dyadic moment matching

Source: `RH_Ramanujan_Laguerre_Schur_Continuation_20260911.md`, §6.
This module proves the finite algebra in its feasibility argument: a triangular
polynomial coefficient matrix with nonzero diagonal, evaluated at distinct
nodes, is invertible. The dyadic specialization proves that the advertised
leading coefficients are nonzero and solves every finite constraint vector.

The actual arithmetic Laguerre coefficient identity and integrability are not
assumed globally or established here. They remain explicit inputs when this
finite result is applied to the arithmetic packets. No norm bound follows from
finite invertibility.
-/

noncomputable section
open scoped BigOperators Matrix

namespace RiemannResearch.Analysis.DyadicMomentEvaluation

/-- Row `j` is the polynomial with coefficient row `C j`; columns are nodes. -/
def evaluationMatrix {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  C * (Matrix.vandermonde x).transpose

@[simp] theorem evaluationMatrix_apply {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) (j v : Fin n) :
    evaluationMatrix C x j v = ∑ i : Fin n, C j i * x v ^ (i : ℕ) := by
  simp [evaluationMatrix, Matrix.mul_apply, Matrix.vandermonde_apply]

/-- Exact determinant factorization retains the coefficient scaling. -/
theorem det_evaluationMatrix {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (hC : C.IsLowerTriangular) :
    (evaluationMatrix C x).det =
      (∏ i : Fin n, C i i) * (Matrix.vandermonde x).det := by
  rw [evaluationMatrix, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_of_isLowerTriangular C hC]

theorem det_evaluationMatrix_ne_zero {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (hC : C.IsLowerTriangular) (hdiag : ∀ i, C i i ≠ 0)
    (hx : Function.Injective x) : (evaluationMatrix C x).det ≠ 0 := by
  rw [det_evaluationMatrix C x hC]
  apply mul_ne_zero
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => hdiag i)
  · exact Matrix.det_vandermonde_ne_zero_iff.mpr hx

/-- An actual finite coefficient vector solving all evaluation constraints. -/
theorem exists_coefficients {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (hC : C.IsLowerTriangular) (hdiag : ∀ i, C i i ≠ 0)
    (hx : Function.Injective x) (target : Fin n → ℝ) :
    ∃ c : Fin n → ℝ, ∀ j,
      ∑ v : Fin n, (∑ i : Fin n, C j i * x v ^ (i : ℕ)) * c v = target j := by
  let A := evaluationMatrix C x
  have hA : IsUnit A.det :=
    isUnit_iff_ne_zero.mpr (det_evaluationMatrix_ne_zero C x hC hdiag hx)
  refine ⟨A⁻¹.mulVec target, ?_⟩
  have heq : A.mulVec (A⁻¹.mulVec target) = target := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hA, Matrix.one_mulVec]
  intro j
  simpa only [Matrix.mulVec, dotProduct, A, evaluationMatrix_apply] using congrFun heq j

/-- The advertised degree-j leading coefficient for the dyadic blocks. -/
def dyadicLeading (j : ℕ) : ℝ :=
  Real.log 2 * (-Real.log 2) ^ j / (j.factorial : ℝ)

theorem dyadicLeading_ne_zero (j : ℕ) : dyadicLeading j ≠ 0 := by
  have hl : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  unfold dyadicLeading
  exact div_ne_zero (mul_ne_zero hl (pow_ne_zero _ (neg_ne_zero.mpr hl)))
    (by exact_mod_cast Nat.factorial_ne_zero j)

/-- Distinct integral nodes v=0,...,K solve every finite moment prescription
whenever the actual coefficient polynomials have the asserted triangular form. -/
theorem exists_dyadic_coefficients (K : ℕ)
    (C : Matrix (Fin (K + 1)) (Fin (K + 1)) ℝ)
    (hC : C.IsLowerTriangular)
    (hdiag : ∀ j, C j j = dyadicLeading j)
    (target : Fin (K + 1) → ℝ) :
    ∃ c : Fin (K + 1) → ℝ, ∀ j,
      ∑ v : Fin (K + 1),
        (∑ i : Fin (K + 1), C j i * (v : ℝ) ^ (i : ℕ)) * c v = target j := by
  apply exists_coefficients C (fun v => (v : ℝ)) hC
  · intro j
    rw [hdiag j]
    exact dyadicLeading_ne_zero j
  · intro i j hij
    apply Fin.ext
    change (i.val : ℝ) = (j.val : ℝ) at hij
    exact_mod_cast hij

/-- Functional version: the solved coefficients are a finite linear
combination of the supplied vectors. The coefficient identity is explicit. -/
theorem exists_finite_moment_match
    {E : Type*} [AddCommGroup E] [Module ℝ E] (K : ℕ)
    (b : Fin (K + 1) → E) (ell : Fin (K + 1) → E →ₗ[ℝ] ℝ)
    (C : Matrix (Fin (K + 1)) (Fin (K + 1)) ℝ)
    (hC : C.IsLowerTriangular) (hdiag : ∀ j, C j j = dyadicLeading j)
    (heval : ∀ j v, ell j (b v) =
      ∑ i : Fin (K + 1), C j i * (v : ℝ) ^ (i : ℕ))
    (target : Fin (K + 1) → ℝ) :
    ∃ c : Fin (K + 1) → ℝ, ∀ j,
      ell j (∑ v : Fin (K + 1), c v • b v) = target j := by
  obtain ⟨c, hc⟩ := exists_dyadic_coefficients K C hC hdiag target
  refine ⟨c, fun j => ?_⟩
  simpa only [map_sum, map_smul, smul_eq_mul, heval, mul_comm] using hc j

end RiemannResearch.Analysis.DyadicMomentEvaluation
