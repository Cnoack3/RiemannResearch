/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
/-!
# A full matrix algebra with nonzero metric displacement

RH consumer: QSquarefreeSchurOperator and QSquarefreeCRTRegularity.
This exact two-dimensional model rules out an inference of projection
agreement from positivity, a strict feedback contraction, and a scalar
joint commutant alone. It does not model the squarefree arithmetic identities.

The generators are P=diag(1,0) and B=[[1/4,1/8],[1/8,1/4]].
Their unital algebra is the entire matrix algebra over any characteristic-zero
field, including the complex numbers. For the target (1,1), the ordinary and
(I-B)-metric best coefficients on the first axis are 1 and 5/6.
The exact completed squares certify the discrepancy.

Source: independent finite diagnostic for the user's operator-algebra agenda,
cross-checked in Wolfram Language on 4 November 2026. No novelty is claimed.
For the distinction between irreducible operator algebras and properties of
particular vectors, see M. Rieffel, C-star Algebras (2008), notes by
T. Johnson-Freyd, sections 15.1-15.2:
https://categorified.net/CstarAlgebras.pdf.
That source supports the operator-algebra background, not this arithmetic
diagnostic or an RH conclusion.
-/

noncomputable section
namespace RiemannResearch.Analysis.SchurDisplacementCountermodel
def projection (K : Type*) [Field K] : Matrix (Fin 2) (Fin 2) K :=
  !![1, 0; 0, 0]
def feedback (K : Type*) [Field K] : Matrix (Fin 2) (Fin 2) K :=
  !![1/4, 1/8; 1/8, 1/4]
theorem matrix_decomposition {K : Type*} [Field K] [CharZero K]
    (M : Matrix (Fin 2) (Fin 2) K) :
    M = M 0 0 • projection K + M 1 1 • (1 - projection K) +
      (8 * M 0 1) • (projection K * feedback K * (1 - projection K)) +
      (8 * M 1 0) • ((1 - projection K) * feedback K * projection K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [projection, feedback, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_two] <;> ring
theorem algebra_eq_top_of_contains {K : Type*} [Field K] [CharZero K]
    (S : Subalgebra K (Matrix (Fin 2) (Fin 2) K))
    (hp : projection K ∈ S) (hb : feedback K ∈ S) : S = ⊤ := by
  apply top_unique
  intro M hM
  rw [matrix_decomposition M]
  have hn := S.sub_mem S.one_mem hp
  exact S.add_mem
    (S.add_mem
      (S.add_mem (S.toSubmodule.smul_mem _ hp) (S.toSubmodule.smul_mem _ hn))
      (S.toSubmodule.smul_mem _ (S.mul_mem (S.mul_mem hp hb) hn)))
    (S.toSubmodule.smul_mem _ (S.mul_mem (S.mul_mem hn hb) hp))
theorem joint_commutant_scalar {K : Type*} [Field K] [CharZero K]
    (M : Matrix (Fin 2) (Fin 2) K)
    (hp : M * projection K = projection K * M)
    (hb : M * feedback K = feedback K * M) :
    ∃ c : K, M = c • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 0 1) hp
  have h10 := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 1 0) hp
  have hd := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 0 1) hb
  simp [projection, feedback, Matrix.mul_apply, Fin.sum_univ_two] at h01 h10 hd
  have he : M 1 1 = M 0 0 := by linear_combination -8 * hd
  refine ⟨M 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01.symm, h10, he]
def bForm (x y : ℝ) : ℝ := x^2/4 + x*y/4 + y^2/4
def metricForm (x y : ℝ) : ℝ := x^2+y^2-bForm x y
theorem bForm_squares (x y : ℝ) :
    bForm x y = (3/16:ℝ)*(x+y)^2+(1/16:ℝ)*(x-y)^2 := by
  unfold bForm
  ring
theorem metricForm_squares (x y : ℝ) :
    metricForm x y = (5/16:ℝ)*(x+y)^2+(7/16:ℝ)*(x-y)^2 := by
  unfold metricForm bForm
  ring
theorem feedback_contraction_gap (x y : ℝ) :
    (9/64:ℝ)*(x^2+y^2) -
      ((x/4+y/8)^2+(x/8+y/4)^2) = (1/16:ℝ)*(x-y)^2 := by ring
theorem metric_projection_gap (t : ℝ) :
    metricForm (1-t) 1 = (35/48:ℝ)+(3/4:ℝ)*(t-5/6)^2 := by
  unfold metricForm bForm
  ring
theorem ordinary_projection_gap (t : ℝ) :
    (1-t)^2+1 = 1+(t-1)^2 := by ring
theorem schur_completion (x y : ℝ) :
    bForm y x - y^2 =
      (13/48:ℝ)*x^2-(3/4:ℝ)*(y-x/6)^2 := by
  unfold bForm
  ring
theorem displacement_nonzero :
    (1-(5/6:ℝ)) = (1/6:ℝ) ∧ (1-(5/6:ℝ)) ≠ 0 := by norm_num
theorem projection_idempotent {K : Type*} [Field K] :
    projection K * projection K = projection K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [projection, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
theorem feedback_transpose {K : Type*} [Field K] :
    (feedback K).transpose = feedback K := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl
theorem bForm_lower_gap (x y : ℝ) :
    bForm x y - (1/8:ℝ)*(x^2+y^2) = (1/8:ℝ)*(x+y)^2 := by
  unfold bForm
  ring
theorem bForm_upper_gap (x y : ℝ) :
    (3/8:ℝ)*(x^2+y^2) - bForm x y = (1/8:ℝ)*(x-y)^2 := by
  unfold bForm
  ring
theorem displacement_normal_equation :
    (1-(1/4:ℝ))*(1-(5/6:ℝ)) = (1/8:ℝ) := by norm_num
end RiemannResearch.Analysis.SchurDisplacementCountermodel
