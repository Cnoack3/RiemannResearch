/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

/-!
# Finite triangular matrices and finitely supported eigenvectors

These statements concern finite matrices, or the finite sum defining the action
of an infinite matrix on a finitely supported vector. They make no assertion
that an infinite triangular matrix defines a bounded operator on `ℓ²`.
-/

noncomputable section

open scoped BigOperators
open Matrix

namespace RiemannResearch.TriangularEigenvectors

variable {N : ℕ}

/-- The eigenvalues of a finite upper triangular real matrix are exactly its
diagonal entries. No assumption that the diagonal entries are distinct is used. -/
theorem hasEigenvalue_iff_diagonal
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsUpperTriangular) (μ : ℝ) :
    Module.End.HasEigenvalue A.mulVecLin μ ↔ ∃ i, A i i = μ := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly,
    Matrix.charpoly_mulVecLin, Matrix.charpoly_of_isUpperTriangular A hA]
  simp only [Polynomial.IsRoot, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, Finset.prod_eq_zero_iff,
    Finset.mem_univ, true_and, sub_eq_zero]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, hi.symm⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, hi.symm⟩

/-- Upper triangularity is preserved by the genuine matrix inverse. -/
theorem inverse_isUpperTriangular
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsUpperTriangular)
    (hdet : IsUnit A.det) : A⁻¹.IsUpperTriangular := by
  letI : Invertible A := Matrix.invertibleOfIsUnitDet A hdet
  exact Matrix.blockTriangular_inv_of_blockTriangular hA

/-- The left inverse of a finite upper triangular matrix is upper triangular.
This form is useful when a change-of-basis construction already supplies its
inverse matrix by an identity `B * A = 1`. -/
theorem leftInverse_isUpperTriangular
    (A B : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsUpperTriangular)
    (hBA : B * A = 1) : B.IsUpperTriangular := by
  letI : Invertible A := invertibleOfLeftInverse A B hBA
  have hInv : A⁻¹.IsUpperTriangular :=
    Matrix.blockTriangular_inv_of_blockTriangular hA
  rwa [Matrix.inv_eq_left_inv hBA] at hInv

/-- A nonzero eigenvalue becomes its reciprocal under inversion, with exactly
the same eigenvector. This lemma is about the vector equation. -/
theorem inverse_mulVec_eigen
    (A : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ) (μ : ℝ)
    (hdet : IsUnit A.det) (hμ : μ ≠ 0)
    (hv : A *ᵥ v = μ • v) : A⁻¹ *ᵥ v = μ⁻¹ • v := by
  have h := congrArg (fun u => A⁻¹ *ᵥ u) hv
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hdet,
    Matrix.one_mulVec, Matrix.mulVec_smul] at h
  have hh := congrArg (fun u => μ⁻¹ • u) h
  simpa only [smul_smul, inv_mul_cancel₀ hμ, one_smul] using hh.symm

/-- The reciprocal correspondence of vector equations is an equivalence. -/
theorem inverse_mulVec_eigen_iff
    (A : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ) (μ : ℝ)
    (hdet : IsUnit A.det) (hμ : μ ≠ 0) :
    A⁻¹ *ᵥ v = μ⁻¹ • v ↔ A *ᵥ v = μ • v := by
  constructor
  · intro hv
    have h := inverse_mulVec_eigen A⁻¹ v μ⁻¹
      (Matrix.isUnit_nonsing_inv_det A hdet) (inv_ne_zero hμ) hv
    simpa only [Matrix.nonsing_inv_nonsing_inv A hdet, inv_inv] using h
  · exact inverse_mulVec_eigen A v μ hdet hμ

/-- Inversion preserves the nonzero eigenvectors and reciprocates their
eigenvalues. -/
theorem inverse_hasEigenvector_iff
    (A : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ) (μ : ℝ)
    (hdet : IsUnit A.det) (hμ : μ ≠ 0) :
    Module.End.HasEigenvector (A⁻¹).mulVecLin μ⁻¹ v ↔
      Module.End.HasEigenvector A.mulVecLin μ v := by
  simp only [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff,
    Matrix.mulVecLin_apply]
  exact and_congr (inverse_mulVec_eigen_iff A v μ hdet hμ) Iff.rfl

/-- The nonzero eigenvalues correspond by reciprocation under inversion. -/
theorem inverse_hasEigenvalue_iff
    (A : Matrix (Fin N) (Fin N) ℝ) (μ : ℝ)
    (hdet : IsUnit A.det) (hμ : μ ≠ 0) :
    Module.End.HasEigenvalue (A⁻¹).mulVecLin μ⁻¹ ↔
      Module.End.HasEigenvalue A.mulVecLin μ := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ((inverse_hasEigenvector_iff A v μ hdet hμ).mp hv)
  · intro h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ((inverse_hasEigenvector_iff A v μ hdet hμ).mpr hv)

/-- A genuine eigenvalue of an invertible matrix is nonzero. -/
theorem eigenvalue_ne_zero_of_isUnitDet
    (A : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ) (μ : ℝ)
    (hdet : IsUnit A.det) (hv : Module.End.HasEigenvector A.mulVecLin μ v) : μ ≠ 0 := by
  intro hμ
  have hzero : A *ᵥ v = 0 := by
    simpa only [Matrix.mulVecLin_apply, hμ, zero_smul] using hv.apply_eq_smul
  have h := congrArg (fun u => A⁻¹ *ᵥ u) hzero
  have hvzero : v = 0 := by
    simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hdet,
      Matrix.one_mulVec, Matrix.mulVec_zero] using h
  exact (Module.End.hasEigenvector_iff.mp hv).2 hvzero

/-- The part of a row strictly to the right of its diagonal. -/
def upperTail (A : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ)
    (i : Fin N) : ℝ :=
  ∑ k : Fin N, if i < k then A i k * v k else 0

/-- A row of an upper triangular matrix consists of its diagonal contribution
and the contribution from larger indices. -/
theorem mulVec_eq_diagonal_add_tail
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsUpperTriangular)
    (v : Fin N → ℝ) (i : Fin N) :
    (A *ᵥ v) i = A i i * v i + upperTail A v i := by
  change (∑ k, A i k * v k) = _
  calc
    _ = ∑ k : Fin N,
        ((if k = i then A i i * v i else 0) +
          (if i < k then A i k * v k else 0)) := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hki : k = i
      · subst k
        simp
      by_cases hik : i < k
      · simp [hki, hik]
      · have hlt : k < i := by omega
        simp [hA hlt, hki, hik]
    _ = _ := by simp [Finset.sum_add_distrib, upperTail]

/-- The row equations describe every eigenvector, including cases where a
diagonal value is repeated and backward substitution may have a zero divisor. -/
theorem mulVec_eigen_iff_rowEquations
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsUpperTriangular)
    (v : Fin N → ℝ) (μ : ℝ) :
    A *ᵥ v = μ • v ↔
      ∀ i, (A i i - μ) * v i + upperTail A v i = 0 := by
  constructor
  · intro h i
    have hi := congrFun h i
    rw [mulVec_eq_diagonal_add_tail A hA v i] at hi
    change A i i * v i + upperTail A v i = μ * v i at hi
    nlinarith [hi]
  · intro h
    funext i
    rw [mulVec_eq_diagonal_add_tail A hA v i]
    change A i i * v i + upperTail A v i = μ * v i
    nlinarith [h i]

/-- The complete eigenspace description, with nonzeroness stated explicitly. -/
theorem hasEigenvector_iff_rowEquations
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsUpperTriangular)
    (v : Fin N → ℝ) (μ : ℝ) :
    Module.End.HasEigenvector A.mulVecLin μ v ↔
      (∀ i, (A i i - μ) * v i + upperTail A v i = 0) ∧ v ≠ 0 := by
  simp only [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff,
    Matrix.mulVecLin_apply]
  exact and_congr (mulVec_eigen_iff_rowEquations A hA v μ) Iff.rfl

/-- The usual backward-substitution formula certifies an eigenvector.

Only the entries before the selected diagonal entry need to differ from it.
The sum over all larger indices equals the sum up to `j`, because `hzero`
sets every later coordinate to zero. -/
theorem backSubstitution_isEigenvector
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsUpperTriangular)
    (j : Fin N) (v : Fin N → ℝ)
    (hzero : ∀ i, j < i → v i = 0)
    (hone : v j = 1)
    (hd : ∀ i, i < j → A i i ≠ A j j)
    (hrec : ∀ i, i < j →
      v i = upperTail A v i / (A j j - A i i)) :
    Module.End.HasEigenvector A.mulVecLin (A j j) v := by
  have he : A *ᵥ v = (A j j) • v := by
    funext i
    rw [mulVec_eq_diagonal_add_tail A hA v i]
    change A i i * v i + upperTail A v i = A j j * v i
    rcases lt_trichotomy i j with hij | hij | hji
    · have hden : A j j - A i i ≠ 0 := sub_ne_zero.mpr (Ne.symm (hd i hij))
      have h := (eq_div_iff hden).mp (hrec i hij)
      nlinarith [h]
    · subst i
      have ht : upperTail A v j = 0 := by
        unfold upperTail
        apply Finset.sum_eq_zero
        intro k hk
        by_cases hjk : j < k
        · simp [hjk, hzero k hjk]
        · simp [hjk]
      rw [ht]
      ring
    · have ht : upperTail A v i = 0 := by
        unfold upperTail
        apply Finset.sum_eq_zero
        intro k hk
        by_cases hik : i < k
        · simp [hik, hzero k (lt_trans hji hik)]
        · simp [hik]
      rw [hzero i hji, ht]
      ring
  have hvne : v ≠ 0 := by
    intro h
    have hh := congrFun h j
    simpa only [hone, Pi.zero_apply, one_ne_zero] using hh
  exact ⟨Module.End.mem_eigenspace_iff.mpr he, hvne⟩

/-- Reverse recursion giving the normalized eigenvector for column `j`.
The recursion only calls a larger index, so `N - k` strictly decreases.
Outside the finite matrix, the value is zero. -/
def backwardValue
    (A : Matrix (Fin N) (Fin N) ℝ) (j : Fin N) (k : ℕ) : ℝ :=
  if hk : k < N then
    if k = j.val then 1 else
      if k < j.val then
        (∑ l : Fin N, if hkl : k < l.val then
          A ⟨k, hk⟩ l * backwardValue A j l.val else 0) /
          (A j j - A ⟨k, hk⟩ ⟨k, hk⟩)
      else 0
  else 0
termination_by N - k
decreasing_by omega

/-- The vector obtained from reverse substitution. -/
def backwardVector (A : Matrix (Fin N) (Fin N) ℝ)
    (j : Fin N) (i : Fin N) : ℝ := backwardValue A j i.val

theorem backwardVector_at
    (A : Matrix (Fin N) (Fin N) ℝ) (j : Fin N) :
    backwardVector A j j = 1 := by
  change backwardValue A j j.val = 1
  rw [backwardValue]
  simp [j.isLt]

theorem backwardVector_above
    (A : Matrix (Fin N) (Fin N) ℝ) (j i : Fin N) (h : j < i) :
    backwardVector A j i = 0 := by
  change backwardValue A j i.val = 0
  rw [backwardValue]
  have h' : j.val < i.val := h
  simp [i.isLt, ne_of_gt h', not_lt_of_ge h'.le]

theorem backwardVector_rec
    (A : Matrix (Fin N) (Fin N) ℝ) (j i : Fin N) (h : i < j) :
    backwardVector A j i =
      upperTail A (backwardVector A j) i / (A j j - A i i) := by
  change backwardValue A j i.val = _
  rw [backwardValue]
  have h' : i.val < j.val := h
  simp [i.isLt, ne_of_lt h', h', upperTail, backwardVector]

/-- An explicit eigenvector under the distinct-earlier-diagonal condition. -/
theorem backwardVector_hasEigenvector
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsUpperTriangular)
    (j : Fin N) (hd : ∀ i, i < j → A i i ≠ A j j) :
    Module.End.HasEigenvector A.mulVecLin (A j j) (backwardVector A j) := by
  exact backSubstitution_isEigenvector A hA j (backwardVector A j)
    (fun i hi => backwardVector_above A j i hi)
    (backwardVector_at A j) hd
    (fun i hi => backwardVector_rec A j i hi)

/-- Extend a finite coordinate vector to a sequence by zero. -/
def padFinite (v : Fin N → ℝ) (n : ℕ) : ℝ :=
  if hn : n < N then v ⟨n, hn⟩ else 0

theorem padFinite_ne_zero (v : Fin N → ℝ) (hv : v ≠ 0) :
    padFinite v ≠ 0 := by
  intro h
  apply hv
  funext i
  have hh := congrFun h i.val
  simpa [padFinite, i.isLt] using hh

/-- A finite-section eigenvector of an infinite upper triangular matrix remains
an eigenvector after padding by zero. The action here is explicitly a finite
sum, so this theorem does not assume or assert a bounded operator on `ℓ²`. -/
theorem padded_eigenequation
    (A : ℕ → ℕ → ℝ) (hA : ∀ i j, j < i → A i j = 0)
    (v : Fin N → ℝ) (μ : ℝ)
    (hv : (fun i j : Fin N => A i.val j.val) *ᵥ v = μ • v) :
    ∀ n, (∑ i : Fin N, A n i.val * v i) = μ * padFinite v n := by
  intro n
  by_cases hn : n < N
  · simpa [Matrix.mulVec, dotProduct, padFinite, hn] using congrFun hv ⟨n, hn⟩
  · simp only [padFinite, dif_neg hn, mul_zero]
    apply Finset.sum_eq_zero
    intro i hi
    rw [hA n i.val (lt_of_lt_of_le i.isLt (Nat.le_of_not_gt hn)), zero_mul]

end RiemannResearch.TriangularEigenvectors
