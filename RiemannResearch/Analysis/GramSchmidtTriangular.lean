/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.GramSchmidtCofactors
import RiemannResearch.Analysis.OrthonormalGramChange
import RiemannResearch.LinearAlgebra.TriangularEigenvectors

/-!
# The exact triangular Gram-Schmidt matrix

Source: the user's matrix verification request, 4 November 2026.
Column j has finite support in indices at most j. All finite sections are
compatible, and their identities refer to the full Hilbert Gram matrix.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.GramSchmidtTriangular
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.GramSchmidtCofactors
open RiemannResearch.Analysis.OrthonormalGramChange

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def entry (v : ℕ → H) (i j : ℕ) : ℝ :=
  if h : i ≤ j then coefficient v j ⟨i, by omega⟩ else 0

def forward (v : ℕ → H) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => entry v i.val j.val

def reverse (v : ℕ → H) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  crossMatrix (initialFamily v n) (initialFamily (mode v) n)

theorem entry_above_column (v : ℕ → H) {i j : ℕ} (h : j < i) :
    entry v i j = 0 := by simp [entry, Nat.not_le_of_gt h]

theorem entry_diagonal (v : ℕ → H) (j : ℕ) :
    entry v j j = coefficient v j (Fin.last j) := by
  simp only [entry, dif_pos (le_refl j)]
  rfl

theorem forward_upper (v : ℕ → H) (n : ℕ) : (forward v n).IsUpperTriangular := by
  intro i j h
  exact entry_above_column v h

theorem column_synthesis {v : ℕ → H} (hv : LinearIndependent ℝ v)
    (n : ℕ) (j : Fin n) :
    (∑ i : Fin n, forward v n i j • v i.val) = mode v j.val := by
  let f : ℕ → H := fun k => entry v k j.val • v k
  have hsub : Finset.range (j.val + 1) ⊆ Finset.range n :=
    Finset.range_mono j.isLt
  have heq : (∑ k ∈ Finset.range (j.val + 1), f k) =
      ∑ k ∈ Finset.range n, f k := by
    apply Finset.sum_subset hsub
    intro k hk hnot
    have hjk : j.val < k := by
      simp only [Finset.mem_range] at hnot
      omega
    simp [f, entry_above_column v hjk]
  calc
    _ = ∑ k ∈ Finset.range n, f k := Fin.sum_univ_eq_sum_range f n
    _ = ∑ k ∈ Finset.range (j.val + 1), f k := heq.symm
    _ = ∑ k : Fin (j.val + 1), f k.val :=
      (Fin.sum_univ_eq_sum_range f (j.val + 1)).symm
    _ = ∑ k : Fin (j.val + 1), coefficient v j.val k • v k.val := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [f, entry, Nat.lt_succ_iff.mp k.isLt]
    _ = _ := coefficient_synthesis hv j.val

theorem modes_mem_span {v : ℕ → H} (hv : LinearIndependent ℝ v)
    (n : ℕ) (j : Fin n) :
    initialFamily (mode v) n j ∈ synthesisSpan (initialFamily v n) := by
  rw [show initialFamily (mode v) n j = mode v j.val from rfl,
    ← column_synthesis hv n j]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨i, rfl⟩

theorem modes_orthonormal {v : ℕ → H} (hv : LinearIndependent ℝ v) (n : ℕ) :
    Orthonormal ℝ (initialFamily (mode v) n) :=
  (mode_orthonormal hv).comp (fun i : Fin n => i.val) Fin.val_injective

theorem forward_eq_coefficients {v : ℕ → H} (hv : LinearIndependent ℝ v)
    (n : ℕ) :
    forward v n = coefficients (prefix_independent hv n) (initialFamily (mode v) n) := by
  ext i j
  have h : (fun k => forward v n k j) =
      (fun k => coefficients (prefix_independent hv n) (initialFamily (mode v) n) k j) := by
    apply (prefix_independent hv n).fintypeLinearCombination_injective
    change (∑ k, forward v n k j • v k.val) = _
    rw [column_synthesis hv n j]
    exact (OrthonormalGramChange.column_synthesis
      (prefix_independent hv n) _ (modes_mem_span hv n) j).symm
  exact congrFun h i

theorem reverse_apply (v : ℕ → H) (n : ℕ) (i j : Fin n) :
    reverse v n i j = inner ℝ (mode v i.val) (v j.val) := rfl

theorem reverse_upper {v : ℕ → H} (hv : LinearIndependent ℝ v) (n : ℕ) :
    (reverse v n).IsUpperTriangular := by
  intro i j h
  have h' : j.val < i.val := h
  rw [reverse_apply, real_inner_comm,
    atom_inner_mode hv i.val j.val h'.le, if_neg (Nat.ne_of_lt h')]

theorem forward_inverse {v : ℕ → H} (hv : LinearIndependent ℝ v) (n : ℕ) :
    (forward v n)⁻¹ = reverse v n := by
  rw [forward_eq_coefficients hv]
  exact coefficients_inverse (prefix_independent hv n)
    (modes_orthonormal hv n) (modes_mem_span hv n)

theorem reverse_inverse {v : ℕ → H} (hv : LinearIndependent ℝ v) (n : ℕ) :
    (reverse v n)⁻¹ = forward v n := by
  rw [forward_eq_coefficients hv]
  exact cross_inverse (prefix_independent hv n)
    (modes_orthonormal hv n) (modes_mem_span hv n)

theorem inverse_eq_transpose_mul_gram {v : ℕ → H} (hv : LinearIndependent ℝ v)
    (n : ℕ) : (forward v n)⁻¹ = (forward v n).transpose * gram v n := by
  rw [forward_inverse hv, forward_eq_coefficients hv]
  exact (transpose_coefficients_mul_gram (prefix_independent hv n)
    _ (modes_mem_span hv n)).symm

theorem orthonormal_identity {v : ℕ → H} (hv : LinearIndependent ℝ v)
    (n : ℕ) : (forward v n).transpose * gram v n * forward v n = 1 := by
  rw [forward_eq_coefficients hv]
  exact orthonormal_gram_identity (prefix_independent hv n)
    (modes_orthonormal hv n) (modes_mem_span hv n)

theorem gram_factorization {v : ℕ → H} (hv : LinearIndependent ℝ v)
    (n : ℕ) : gram v n = (reverse v n).transpose * reverse v n :=
  gram_eq_transpose_cross_mul_cross (prefix_independent hv n)
    (modes_orthonormal hv n) (modes_mem_span hv n)

theorem diagonal_reciprocal {v : ℕ → H} (hv : LinearIndependent ℝ v) (j : ℕ) :
    entry v j j = (scale v j)⁻¹ := by
  rw [entry_diagonal, ← one_div]
  exact (eq_div_iff (ne_of_gt (scale_pos hv j))).mpr
    (coefficient_diagonal_mul_scale hv j)

theorem diagonal_det_ratio {v : ℕ → H} (hv : LinearIndependent ℝ v) (j : ℕ) :
    entry v j j = Real.sqrt ((gram v j).det / (gram v (j + 1)).det) := by
  rw [entry_diagonal, coefficient_diagonal_eq_sqrt_det_ratio hv]

theorem entry_cofactor {v : ℕ → H} (hv : LinearIndependent ℝ v)
    (i j : ℕ) (hij : i ≤ j) :
    entry v i j =
      (gram v (j + 1)).adjugate ⟨i, by omega⟩ (Fin.last j) /
        Real.sqrt ((gram v j).det * (gram v (j + 1)).det) := by
  simp only [entry, dif_pos hij]
  exact coefficient_eq_normalized_adjugate hv j _

theorem eigenvalue_iff_det_ratio {v : ℕ → H} (hv : LinearIndependent ℝ v)
    (n : ℕ) (μ : ℝ) :
    Module.End.HasEigenvalue (forward v n).mulVecLin μ ↔
      ∃ j : Fin n, Real.sqrt ((gram v j.val).det / (gram v (j.val + 1)).det) = μ := by
  rw [RiemannResearch.TriangularEigenvectors.hasEigenvalue_iff_diagonal
    (forward v n) (forward_upper v n)]
  simp only [forward, diagonal_det_ratio hv]

end RiemannResearch.Analysis.GramSchmidtTriangular
