import RiemannResearch.RH.ConditionalResidueGram
import RiemannResearch.RH.FiniteResidueHeadSurjectivity
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The actual full-row-rank head matrix and exact signed head/tail split

Source: `ArithmeticVariationalProof.md`, Sections 4--6; user-provided
conditional-iid completion, Section 11. All matrices use the concrete
arithmetic residue means. Full row rank follows from the proved finite
interpolation construction. The decomposition keeps every signed entry.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.RH.Pareto
open Analysis.Cesaro Probability.ConditionalIID ArithmeticCumulative

def conditionalResidueHeadMatrix (N : ℕ) (s : Finset ℕ) : Matrix (Fin N) s ℝ :=
  fun t d => cesaro (residue d.1) (t.1 + 1)

theorem finiteResidueSubspace_eq_span_range (D : ℕ) :
    finiteResidueSubspace D =
      Submodule.span ℝ (Set.range (fun d : Finset.Icc 2 D => residue d.1)) := by
  unfold finiteResidueSubspace
  congr 1
  ext f
  constructor
  · rintro ⟨d, hd, hdD, rfl⟩
    exact ⟨⟨d, Finset.mem_Icc.mpr ⟨hd, hdD⟩⟩, rfl⟩
  · rintro ⟨d, rfl⟩
    exact ⟨d.1, (Finset.mem_Icc.mp d.2).1, (Finset.mem_Icc.mp d.2).2, rfl⟩

/-- Surjectivity of the actual coefficient matrix, with no rank premise. -/
theorem conditionalResidueHeadMatrix_surjective (N D : ℕ) (hND : N + 1 ≤ D) :
    Function.Surjective (conditionalResidueHeadMatrix N (Finset.Icc 2 D)).mulVec := by
  classical
  intro b
  obtain ⟨f, hf⟩ := finiteResidue_cesaro_head_surjective N D hND b
  have hfm : f.1 ∈ Submodule.span ℝ
      (Set.range (fun d : Finset.Icc 2 D => residue d.1)) := by
    rw [← finiteResidueSubspace_eq_span_range]
    exact f.2
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hfm
  refine ⟨c, ?_⟩
  funext i
  have hseq : (fun n => ∑ d : Finset.Icc 2 D, c d * residue d.1 n) = f.1 := by
    funext n
    have h := congrFun hc n
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h
  have hmean := congrFun hf i
  change cesaro f.1 (i.1 + 1) = b i at hmean
  rw [← hseq, cesaro_finsetCombination] at hmean
  simpa only [conditionalResidueHeadMatrix, Matrix.mulVec, dotProduct, mul_comm] using hmean

def conditionalResidueHeadGram (N : ℕ) (s : Finset ℕ) : Matrix s s ℝ :=
  fun i j => ∑ t : Fin N, conditionalWeight t.1 *
    (cesaro (residue i.1) (t.1 + 1) * cesaro (residue j.1) (t.1 + 1))

/-- The compulsory finite head is precisely `Aᵀ diag(q) A`. -/
theorem conditionalResidueHeadGram_eq_matrix_product (N : ℕ) (s : Finset ℕ) :
    conditionalResidueHeadGram N s =
      (conditionalResidueHeadMatrix N s).transpose *
        Matrix.diagonal (fun t : Fin N => conditionalWeight t.1) *
          conditionalResidueHeadMatrix N s := by
  classical
  ext i j
  rw [Matrix.mul_assoc]
  simp [conditionalResidueHeadGram, conditionalResidueHeadMatrix, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.diagonal_apply, mul_assoc, mul_left_comm, mul_comm]

/-- Exact full signed matrix decomposition, justified by entrywise summability. -/
theorem conditionalResidueGramMatrix_eq_head_add_tail (N : ℕ) (s : Finset ℕ)
    (hs : ∀ d ∈ s, 2 ≤ d) :
    conditionalResidueGramMatrix s =
      conditionalResidueHeadGram N s + conditionalResidueTailMatrix N s := by
  ext i j
  have hsum : Summable (fun k : ℕ => conditionalWeight k *
      (cesaro (residue i.1) (k + 1) * cesaro (residue j.1) (k + 1))) := by
    simpa only [Nat.add_zero] using conditionalResidueTailMatrix_entry_summable 0 s hs i j
  have he := hsum.sum_add_tsum_nat_add N
  change (∑ k ∈ Finset.range N, conditionalWeight k *
      (cesaro (residue i.1) (k + 1) * cesaro (residue j.1) (k + 1))) +
      conditionalResidueTailMatrix N s i j = conditionalResidueGramMatrix s i j at he
  change conditionalResidueGramMatrix s i j =
    conditionalResidueHeadGram N s i j + conditionalResidueTailMatrix N s i j
  have hfin : conditionalResidueHeadGram N s i j =
      ∑ k ∈ Finset.range N, conditionalWeight k *
        (cesaro (residue i.1) (k + 1) * cesaro (residue j.1) (k + 1)) :=
    Fin.sum_univ_eq_sum_range (fun k => conditionalWeight k *
      (cesaro (residue i.1) (k + 1) * cesaro (residue j.1) (k + 1))) N
  exact he.symm.trans (congrArg (fun r : ℝ => r + conditionalResidueTailMatrix N s i j)
    hfin.symm)

theorem conditionalResidueGramMatrix_eq_weighted_head_add_tail (N : ℕ) (s : Finset ℕ)
    (hs : ∀ d ∈ s, 2 ≤ d) :
    conditionalResidueGramMatrix s =
      (conditionalResidueHeadMatrix N s).transpose *
        Matrix.diagonal (fun t : Fin N => conditionalWeight t.1) *
          conditionalResidueHeadMatrix N s + conditionalResidueTailMatrix N s := by
  rw [conditionalResidueGramMatrix_eq_head_add_tail N s hs,
    conditionalResidueHeadGram_eq_matrix_product]

end RiemannResearch.RH.Pareto
