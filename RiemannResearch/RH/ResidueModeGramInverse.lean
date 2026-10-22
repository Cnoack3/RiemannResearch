import RiemannResearch.RH.ResidueGramCofactors

/-!
# Inverse Gram matrix in orthonormal residue coordinates

Source: user-provided Mellin DPP construction, 20 September 2026.
This finite change-of-basis identity identifies the actual inverse-Gram
kernel with the sum of the actual Gram--Schmidt mode kernels.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.Analysis.FiniteHilbertGram
open IntegerDPP

def modeMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun j i => modeCoefficient (i.val + 2) j.val

theorem residueMode_expansion_finite (n : ℕ) (j : Fin n) :
    residueMode j.val = ∑ i : Fin n, modeMatrix n j i • residueAtom i.val := by
  have hm : residueMode j.val ∈ finiteSpace n := by
    rw [← residueMode_finiteSpace n]
    exact Submodule.subset_span ⟨j, rfl⟩
  obtain ⟨a, ha⟩ := finiteSpace_expansion n (residueMode j.val) hm
  have hc : a = fun i => modeMatrix n j i := by
    funext i
    have he := congrArg (coefficientCLM (i.val + 2)) ha
    rw [coefficient_finite_sum] at he
    exact he.symm
  simpa only [hc] using ha

theorem modeMatrix_gram (n : ℕ) :
    modeMatrix n * fullGram n * (modeMatrix n).transpose = 1 := by
  ext i j
  have hinner : inner ℝ (residueMode i.val) (residueMode j.val) =
      if i = j then 1 else 0 := by
    simpa only [Fin.val_inj] using (orthonormal_iff_ite.mp residueMode_orthonormal) i.val j.val
  rw [residueMode_expansion_finite n i, residueMode_expansion_finite n j] at hinner
  simp only [sum_inner, inner_sum, real_inner_smul_left, inner_smul_right,
    Finset.mul_sum] at hinner
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
    fullGram, RiemannResearch.Analysis.FiniteHilbertGram.gramMatrix,
    Finset.sum_mul]
  convert hinner using 1
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem fullGram_inverse_eq_modeMatrix (n : ℕ) :
    (fullGram n)⁻¹ = (modeMatrix n).transpose * modeMatrix n := by
  have h := modeMatrix_gram n
  rw [Matrix.mul_assoc] at h
  have h' := mul_eq_one_comm.mp h
  rw [Matrix.mul_assoc] at h'
  exact Matrix.inv_eq_right_inv h'

end RiemannResearch.RH.Pareto.CoefficientStabilization
