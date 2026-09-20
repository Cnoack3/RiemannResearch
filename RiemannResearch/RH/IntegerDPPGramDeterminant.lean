import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import RiemannResearch.RH.IntegerDPPExistence
import RiemannResearch.RH.IntegerDPPWindow

/-!
# Arithmetic Gram determinants and finite-window gaps

Source: user-provided DPP/Fredholm conversation, 20 September 2026.
The matrices contain the actual complete Pareto inner products, including all
tail and mixed terms. At z = 1 the real-parameter determinant polynomial is
the actual first-site vacancy. This is a finite determinant computation, not
a construction of general infinite-dimensional Fredholm determinants.
The vanishing determinant ratio implies Mathlib's RiemannHypothesis; no
vanishing assertion or RH-to-density converse is assumed.
-/

namespace RiemannResearch.RH.Pareto.IntegerDPP
noncomputable section
open Filter
open scoped Topology BigOperators
open CoefficientStabilization CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.FiniteHilbertGram

def fullGram (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  gramMatrix (fun i : Fin n => residueAtom i.val)
def tailGram (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  gramMatrix (fun i : Fin n => tailAtom i.val)

theorem fullGram_det_pos (n : ℕ) : 0 < (fullGram n).det :=
  gramMatrix_det_pos (finiteAtom_independent n)
theorem tailGram_det_pos (n : ℕ) : 0 < (tailGram n).det :=
  gramMatrix_det_pos (finiteTailAtom_independent n)

theorem fullGram_eq_tailGram_update (n : ℕ) :
    fullGram n = tailGram n + (1 / 2 : ℝ) •
      Matrix.vecMulVec (reciprocalSource n) (reciprocalSource n) := by
  ext i j
  simp only [fullGram, tailGram, gramMatrix, tailAtom, tailMap_inner,
    residueAtom_evaluation, reciprocalSource, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec, Matrix.of_apply]
  ring

theorem fullGram_det_eq (n : ℕ) :
    (fullGram n).det = (tailGram n).det * (1 + tailCapacity n / 2) := by
  rw [fullGram_eq_tailGram_update]
  have h := gramMatrix_det_update (finiteTailAtom_independent n)
    (reciprocalSource n) (1 / 2 : ℝ)
  simpa only [tailGram, tailCapacity, one_div, div_eq_mul_inv, mul_comm, one_mul] using h

theorem gram_det_ratio_eq_vacancy (n : ℕ) :
    (tailGram n).det / (fullGram n).det = vacancy n := by
  rw [fullGram_det_eq, vacancy_eq_capacity]
  have ht := ne_of_gt (tailGram_det_pos n)
  have hc : tailCapacity n + 2 ≠ 0 := by linarith [tailCapacity_nonneg n]
  have hc' : 2 + tailCapacity n ≠ 0 := by linarith [tailCapacity_nonneg n]
  have hd : 1 + tailCapacity n / 2 ≠ 0 := by linarith [tailCapacity_nonneg n]
  field_simp [ht, hc, hc', hd]
  ring

def headDeterminant (n : ℕ) (z : ℝ) : ℝ :=
  (fullGram n - (z / 2) • Matrix.vecMulVec (reciprocalSource n)
    (reciprocalSource n)).det / (fullGram n).det

theorem headDeterminant_eq (n : ℕ) (z : ℝ) :
    headDeterminant n z = 1 - z * fullCapacity n / 2 := by
  have he : fullGram n - (z / 2) •
      Matrix.vecMulVec (reciprocalSource n) (reciprocalSource n) =
      fullGram n + (-(z / 2)) •
      Matrix.vecMulVec (reciprocalSource n) (reciprocalSource n) := by
    rw [neg_smul, sub_eq_add_neg]
  unfold headDeterminant
  rw [he]
  have h := gramMatrix_det_update (finiteAtom_independent n)
    (reciprocalSource n) (-(z / 2))
  change (fullGram n + _).det = (fullGram n).det *
    (1 + (-(z / 2)) * fullCapacity n) at h
  rw [h]
  have hg := ne_of_gt (fullGram_det_pos n)
  field_simp
  ring

theorem headDeterminant_one (n : ℕ) : headDeterminant n 1 = vacancy n := by
  rw [headDeterminant_eq, vacancy_eq_fullCapacity, one_mul]

theorem determinant_ratio_zero_iff_capacity :
    Tendsto (fun n => (tailGram n).det / (fullGram n).det) atTop (𝓝 0) ↔
      Tendsto tailCapacity atTop atTop := by
  simp_rw [gram_det_ratio_eq_vacancy]
  exact vacancy_tendsto_zero_iff

theorem riemannHypothesis_of_determinant_ratio_zero
    (h : Tendsto (fun n => (tailGram n).det / (fullGram n).det) atTop (𝓝 0)) :
    RiemannHypothesis :=
  riemannHypothesis_of_tailCapacity_tendsto (determinant_ratio_zero_iff_capacity.mp h)

theorem integerLaw_first_site_gram_determinant (n : ℕ) :
    (integerLaw n).real {x | x 0 = false} =
      (tailGram n).det / (fullGram n).det := by
  rw [integerLaw_first_site_vacancy, gram_det_ratio_eq_vacancy]
end
end RiemannResearch.RH.Pareto.IntegerDPP
namespace RiemannResearch.RH.Pareto.IntegerDPP
noncomputable section
open CoefficientStabilization
open CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.FiniteHilbertGram
open scoped BigOperators

def windowFeatures (N m : ℕ) (e : Fin m → ℕ) : Matrix (Fin m) (Fin N) ℝ :=
  observationMatrix (fun k : Fin N => residueAtom k.val) (fun i => countingBasis (e i))

def windowGram (N m : ℕ) (e : Fin m → ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  (windowFeatures N m e).transpose * windowFeatures N m e

theorem integerKernel_window_matrix (N m : ℕ) (e : Fin m → ℕ) :
    Matrix.of (fun i j => integerKernel N (e i) (e j)) =
      windowFeatures N m e * (fullGram N)⁻¹ * (windowFeatures N m e).transpose := by
  exact projection_kernel_matrix (finiteAtom_independent N) (fun i => countingBasis (e i))

theorem window_determinant_eq_gram_ratio (N m : ℕ) (e : Fin m → ℕ) (z : ℝ) :
    (1 - z • Matrix.of (fun i j => integerKernel N (e i) (e j))).det =
      (fullGram N - z • windowGram N m e).det / (fullGram N).det := by
  have h := Matrix.det_sub_mul_div (fullGram N)
    (isUnit_iff_ne_zero.mpr (ne_of_gt (fullGram_det_pos N)))
    (z • (windowFeatures N m e).transpose) (windowFeatures N m e)
  rw [Matrix.smul_mul, Matrix.mul_smul] at h
  rw [integerKernel_window_matrix]
  exact h.symm

end
end RiemannResearch.RH.Pareto.IntegerDPP

namespace RiemannResearch.RH.Pareto.IntegerDPP

/-- Full finite-window gap probability as a ratio of actual Gram determinants. -/
theorem integerLaw_window_gram_determinant (N m : ℕ) (e : Fin m ↪ ℕ) :
    (integerLaw N).real {x | ∀ i, x (e i) = false} =
      (fullGram N - windowGram N m e).det / (fullGram N).det := by
  rw [integerLaw_finite_gap]
  simpa only [one_smul] using window_determinant_eq_gram_ratio N m e 1

end RiemannResearch.RH.Pareto.IntegerDPP
