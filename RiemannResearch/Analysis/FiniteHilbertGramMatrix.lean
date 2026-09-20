import RiemannResearch.Analysis.FiniteGramCapacity
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Misc
/-!
# Matrix determinants of finite Hilbert Gram forms

Source: user-provided orthonormal/DPP/Fredholm argument, 20 September 2026,
for the requested identities. The determinant update is the standard matrix
determinant lemma, proved using Mathlib's finite rank determinant theorem.
Independence proves positivity and identifies the actual matrix inverse with
the existing inverse Gram source; no inverse is postulated.
-/

open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteHilbertGram
noncomputable section
variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
def gramMatrix (v : ι → H) : Matrix ι ι ℝ := fun i j => inner ℝ (v i) (v j)
omit [DecidableEq ι] in
theorem gramMatrix_mulVec (v : ι → H) (c : ι → ℝ) :
    (gramMatrix v).mulVec c = gram v c := by
  funext i
  simp [Matrix.mulVec, dotProduct, gramMatrix, gram_apply]
omit [DecidableEq ι] in
theorem gramMatrix_posDef {v : ι → H} (hv : LinearIndependent ℝ v) :
    (gramMatrix v).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    simp [Matrix.conjTranspose_apply, gramMatrix, real_inner_comm]
  · intro c hc
    rw [gramMatrix_mulVec]
    have hn : Fintype.linearCombination ℝ v c ≠ 0 := by
      intro hz
      apply hc
      apply hv.fintypeLinearCombination_injective
      simpa using hz
    have hp := sq_pos_of_pos (norm_pos_iff.mpr hn)
    rw [gram_quadratic] at hp
    simpa only [dotProduct, star_trivial] using hp
theorem gramMatrix_det_pos {v : ι → H} (hv : LinearIndependent ℝ v) :
    0 < (gramMatrix v).det := (gramMatrix_posDef hv).det_pos
theorem gramMatrix_inverseSource {v : ι → H} (hv : LinearIndependent ℝ v) (b : ι → ℝ) :
    (gramMatrix v)⁻¹.mulVec b = FiniteGramCapacity.inverseSource hv b := by
  apply gram_injective hv
  rw [← gramMatrix_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (ne_of_gt (gramMatrix_det_pos hv))),
    Matrix.one_mulVec]
  exact (funext (FiniteGramCapacity.inverseSource_normal hv b)).symm
end
end RiemannResearch.Analysis.FiniteHilbertGram

namespace Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem det_add_outer (A : Matrix ι ι ℝ) (hA : IsUnit A.det) (u v : ι → ℝ) :
    (A + vecMulVec u v).det = A.det * (1 + v ⬝ᵥ (A⁻¹ *ᵥ u)) := by
  have hout : replicateCol Unit u * replicateRow Unit v = vecMulVec u v := by
    ext i j
    simp [mul_apply, replicateCol, replicateRow, vecMulVec]
  have h := det_add_replicateCol_mul_replicateRow (ι := Unit) hA u v
  rw [hout, det_unique (n := Unit)] at h
  convert h using 2
  simp only [add_apply, one_apply_eq, mul_apply, replicateRow_apply, replicateCol_apply,
    Finset.sum_mul, mulVec, dotProduct]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring
end Matrix
namespace RiemannResearch.Analysis.FiniteHilbertGram
noncomputable section
open FiniteGramCapacity
open scoped BigOperators
variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
theorem gramMatrix_det_update {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (t : ℝ) :
    (gramMatrix v + t • Matrix.vecMulVec b b).det =
      (gramMatrix v).det * (1 + t * capacity hv b) := by
  have he : t • Matrix.vecMulVec b b = Matrix.vecMulVec (t • b) b := by
    ext i j
    simp [Matrix.vecMulVec, mul_assoc]
  rw [he, Matrix.det_add_outer _ (isUnit_iff_ne_zero.mpr (ne_of_gt (gramMatrix_det_pos hv))),
    Matrix.mulVec_smul, gramMatrix_inverseSource hv]
  congr 2
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, capacity, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
end
end RiemannResearch.Analysis.FiniteHilbertGram
namespace RiemannResearch.Analysis.FiniteHilbertGram
noncomputable section
open scoped BigOperators
variable {ι κ H : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
theorem projection_inner_eq_inverseGram {v : ι → H}
    (hv : LinearIndependent ℝ v) (x y : H) :
    inner ℝ ((synthesisSpan v).starProjection x) ((synthesisSpan v).starProjection y) =
      dotProduct (cross v x) ((gramMatrix v)⁻¹.mulVec (cross v y)) := by
  rw [gramMatrix_inverseSource hv]
  rw [real_inner_comm, ← synthesis_inverseCoeff_eq_projection hv y,
    ← synthesis_inverseCoeff_eq_projection hv x, inner_synthesis_left]
  simp_rw [inverseCoeff_normal hv x]
  apply Finset.sum_congr rfl
  intro i _
  change inverseCoeff hv y i * cross v x i =
    cross v x i * FiniteGramCapacity.inverseSource hv (cross v y) i
  exact mul_comm _ _

def observationMatrix (v : ι → H) (x : κ → H) : Matrix κ ι ℝ :=
  fun i j => cross v (x i) j

theorem projection_kernel_matrix {v : ι → H} (hv : LinearIndependent ℝ v)
    (x : κ → H) :
    Matrix.of (fun i j => inner ℝ ((synthesisSpan v).starProjection (x i))
      ((synthesisSpan v).starProjection (x j))) =
      observationMatrix v x * (gramMatrix v)⁻¹ * (observationMatrix v x).transpose := by
  rw [Matrix.mul_assoc]
  ext i j
  rw [Matrix.of_apply, projection_inner_eq_inverseGram hv]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, observationMatrix,
    Matrix.mulVec, dotProduct]

end
end RiemannResearch.Analysis.FiniteHilbertGram

namespace Matrix
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
theorem det_sub_mul_div (G : Matrix ι ι ℝ) (hG : IsUnit G.det)
    (U : Matrix ι κ ℝ) (V : Matrix κ ι ℝ) :
    (G - U * V).det / G.det = (1 - V * G⁻¹ * U).det := by
  have h : (G - U * V).det = G.det * (1 - V * G⁻¹ * U).det := by
    simpa only [sub_eq_add_neg, Matrix.neg_mul, Matrix.mul_neg] using
      (det_add_mul (-U) V hG)
  rw [h]
  exact mul_div_cancel_left₀ _ (isUnit_iff_ne_zero.mp hG)
end Matrix
