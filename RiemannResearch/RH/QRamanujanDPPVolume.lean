import RiemannResearch.RH.QRamanujanDPPLaw
import RiemannResearch.RH.IntegerDPPTrace
import RiemannResearch.Probability.DeterminantalConfiguration
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Exact Q packet rank and volume-sampling configurations

Source: sixth transfer program, 24 October 2026. Fixed-cardinality projection
DPP terminology follows Kulesza--Taskar, https://arxiv.org/abs/1207.6083.
The counting-space configurations have exactly the actual Q packet rank.
Their probabilities are squared evaluation determinants divided by the full
Q packet Gram determinant, with no finite physical truncation.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical ENNReal
namespace RiemannResearch.RH.QRamanujanDPP
open Pareto ZetaTwoHilbert QRamanujanCanonicalOptimizer
open Pareto.IntegerDPP (countingBasis countingBasis_inner_vector)
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Probability.DPP

def mode (n : ℕ) : Fin n → QHilbert :=
  InnerProductSpace.gramSchmidtNormed ℝ (packetFamily n)

theorem mode_orthonormal (n : ℕ) : Orthonormal ℝ (mode n) :=
  InnerProductSpace.gramSchmidtNormed_orthonormal (packet_independent n)

theorem mode_stage (n : ℕ) : synthesisSpan (mode n) = QFullResidueProjection.stage n := by
  have he : Submodule.span ℝ (Set.range (mode n)) =
      Submodule.span ℝ (Set.range (packetFamily n)) :=
    (InnerProductSpace.span_gramSchmidtNormed_range (packetFamily n)).trans
      (InnerProductSpace.span_gramSchmidt ℝ (packetFamily n))
  exact he.trans (packet_span_eq_stage n)

theorem stage_finrank (n : ℕ) : Module.finrank ℝ (QFullResidueProjection.stage n) = n := by
  rw [← packet_span_eq_stage]
  change Module.finrank ℝ (Submodule.span ℝ (Set.range (packetFamily n))) = n
  rw [finrank_span_eq_card (packet_independent n), Fintype.card_fin]

theorem kernel_diagonal_mode_sum (n i : ℕ) :
    kernel n i i = ∑ j : Fin n, (mode n j i) ^ 2 := by
  change inner ℝ ((QFullResidueProjection.stage n).starProjection (countingBasis i))
    ((QFullResidueProjection.stage n).starProjection (countingBasis i)) = _
  rw [real_inner_self_eq_norm_sq]
  have h := projection_norm_sq_eq_orthonormal_sum (mode_orthonormal n) (countingBasis i)
  simp only [mode_stage] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_comm, countingBasis_inner_vector]

theorem kernel_diagonal_summable (n : ℕ) : Summable (fun i => kernel n i i) := by
  simp only [kernel_diagonal_mode_sum]
  exact summable_sum (fun j _ => hilbert_coordinate_square_summable (mode n j))

theorem kernel_diagonal_tsum (n : ℕ) : (∑' i, kernel n i i) = (n : ℝ) := by
  simp only [kernel_diagonal_mode_sum]
  have hs (j : Fin n) : Summable (fun i : ℕ => (mode n j i) ^ 2) :=
    hilbert_coordinate_square_summable (mode n j)
  rw [Summable.tsum_finsetSum (s := Finset.univ) (fun j _ => hs j)]
  simp only [← hilbert_norm_sq, (mode_orthonormal n).norm_eq_one, one_pow]
  simp

theorem principal_det_zero_of_rank (n : ℕ) (a : Fin (n + 1) → ℕ) :
    (Matrix.of (fun i j => kernel n (a i) (a j))).det = 0 := by
  by_contra hd
  let v : Fin (n + 1) → QFullResidueProjection.stage n := fun i =>
    ⟨(QFullResidueProjection.stage n).starProjection (countingBasis (a i)),
      (QFullResidueProjection.stage n).starProjection_apply_mem _⟩
  have hv : LinearIndependent ℝ v := Matrix.linearIndependent_of_det_gram_ne_zero (by
    change (Matrix.of (fun i j => kernel n (a i) (a j))).det ≠ 0
    exact hd)
  have hc := hv.fintype_card_le_finrank
  rw [Fintype.card_fin, stage_finrank] at hc
  omega

theorem law_cardinality (n : ℕ) :
    ∀ᵐ x ∂law n, setCount {i | x i = true} = n :=
  (law_isDPP n).setCount_eq_ae_of_rank_trace n
    (fun e => principal_det_zero_of_rank n e)
    (kernel_diagonal_summable n) (kernel_diagonal_tsum n)

theorem full_configuration (n : ℕ) (e : Fin n ↪ ℕ) :
    (law n).real {x | {i | x i = true} = Set.range e} =
      (Matrix.of (fun i j => kernel n (e i) (e j))).det :=
  (law_isDPP n).full_configuration_of_setCount n (law_cardinality n) e

/-- Exact volume sampling under the complete physical Q law. -/
theorem full_configuration_volume (n : ℕ) (e : Fin n ↪ ℕ) :
    (law n).real {x | {i | x i = true} = Set.range e} =
      (observationMatrix (packetFamily n) (fun i => countingBasis (e i))).det ^ 2 /
        (packetGram n).det := by
  rw [full_configuration, kernel_matrix, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  ring

end RiemannResearch.RH.QRamanujanDPP
