import RiemannResearch.RH.RamanujanFiniteSpanBridge
import RiemannResearch.RH.MellinProjectionKernel
import RiemannResearch.RH.IntegerDPPKernel
import RiemannResearch.RH.ParetoBoundedMellinLinearity
import RiemannResearch.RH.ResidueOrthonormalCoordinates
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Tactic.Ring

/-!
# Integer and Mellin projection kernels in the Ramanujan packet basis

All kernels in this module use the natural conductor prefix. The finite
span is unchanged by passing to the integrated Ramanujan packets or to
their Gram–Schmidt modes.
-/

noncomputable section

open scoped BigOperators

namespace RiemannResearch.RH.Pareto

open CoefficientStabilization
open RiemannResearch.Analysis.FiniteHilbertGram

private theorem starProjection_congr_space {S T : Submodule ℝ ThresholdHilbert}
    [S.HasOrthogonalProjection] [T.HasOrthogonalProjection] (h : S = T) (x : ThresholdHilbert) :
    S.starProjection x = T.starProjection x := by
  subst T
  rfl

/-- Gram–Schmidt applied to the actual integrated packets in conductor order. -/
def packetMode (n : ℕ) : Fin n → ThresholdHilbert :=
  InnerProductSpace.gramSchmidtNormed ℝ (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))

theorem packetMode_orthonormal (n : ℕ) : Orthonormal ℝ (packetMode n) :=
  InnerProductSpace.gramSchmidtNormed_orthonormal (finitePacket_independent n)

theorem packetMode_span (n : ℕ) : synthesisSpan (packetMode n) = finiteSpace n := by
  let v := fun i : Fin n => ramanujanPacketHilbert (i.val + 2)
  exact ((InnerProductSpace.span_gramSchmidtNormed_range v).trans
    (InnerProductSpace.span_gramSchmidt ℝ v)).trans (finitePacket_span_eq n)

theorem packetMode_projection_eq_residueMode (n : ℕ) (x : ThresholdHilbert) :
    (synthesisSpan (packetMode n)).starProjection x =
      (synthesisSpan (fun i : Fin n => residueMode i.val)).starProjection x := by
  exact starProjection_congr_space ((packetMode_span n).trans (residueMode_finiteSpace n).symm) x

namespace IntegerDPP

/-- The complete integer kernel, with the physical site vectors as its two observations. -/
theorem integerKernel_eq_packetInverseGram (n i j : ℕ) :
    integerKernel n i j =
      dotProduct (cross (fun k : Fin n => ramanujanPacketHilbert (k.val + 2)) (countingBasis i))
        ((finitePacketGram n)⁻¹.mulVec
          (cross (fun k : Fin n => ramanujanPacketHilbert (k.val + 2)) (countingBasis j))) := by
  have h := projection_inner_eq_inverseGram (finitePacket_independent n)
    (countingBasis i) (countingBasis j)
  have hs : synthesisSpan (fun k : Fin n => ramanujanPacketHilbert (k.val + 2)) =
      finiteSpace n := finitePacket_span_eq n
  rw [starProjection_congr_space hs (countingBasis i),
    starProjection_congr_space hs (countingBasis j)] at h
  exact h

end IntegerDPP

namespace MellinFrequency

/-- The Mellin inverse-Gram kernel with integrated Ramanujan features. -/
def packetFrequencyKernel (n : ℕ) (t u : ℝ) : ℂ :=
  ∑ i : Fin n, ∑ j : Fin n,
    paretoMellin (ramanujanPacketHilbert (i.val + 2)) (criticalPoint t) *
      (((finitePacketGram n)⁻¹ i j : ℝ) : ℂ) *
      star (paretoMellin (ramanujanPacketHilbert (j.val + 2)) (criticalPoint u))

private def packetModeMatrix (n : ℕ) (w : Fin n → ThresholdHilbert) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun j => inverseCoeff (finitePacket_independent n) (w j)

private theorem packetMode_expansion (n : ℕ) (w : Fin n → ThresholdHilbert)
    (hw : ∀ j, w j ∈ finiteSpace n) (j : Fin n) :
    w j = ∑ i : Fin n, packetModeMatrix n w j i • ramanujanPacketHilbert (i.val + 2) := by
  have h := synthesis_inverseCoeff_eq_projection (finitePacket_independent n) (w j)
  have hspan : synthesisSpan (fun k : Fin n => ramanujanPacketHilbert (k.val + 2)) =
      finiteSpace n := finitePacket_span_eq n
  rw [starProjection_congr_space hspan (w j), Submodule.starProjection_eq_self_iff.mpr (hw j)] at h
  simpa only [Fintype.linearCombination_apply, packetModeMatrix] using h.symm

private theorem packetGram_inverse_eq_modeMatrix (n : ℕ) (w : Fin n → ThresholdHilbert)
    (hw : ∀ j, w j ∈ finiteSpace n) (ho : Orthonormal ℝ w) :
    (finitePacketGram n)⁻¹ = (packetModeMatrix n w).transpose * packetModeMatrix n w := by
  let C := packetModeMatrix n w
  have h : C * finitePacketGram n * C.transpose = 1 := by
    ext i j
    have hi := (orthonormal_iff_ite.mp ho) i j
    rw [packetMode_expansion n w hw i, packetMode_expansion n w hw j] at hi
    simp only [sum_inner, inner_sum, real_inner_smul_left, inner_smul_right,
      Finset.mul_sum] at hi
    simp only [C, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      finitePacketGram, gramMatrix, Finset.sum_mul]
    convert hi using 1
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [Matrix.mul_assoc] at h
  have hinv := mul_eq_one_comm.mp h
  rw [Matrix.mul_assoc] at hinv
  exact Matrix.inv_eq_right_inv hinv

private theorem transform_packet_expansion (n : ℕ) (w : Fin n → ThresholdHilbert)
    (hw : ∀ j, w j ∈ finiteSpace n) (j : Fin n) (t : ℝ) :
    paretoMellin (w j) (criticalPoint t) =
      ∑ i : Fin n, (packetModeMatrix n w j i : ℂ) *
        paretoMellin (ramanujanPacketHilbert (i.val + 2)) (criticalPoint t) := by
  rw [packetMode_expansion n w hw j, paretoMellin_fintype_sum_of_bounded]
  · simp only [paretoMellin_smul, Complex.real_smul]
  · intro i
    apply finiteSpace_sequence_bounded n
    apply (finiteSpace n).smul_mem
    have hs : synthesisSpan (fun k : Fin n => ramanujanPacketHilbert (k.val + 2)) =
        finiteSpace n := finitePacket_span_eq n
    rw [← hs]
    exact Submodule.subset_span ⟨i, rfl⟩
  · simp

/-- Every orthonormal basis of the prefix gives the same Mellin kernel. -/
theorem packetFrequencyKernel_eq_orthonormal_sum (n : ℕ) (w : Fin n → ThresholdHilbert)
    (hw : ∀ j, w j ∈ finiteSpace n) (ho : Orthonormal ℝ w) (t u : ℝ) :
    packetFrequencyKernel n t u =
      ∑ k : Fin n, paretoMellin (w k) (criticalPoint t) *
        star (paretoMellin (w k) (criticalPoint u)) := by
  simp only [packetFrequencyKernel, packetGram_inverse_eq_modeMatrix n w hw ho,
    Matrix.mul_apply, Matrix.transpose_apply, Complex.ofReal_sum, Complex.ofReal_mul,
    Finset.mul_sum, Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [transform_packet_expansion n w hw k t, transform_packet_expansion n w hw k u]
  simp only [star_sum, star_mul, Complex.star_def, Complex.conj_ofReal,
    Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem kernel_eq_packetFrequencyKernel (n : ℕ) (t u : ℝ) :
    kernel n t u = packetFrequencyKernel n t u := by
  rw [kernel_eq_mode_sum, packetFrequencyKernel_eq_orthonormal_sum n (fun k => residueMode k.val)]
  · rfl
  · intro k
    rw [← residueMode_finiteSpace]
    exact Submodule.subset_span ⟨k, rfl⟩
  · exact residueMode_orthonormal.comp (fun i : Fin n => i.val) Fin.val_injective

theorem kernel_eq_packetMode_sum (n : ℕ) (t u : ℝ) :
    kernel n t u = ∑ k : Fin n, paretoMellin (packetMode n k) (criticalPoint t) *
      star (paretoMellin (packetMode n k) (criticalPoint u)) := by
  rw [kernel_eq_packetFrequencyKernel]
  refine packetFrequencyKernel_eq_orthonormal_sum n (packetMode n) ?_
    (packetMode_orthonormal n) t u
  intro k
  rw [← packetMode_span]
  exact Submodule.subset_span ⟨k, rfl⟩

end MellinFrequency
end RiemannResearch.RH.Pareto
