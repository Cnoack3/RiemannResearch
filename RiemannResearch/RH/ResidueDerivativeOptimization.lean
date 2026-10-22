import RiemannResearch.RH.CRTPrimitiveEscape
import RiemannResearch.RH.ThresholdHilbertAdjoint

/-!
# Legal and derivative optimizers differ already at the first residue

Source: direct calculation in the user's actual Pareto Hilbert space.
The anchored target derivative is the first point atom. The full norm-square
polynomial and signed normal-equation defect are evaluated exactly.
This rules out an automatic commutation claim; it does not rule out asymptotic
compatibility for the exhaustive optimal sequence.
-/


noncomputable section
namespace RiemannResearch.RH.Pareto.CRTPrimitiveEscape

private theorem binaryJump_one_weighted_square (k : ℕ) :
    positiveWeight k * binaryJump 1 k ^ 2 = positiveWeight k := by
  by_cases hk : k = 0
  · subst k
    simp [binaryJump_zero, positiveWeight]
  · have hj := binaryJump_multiple 1 k (by decide) (Nat.pos_of_ne_zero hk)
    simp only [Nat.one_mul, Nat.cast_one, one_mul] at hj
    rw [hj, alternatingProfile_sq, mul_one]

private theorem binaryJump_one_summable :
    Summable (fun k : ℕ => positiveWeight k * binaryJump 1 k ^ 2) := by
  apply positiveWeight_summable.congr
  intro k
  exact (binaryJump_one_weighted_square k).symm

/-- Actual physical difference of the first legal primitive. -/
def binaryJumpOneHilbert : ThresholdHilbert :=
  sequenceHilbert (binaryJump 1) binaryJump_one_summable

@[simp] theorem binaryJumpOneHilbert_sequence :
    hilbertSequence binaryJumpOneHilbert = binaryJump 1 := by
  apply hilbertSequence_sequenceHilbert
  exact binaryJump_zero 1

theorem binaryJumpOneHilbert_norm_sq : ‖binaryJumpOneHilbert‖ ^ 2 = 1 := by
  rw [hilbert_norm_weighted_sq, binaryJumpOneHilbert_sequence]
  simp_rw [binaryJump_one_weighted_square]
  exact positiveWeight_tsum

private theorem binaryJump_one_one : binaryJump 1 1 = 1 := by
  rw [binaryJump_eq 1 1 (by decide)]
  norm_num

/-- The physical target is Δ1=δ₁, including the anchored boundary term. -/
theorem target_atom_one_norm_sq : ‖hilbertAtom 1 (by decide)‖ ^ 2 = (1/2 : ℝ) := by
  rw [← real_inner_self_eq_norm_sq,
    hilbertAtom_inner, hilbertAtom_sequence]
  norm_num [positiveWeight]

theorem target_atom_binaryJump_inner :
    inner ℝ (hilbertAtom 1 (by decide)) binaryJumpOneHilbert = (1/2 : ℝ) := by
  rw [hilbertAtom_inner, binaryJumpOneHilbert_sequence, binaryJump_one_one]
  norm_num [positiveWeight]

/-- Complete derivative objective, with its unique minimizer visible. -/
theorem binaryJumpOne_derivative_target_error (t : ℝ) :
    ‖hilbertAtom 1 (by decide) - t • binaryJumpOneHilbert‖ ^ 2 =
      (1/4 : ℝ) + (t - 1/2)^2 := by
  rw [norm_sub_sq_real, target_atom_one_norm_sq,
    real_inner_smul_right, target_atom_binaryJump_inner, norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs, binaryJumpOneHilbert_norm_sq]
  ring

/-- The legal optimizer t=1 does not satisfy derivative normal equations. -/
theorem binaryJumpOne_optimizer_incompatibility :
    inner ℝ (hilbertAtom 1 (by decide) - binaryJumpOneHilbert)
      binaryJumpOneHilbert = -(1/2 : ℝ) := by
  rw [inner_sub_left, target_atom_binaryJump_inner,
    real_inner_self_eq_norm_sq, binaryJumpOneHilbert_norm_sq]
  norm_num

end RiemannResearch.RH.Pareto.CRTPrimitiveEscape
