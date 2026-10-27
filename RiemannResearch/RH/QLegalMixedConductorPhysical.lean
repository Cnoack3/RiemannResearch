/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QLegalMixedConductorAsymptotics
import RiemannResearch.RH.QReciprocalQuarterContraction
import Lean.Elab.Tactic.Omega

/-!
# Literal physical correction and uniform remainder control

Source: LegalSubspaceProjectionObstruction.md. The actual projected residual
has a high-conductor part plus a uniformly bounded physical remainder. The
sharp ordinary norm bounds are supplied by the general quarter-contraction.
The larger harmless remainder constant four simplifies the divergence proof.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QLegalMixedConductor
open ZetaTwoHilbert ZetaTwoProbability QShiftedReciprocal ArithmeticCumulative

theorem actualResidual_norm_le_one (d : ℕ) : ‖actualResidual d‖ ≤ 1 := by
  have ho := Submodule.inner_right_of_mem_orthogonal
    ((mixedSpace d).starProjection_apply_mem qOne) (actualResidual_orthogonal d)
  have he : ‖actualResidual d‖ ^ 2 = inner ℝ qOne (actualResidual d) := by
    calc
      _ = inner ℝ (actualResidual d) (actualResidual d) :=
        (real_inner_self_eq_norm_sq _).symm
      _ = inner ℝ qOne (actualResidual d) := by
        change inner ℝ (qOne - (mixedSpace d).starProjection qOne)
          (actualResidual d) = _
        rw [inner_sub_left, ho, sub_zero]
  have hi := real_inner_le_norm qOne (actualResidual d)
  rw [qOne_norm, one_mul, ← he] at hi
  nlinarith [norm_nonneg (actualResidual d)]

theorem actualCorrection_norm_le_one (d : ℕ) : ‖actualCorrection d‖ ≤ 1 := by
  calc
    _ ≤ ‖(mixedSpace d).starProjection‖ * ‖B (actualResidual d)‖ :=
      (mixedSpace d).starProjection.le_opNorm _
    _ ≤ ‖B (actualResidual d)‖ := by
      simpa using mul_le_mul_of_nonneg_right
        (Submodule.starProjection_norm_le (mixedSpace d)) (norm_nonneg _)
    _ ≤ ‖actualResidual d‖ := B_norm_le _
    _ ≤ 1 := actualResidual_norm_le_one d

theorem correctionParityCoefficient_abs_le (d : ℕ) (hd : 2 < d) :
    |correctionParityCoefficient d| ≤ 3 := by
  have ho : inner ℝ (orthogonalVector d) parityAtom = 0 := by
    rw [real_inner_comm]; exact orthogonalVector_orthogonal d
  have he : inner ℝ (actualCorrection d) parityAtom =
      correctionParityCoefficient d * (3 / 16) := by
    rw [actualCorrection_eq d hd, inner_add_left, real_inner_smul_left,
      real_inner_smul_left, ho, mul_zero, add_zero,
      real_inner_self_eq_norm_sq, parityAtom_norm_sq]
  have hi := abs_real_inner_le_norm (actualCorrection d) parityAtom
  have hg : ‖parityAtom‖ ≤ 1 / 2 := by
    nlinarith [parityAtom_norm_sq, norm_nonneg parityAtom]
  have hm := mul_le_mul (actualCorrection_norm_le_one d) hg (norm_nonneg parityAtom)
    (by norm_num : (0 : ℝ) ≤ 1)
  rw [he, abs_mul] at hi
  norm_num at hi hm
  linarith

theorem correctionCoefficient_abs_le (d : ℕ) (hd : 2 < d) (hG : 25 ≤ gram d) :
    |correctionCoefficient d| ≤ 1 / 5 := by
  have he : inner ℝ (actualCorrection d) (orthogonalVector d) =
      correctionCoefficient d * ‖orthogonalVector d‖ ^ 2 := by
    rw [actualCorrection_eq d hd, inner_add_left, real_inner_smul_left,
      real_inner_smul_left, orthogonalVector_orthogonal d, mul_zero, zero_add,
      real_inner_self_eq_norm_sq]
  have hi := abs_real_inner_le_norm (actualCorrection d) (orthogonalVector d)
  have hm := mul_le_mul_of_nonneg_right (actualCorrection_norm_le_one d)
    (norm_nonneg (orthogonalVector d))
  rw [he, abs_mul, abs_of_nonneg (sq_nonneg ‖orthogonalVector d‖)] at hi
  simp only [one_mul] at hm
  have hn : 5 ≤ ‖orthogonalVector d‖ := by
    change 25 ≤ ‖orthogonalVector d‖ ^ 2 at hG
    nlinarith [norm_nonneg (orthogonalVector d)]
  have hp : 0 < ‖orthogonalVector d‖ := by linarith
  have hprod : |correctionCoefficient d| * ‖orthogonalVector d‖ ≤ 1 := by
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith
  nlinarith [mul_nonneg (abs_nonneg (correctionCoefficient d)) (sub_nonneg.mpr hn)]

theorem fixedParityCoefficient_abs_le : |fixedParityCoefficient| ≤ 2 := by
  have hg : ‖parityAtom‖ ≤ 1 / 2 := by
    nlinarith [parityAtom_norm_sq, norm_nonneg parityAtom]
  have hi := abs_real_inner_le_norm (qResidue 3) parityAtom
  have hm := mul_le_mul qResidue_three_norm_le hg (norm_nonneg parityAtom)
    (by norm_num : (0 : ℝ) ≤ 2 / 3)
  rw [fixedParityCoefficient, abs_div, parityAtom_norm_sq]
  norm_num
  nlinarith

theorem parityCoefficient_abs_eventually : ∀ᶠ d in atTop, |parityCoefficient d| ≤ 3 := by
  have h := parityCoefficient_tendsto.abs.eventually
    (gt_mem_nhds (show |fixedParityCoefficient| < 3 by
      linarith [fixedParityCoefficient_abs_le]))
  exact h.mono (fun _ h => h.le)

/-- The fixed-conductor part of the literal physical sequence. -/
def physicalRemainder (d n : ℕ) : ℝ :=
  (correctionParityCoefficient d - correctionCoefficient d * parityCoefficient d) *
    residueFraction 2 n + correctionCoefficient d * residueFraction 3 n

theorem actualCorrection_decomposition (d n : ℕ) (hd : 2 < d) :
    qSequence (actualCorrection d) n =
      correctionCoefficient d * (10 * Real.sqrt (d : ℝ)) * residueFraction d n +
        physicalRemainder d n := by
  rw [actualCorrection_sequence d n hd]
  unfold physicalRemainder
  ring

theorem physicalRemainder_abs_le (d : ℕ) (hd : 2 < d) (hG : 25 ≤ gram d)
    (hc : |parityCoefficient d| ≤ 3) (n : ℕ) : |physicalRemainder d n| ≤ 4 := by
  have hg := correctionParityCoefficient_abs_le d hd
  have hb := correctionCoefficient_abs_le d hd hG
  have h2 : |residueFraction 2 n| ≤ 1 := by
    simpa only [qSequence_qResidue] using qResidue_physical_abs_le_one 2 n
  have h3 : |residueFraction 3 n| ≤ 1 := by
    simpa only [qSequence_qResidue] using qResidue_physical_abs_le_one 3 n
  calc
    _ ≤ |correctionParityCoefficient d - correctionCoefficient d * parityCoefficient d| *
        |residueFraction 2 n| + |correctionCoefficient d| * |residueFraction 3 n| := by
      simpa only [physicalRemainder, abs_mul] using abs_add_le
        ((correctionParityCoefficient d - correctionCoefficient d * parityCoefficient d) *
          residueFraction 2 n) (correctionCoefficient d * residueFraction 3 n)
    _ ≤ |correctionParityCoefficient d - correctionCoefficient d * parityCoefficient d| +
        |correctionCoefficient d| := by
      have hA := mul_le_mul_of_nonneg_left h2 (abs_nonneg (correctionParityCoefficient d - correctionCoefficient d * parityCoefficient d))
      have hB := mul_le_mul_of_nonneg_left h3 (abs_nonneg (correctionCoefficient d))
      simpa only [mul_one] using add_le_add hA hB
    _ ≤ |correctionParityCoefficient d| +
        |correctionCoefficient d| * |parityCoefficient d| + |correctionCoefficient d| := by
      have htri : |correctionParityCoefficient d -
          correctionCoefficient d * parityCoefficient d| ≤
          |correctionParityCoefficient d| +
            |correctionCoefficient d| * |parityCoefficient d| := by
        simpa only [sub_eq_add_neg, abs_neg, abs_mul] using
          abs_add_le (correctionParityCoefficient d)
            (-(correctionCoefficient d * parityCoefficient d))
      exact add_le_add htri le_rfl
    _ ≤ 4 := by
      have hm := mul_le_mul hb hc (abs_nonneg (parityCoefficient d)) (by norm_num)
      linarith

theorem physicalRemainder_bounded_eventually :
    ∀ᶠ d in atTop, ∀ n, |physicalRemainder d n| ≤ 4 := by
  filter_upwards [eventually_ge_atTop (3 : ℕ), gram_bounds_eventually,
    parityCoefficient_abs_eventually] with d hd hG hc
  exact physicalRemainder_abs_le d (by omega) hG.1 hc

theorem actualResidual_norm_le_half (d : ℕ) : ‖actualResidual d‖ ≤ 1 / 2 := by
  have ho := Submodule.inner_right_of_mem_orthogonal
    ((mixedSpace d).starProjection_apply_mem qOne) (actualResidual_orthogonal d)
  have hp := Submodule.inner_right_of_mem_orthogonal
    (parityAtom_mem_mixedSpace d) (actualResidual_orthogonal d)
  have he : ‖actualResidual d‖ ^ 2 = inner ℝ evenTarget (actualResidual d) := by
    calc
      _ = inner ℝ (actualResidual d) (actualResidual d) :=
        (real_inner_self_eq_norm_sq _).symm
      _ = inner ℝ qOne (actualResidual d) := by
        change inner ℝ (qOne - (mixedSpace d).starProjection qOne)
          (actualResidual d) = _
        rw [inner_sub_left, ho, sub_zero]
      _ = _ := by rw [qOne_eq_parity_even, inner_add_left,
        real_inner_smul_left, hp, mul_zero, zero_add]
  have hj : ‖evenTarget‖ ≤ 1 / 2 := by
    nlinarith [evenTarget_norm_sq, norm_nonneg evenTarget]
  have hi := real_inner_le_norm evenTarget (actualResidual d)
  have hm := mul_le_mul_of_nonneg_right hj (norm_nonneg (actualResidual d))
  rw [← he] at hi
  nlinarith [norm_nonneg (actualResidual d)]

theorem actualCorrection_norm_le_eighth (d : ℕ) : ‖actualCorrection d‖ ≤ 1 / 8 := by
  have h := projected_B_quarter_norm_le (mixedSpace d) (actualResidual_orthogonal d)
  change ‖actualCorrection d‖ ≤ (1 / 4 : ℝ) * ‖actualResidual d‖ at h
  linarith [actualResidual_norm_le_half d]

end RiemannResearch.RH.QLegalMixedConductor
