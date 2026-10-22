/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QParityBasis
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoParitySignal
import RiemannResearch.RH.PrimePowerTargetMellin
import RiemannResearch.RH.PrimePowerTwoTargetCriterion
import RiemannResearch.RH.QSquarefreeDilationObstruction
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# A legal orthonormal parity coordinate for the dyadic logarithm target

Source: user-provided orthonormal-basis research direction, 20 October 2026.
The constant and centered parity vectors belong to the actual squarefree
closure enlarged by constants. The dyadic logarithm target has parity
coefficient 1 / sqrt 3, giving an exact captured energy of 1/3. The residual
norm is retained; membership of the complete prime-power targets in the
enclosure remains an open obligation.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace RiemannResearch.RH.PrimePowerTarget
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParitySignal

theorem qTarget_two_inner_even :
    inner ℝ (qTarget 2 (by norm_num)) qEven =
      (inner ℝ (qTarget 2 (by norm_num)) qOne + 1) / 4 := by
  rw [qInner_even_reindex]
  have hpoint (k : ℕ) :
      positiveQWeight (2 * k) * qSequence (qTarget 2 (by norm_num)) (2 * k) =
      (1 / 4 : ℝ) * (positiveQWeight k * qSequence (qTarget 2 (by norm_num)) k +
        positiveQWeight k) := by
    by_cases hk : k = 0
    · subst k
      norm_num [positiveQWeight]
    · rw [positiveQWeight_mul, qTarget_sequence]
      have hlog : Nat.log 2 (2 * k) = Nat.log 2 k + 1 := by
        simpa only [Nat.mul_comm] using Nat.log_mul_base (by norm_num : 1 < 2) hk
      dsimp only
      rw [hlog, Nat.cast_add, Nat.cast_one]
      norm_num
      ring
  simp_rw [hpoint]
  rw [tsum_mul_left, (qWeighted_summable _).tsum_add positiveQWeight_summable,
    ← qInner_one_tsum, positiveQWeight_tsum]
  ring

theorem parityUnit_mem_closureWithConstants : parityUnit ∈ closureWithConstants :=
  closureWithConstants.smul_mem _ (closureWithConstants.sub_mem
    (closureWithConstants.smul_mem _ qEven_mem_closureWithConstants)
    qOne_mem_closureWithConstants)

theorem qTarget_two_inner_parityUnit :
    inner ℝ (qTarget 2 (by norm_num)) parityUnit = 1 / Real.sqrt 3 := by
  rw [parityUnit, real_inner_smul_right, parityCentered, inner_sub_right,
    real_inner_smul_right, qTarget_two_inner_even]
  ring

theorem parityFrame_mem_closureWithConstants (i : Bool) :
    parityFrame i ∈ closureWithConstants := by
  cases i
  · exact qOne_mem_closureWithConstants
  · exact parityUnit_mem_closureWithConstants

theorem parityApproximation_mem_closureWithConstants (f : QHilbert) :
    parityApproximation f ∈ closureWithConstants :=
  closureWithConstants.add_mem
    (closureWithConstants.smul_mem _ qOne_mem_closureWithConstants)
    (closureWithConstants.smul_mem _ parityUnit_mem_closureWithConstants)

/-- The first nonconstant legal coordinate captures exactly 1/3 of F₂'s energy.
This is a partial expansion, not a proof that the full target belongs to the enclosure. -/
theorem qTarget_two_parity_energy_exact :
    ‖qTarget 2 (by norm_num)‖ ^ 2 =
      (inner ℝ (qTarget 2 (by norm_num)) qOne) ^ 2 + 1 / 3 +
        ‖qTarget 2 (by norm_num) - parityApproximation (qTarget 2 (by norm_num))‖ ^ 2 := by
  have h := parityApproximation_energy_exact (qTarget 2 (by norm_num))
  have hs : (1 / Real.sqrt 3) ^ 2 = (1 / 3 : ℝ) := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  rw [qTarget_two_inner_parityUnit, hs] at h
  exact h

end RiemannResearch.RH.PrimePowerTarget
