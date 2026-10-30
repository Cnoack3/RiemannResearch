/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFloorDilation
import RiemannResearch.RH.QFloorDilationEnergy
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.RH.QDivisorLegality
import RiemannResearch.RH.QDivisibilityDensity
import RiemannResearch.RH.QDivisibilityHilbertMoments
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# An explicit two-conductor arithmetic trial

Source: the user-provided RH proof-strategy handoff, 30 October 2026,
Section 4.2, asks for an explicit arithmetic trial direction.
The pair below is derived directly from the already formalized residue
refinement and complete-Q floor-dilation estimate; no priority claim is made.

For a positive integer p, the signed pair g_p - 2 g_(2p) is exactly the
negative binary digit of floor(n/p). It vanishes below p, its old-anchor
terms cancel, and its complete Q energy is at most 3/(4p).
Primality is needed only when applying this pair to a legal new-prime
dictionary. No source lower bound, cumulative cancellation estimate, or
Riemann Hypothesis is asserted here.
-/

noncomputable section
namespace RiemannResearch.RH.QCRTPrimePairTrial
open ZetaTwoHilbert ZetaTwoProbability QFloorDilation
open QSquarefreeLatticePackets ArithmeticCumulative QDivisorLegality QDivisibilityDensity

/-- The reciprocal slopes of this pair cancel exactly. -/
def primePair (p : ℕ) : QHilbert :=
  qResidue p - (2 : ℝ) • qResidue (2 * p)

/-- The pair is an actual floor dilation of the binary residue. -/
theorem primePair_eq_floorDilation (p : ℕ) (hp : 0 < p) :
    primePair p = (-2 : ℝ) • floorDilation p hp (qResidue 2) := by
  rw [floorDilation_qResidue p 2 hp (by norm_num)]
  rw [Nat.mul_comm p 2]
  unfold primePair
  module

theorem primePair_eq_floorDilation_base (p : ℕ) (hp : 0 < p) :
    primePair p = floorDilation p hp ((-2 : ℝ) • qResidue 2) := by
  rw [primePair_eq_floorDilation p hp, map_smul]

/-- Exact physical sequence, with the sign and every quotient block retained. -/
theorem primePair_sequence (p n : ℕ) (hp : 0 < p) :
    qSequence (primePair p) n = -(((n / p) % 2 : ℕ) : ℝ) := by
  rw [primePair_eq_floorDilation p hp]
  change qSequenceLinear ((-2 : ℝ) • floorDilation p hp (qResidue 2)) n = _
  rw [map_smul]
  change (-2 : ℝ) * qSequence (floorDilation p hp (qResidue 2)) n = _
  rw [floorDilation_sequence, qSequence_qResidue]
  (norm_num [residueFraction]; ring)

theorem primePair_head (p n : ℕ) (hp : 0 < p) (hnp : n < p) :
    qSequence (primePair p) n = 0 := by
  rw [primePair_sequence p n hp]
  simp only [Nat.div_eq_of_lt hnp, Nat.zero_mod, Nat.cast_zero, neg_zero]

theorem primePair_abs_le_one (p n : ℕ) (hp : 0 < p) :
    |qSequence (primePair p) n| ≤ 1 := by
  rw [primePair_sequence p n hp, abs_neg, abs_of_nonneg (by positivity)]
  have hm : (n / p) % 2 ≤ 1 := by omega
  exact_mod_cast hm

theorem primePair_at (p : ℕ) (hp : 0 < p) :
    qSequence (primePair p) p = -1 := by
  rw [primePair_sequence p p hp]
  simp [Nat.div_self hp]

/-- The old-anchor coefficients cancel before screening. -/
theorem primePair_anchor_cancellation (p L : ℕ) (hp : 0 < p) :
    compensatedResidue p L - (2 : ℝ) • compensatedResidue (2 * p) L =
      primePair p := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  have hc : (L : ℝ) / (p : ℝ) =
      (2 : ℝ) * ((L : ℝ) / ((2 * p : ℕ) : ℝ)) := by
    push_cast
    field_simp [hpR]
  unfold compensatedResidue primePair
  rw [hc]
  module

/-- The exact complete-Q energy of the binary base is 3/4. -/
theorem binary_base_norm_sq : ‖(-2 : ℝ) • qResidue 2‖ ^ 2 = (3 / 4 : ℝ) := by
  have he : (-2 : ℝ) • qResidue 2 = qDivisor 2 - qOne := by
    rw [qDivisor_two_eq]
    module
  rw [he, norm_sub_sq_real, qOne_norm_sq, qDivisor_norm_sq 2 (by decide),
    real_inner_comm, qOne_inner_qDivisor 2 (by decide)]
  norm_num

/-- Complete infinite-tail energy with the exact binary-base constant. -/
theorem primePair_norm_sq_le (p : ℕ) (hp : 0 < p) :
    ‖primePair p‖ ^ 2 ≤ 3 / (4 * (p : ℝ)) := by
  rw [primePair_eq_floorDilation_base p hp]
  have h := floorDilation_norm_sq_le_sharp p hp ((-2 : ℝ) • qResidue 2)
  rw [binary_base_norm_sq] at h
  simpa only [div_div] using h

/-- A divisor-stage application needs both actual conductors. -/
theorem primePair_mem_divisorStage (p L : ℕ) (hp : p ∣ L) (h2p : 2 * p ∣ L) :
    primePair p ∈ divisorStage L := by
  exact (divisorStage L).sub_mem
    (Submodule.subset_span ⟨p, hp, rfl⟩)
    ((divisorStage L).smul_mem _
      (Submodule.subset_span ⟨2 * p, h2p, rfl⟩))

end RiemannResearch.RH.QCRTPrimePairTrial
