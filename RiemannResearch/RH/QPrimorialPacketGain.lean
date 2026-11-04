/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimorialRelativeGain
import RiemannResearch.RH.QSquarefreePrimorialCofinality
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.Analysis.ResidualGainProduct
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Actual primorial packet gains and summable defects

Verified continuation of the prime-block research agenda. The exact recurrence is a specialization
of nested orthogonal projection; the infinite-product criterion reuses
ResidualGainProduct. The arithmetic lower bound is an explicit hypothesis.

Source for the RH closure criterion: Bagchi, Proc. Indian Acad. Sci.
Math. Sci. 116 (2006), 137--146, Remark 8, DOI 10.1007/BF02829783.
Packet grouping and the summable-defect comparison are elementary consequences
of the cited projection and scalar series identities, not arithmetic providers.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.QPrimorialPacketGain
open ZetaTwoHilbert QSquarefreePrimorialCofinality
open RiemannResearch.Analysis.ResidualGain

def packetGain (b : ℕ → ℕ) (k : ℕ) : ℝ :=
  ‖primorialOptimizer (b (k + 1)) - primorialOptimizer (b k)‖ ^ 2

def packetRelativeGain (b : ℕ → ℕ) (k : ℕ) : ℝ :=
  packetGain b k / primorialError (b k)

theorem packet_error_step (b : ℕ → ℕ) (hb : Monotone b) (k : ℕ) :
    primorialError (b k) = primorialError (b (k + 1)) + packetGain b k := by
  exact RiemannResearch.Analysis.ExhaustiveWalk.nested_projection_energy
    (primorialStage (b k)) (primorialStage (b (k + 1)))
    (primorialStage_mono (hb (Nat.le_succ k))) qOne

theorem packetRelativeGain_nonneg (b : ℕ → ℕ) (k : ℕ) :
    0 ≤ packetRelativeGain b k :=
  div_nonneg (sq_nonneg _) (primorialError_pos (b k)).le

theorem packetRelativeGain_lt_one (b : ℕ → ℕ) (hb : Monotone b) (k : ℕ) :
    packetRelativeGain b k < 1 := by
  unfold packetRelativeGain
  apply (div_lt_iff₀ (primorialError_pos (b k))).mpr
  have hs := packet_error_step b hb k
  have hp := primorialError_pos (b (k + 1))
  linarith

theorem packetGain_eq_error_mul_relativeGain (b : ℕ → ℕ) (k : ℕ) :
    packetGain b k = primorialError (b k) * packetRelativeGain b k := by
  unfold packetRelativeGain
  field_simp [ne_of_gt (primorialError_pos (b k))]

theorem packet_error_relativeGain_step (b : ℕ → ℕ) (hb : Monotone b) (k : ℕ) :
    primorialError (b (k + 1)) =
      primorialError (b k) * (1 - packetRelativeGain b k) := by
  have hs := packet_error_step b hb k
  rw [packetGain_eq_error_mul_relativeGain] at hs
  nlinarith

theorem packetRelativeGain_eq_one_sub_ratio
    (b : ℕ → ℕ) (hb : Monotone b) (k : ℕ) :
    packetRelativeGain b k =
      1 - primorialError (b (k + 1)) / primorialError (b k) := by
  unfold packetRelativeGain
  have hs := packet_error_step b hb k
  field_simp [ne_of_gt (primorialError_pos (b k))]
  linarith

theorem packet_error_eq_product (b : ℕ → ℕ) (hb : Monotone b) (K : ℕ) :
    primorialError (b K) = primorialError (b 0) *
      ∏ k ∈ Finset.range K, (1 - packetRelativeGain b k) :=
  by
    simpa only [survivalProduct] using
      (recurrence_eq_mul_product (d := fun k => primorialError (b k))
        (packet_error_relativeGain_step b hb) K)

theorem packet_error_le_exp_neg_sum
    (b : ℕ → ℕ) (hb : Monotone b) (K : ℕ) :
    primorialError (b K) ≤ primorialError (b 0) *
      Real.exp (-(∑ k ∈ Finset.range K, packetRelativeGain b k)) := by
  rw [packet_error_eq_product b hb]
  exact mul_le_mul_of_nonneg_left
    (survivalProduct_le_exp_neg_sum
      (fun k => (packetRelativeGain_lt_one b hb k).le) K)
    (primorialError_pos (b 0)).le

theorem packetError_tendsto_zero_iff (b : ℕ → ℕ)
    (hcofinal : Tendsto b atTop atTop) :
    Tendsto (fun k => primorialError (b k)) atTop (𝓝 0) ↔
      qOne ∈ ZetaTwoProbability.qSquarefreeCRTSpan.topologicalClosure := by
  constructor
  · intro hzero
    have hlim := tendsto_nhds_unique (primorialError_tendsto.comp hcofinal) hzero
    rw [sq_eq_zero_iff, norm_eq_zero, sub_eq_zero, eq_comm,
      Submodule.starProjection_eq_self_iff] at hlim
    exact hlim
  · intro hmem
    exact (primorialError_tendsto_zero_iff.mpr hmem).comp hcofinal

/-- The sequence is the actual arithmetic projection sequence at every endpoint. -/
theorem closure_iff_packetRelativeGain_not_summable
    (b : ℕ → ℕ) (hb : Monotone b) (hcofinal : Tendsto b atTop atTop) :
    qOne ∈ ZetaTwoProbability.qSquarefreeCRTSpan.topologicalClosure ↔
      ¬ Summable (packetRelativeGain b) :=
  (packetError_tendsto_zero_iff b hcofinal).symm.trans
    (residual_tendsto_zero_iff_not_summable (primorialError_pos (b 0))
      (packetRelativeGain_nonneg b) (packetRelativeGain_lt_one b hb)
      (packet_error_relativeGain_step b hb))

theorem riemannHypothesis_of_packetRelativeGain_not_summable
    (b : ℕ → ℕ) (hb : Monotone b) (hcofinal : Tendsto b atTop atTop)
    (h : ¬ Summable (packetRelativeGain b)) : RiemannHypothesis := by
  apply ZetaTwoParetoTransfer.riemannHypothesis_of_qOne_mem_squarefree_closure
  rw [QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure]
  exact (closure_iff_packetRelativeGain_not_summable b hb hcofinal).mpr h

/-- A summable total deficit is allowed at infinitely many packets. -/
theorem riemannHypothesis_of_packet_lower_with_summable_defect
    (b : ℕ → ℕ) (hb : Monotone b) (hcofinal : Tendsto b atTop atTop)
    {a ε : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (hdiv : ¬ Summable a)
    (hε : Summable ε)
    (hlower : ∀ k, a k ≤ packetRelativeGain b k + ε k) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_packetRelativeGain_not_summable b hb hcofinal
  intro hs
  exact hdiv (Summable.of_nonneg_of_le ha hlower (hs.add hε))

end RiemannResearch.RH.QPrimorialPacketGain
