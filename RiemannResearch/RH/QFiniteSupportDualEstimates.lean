/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.DenseProjectionTesting
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QMobiusExactHead
import RiemannResearch.RH.QSquarefreeSublinearHeads
import RiemannResearch.RH.CanonicalMobiusFullEnergy
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Tactic.Linarith

/-!
# Signed finite-support dual estimates

Source: continuation of the user's uniform-dual-bound request, 22 October 2026.
The exact Möbius head identity gives the signed pairing identity first, then
a support-dependent dual bound. Existing unconditional Möbius energy estimates
give sublinear squared constants. They do not give a constant uniform in the
support, and therefore do not discharge the RH consumer's Open hypothesis.
No mathematical novelty is claimed.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QFiniteSupportDualEstimates
open ZetaTwoHilbert QFiniteSupportDualCriterion
open RiemannResearch.Analysis.DenseProjectionTesting

/-- Exact signed pairing, before the Cauchy--Schwarz estimate. -/
theorem exactHead_finite_test_pairing (M : ℕ) (a : QHilbert) :
    inner ℝ (QMobiusExactHead.exactHead M) (finiteHead M a) =
      inner ℝ qOne (finiteHead M a) := by
  apply inner_finiteHead_eq_of_matching_head
  intro k hk hkM
  rw [QMobiusExactHead.exactHead_exact M k hk hkM]
  simp [qOneSequence, Nat.ne_of_gt hk]

/-- The complete Q norm of the concrete Möbius exact-head interpolant. -/
def dualHeadConstant (M : ℕ) : ℝ := ‖QMobiusExactHead.exactHead M‖

/-- Unconditional for all signed tests, but the constant depends on the support. -/
theorem finiteHead_dual_bound (M : ℕ) (a : QHilbert) :
    |inner ℝ qOne (finiteHead M a)| ≤ dualHeadConstant M *
      ‖QFullResidueProjection.closure.starProjection (finiteHead M a)‖ := by
  have hf : QMobiusExactHead.exactHead M ∈ QFullResidueProjection.closure :=
    QFullResidueProjection.legalSpan.le_topologicalClosure
      (QMobiusExactHead.exactHead_mem_legalSpan M)
  rw [← exactHead_finite_test_pairing M a,
    inner_eq_projected_test QFullResidueProjection.closure hf (finiteHead M a)]
  exact abs_real_inner_le_norm _ _

/-- Sublinear squared constants do not establish bounded constants. -/
theorem dualHeadConstant_sq_sublinear :
    Tendsto (fun M => dualHeadConstant M ^ 2 / (M : ℝ)) atTop (𝓝 0) := by
  simpa only [dualHeadConstant] using QSquarefreeSublinearHeads.exactHead_sublinear

theorem dualHeadConstant_sq_lt (M : ℕ) (hM : 0 < M) :
    dualHeadConstant M ^ 2 < 8 * (M : ℝ) / ZetaTwoProbability.zetaTwo := by
  have he := ZetaTwoParetoTransfer.zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq
    (QMobiusExactHead.exactHead M)
  rw [QSquarefreeSublinearHeads.toPareto_exactHead] at he
  have hp := Pareto.canonicalMobiusHilbert_norm_sq_lt_four_mul M hM
  apply (lt_div_iff₀ ZetaTwoProbability.zetaTwo_pos).mpr
  dsimp [dualHeadConstant]
  nlinarith

end RiemannResearch.RH.QFiniteSupportDualEstimates
