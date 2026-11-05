/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QDisplacementTailTests
import RiemannResearch.RH.QResolventHarmonicPrefix

/-! # Projecting the first N residual coordinates

One projection of a finitely supported input suffices to approximate the
displacement on physical windows of length (N + 2) ^ 2 with vanishing harmonic
error. The input is the head of the actual Pareto residual.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QSquarefreeDisplacementRegularity
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage QSquarefreeDisplacementRigidity
open QSquarefreeDisplacementResolvent QShiftedReciprocal QAnnihilatorTailEscape
open QFiniteSupportDualCriterion

/-- One projection applied to N known source coordinates, if these are supplied. -/
def projectedResidualHead (N : ℕ) : QHilbert :=
  closure.starProjection (B (finiteHead N pResidual))

/-- Exact signed remainder including the complete tail of the Pareto residual. -/
theorem projectedResidualHead_error (N : ℕ) :
    displacement - projectedResidualHead N = closure.starProjection (B (tail N pResidual)) := by
  rw [displacement_eq_projected_pResidual, projectedResidualHead, tail, map_sub, map_sub]

theorem projectedResidualHead_scaled_error (N : ℕ) :
    ((N : ℝ) + 2) * ‖displacement - projectedResidualHead N‖ ≤ ‖tail N pResidual‖ := by
  have hz (n : ℕ) (hn : n ≤ N) : qSequence (tail N pResidual) n = 0 := by
    cases n with
    | zero => exact qSequence_zero _
    | succ k =>
      change (pResidual k - finiteHead N pResidual k) / Real.sqrt (qWeight k) = 0
      rw [finiteHead_apply_of_lt _ _ _ (by omega), sub_self, zero_div]
  rw [projectedResidualHead_error]
  have hp (f : QHilbert) : ‖closure.starProjection f‖ ≤ ‖f‖ := by
    exact (closure.starProjection.le_opNorm f).trans (by
      simpa using mul_le_mul_of_nonneg_right (Submodule.starProjection_norm_le closure)
        (norm_nonneg f))
  exact (mul_le_mul_of_nonneg_left (hp _) (by positivity)).trans
    (scaled_B_norm_le_of_head _ _ hz)

/-- No iteration is needed to keep a square-length physical window accurate. -/
theorem projectedResidualHead_harmonic_error (N X : ℕ) (hX : X ≤ (N + 2) ^ 2) :
    |minimumHarmonicPrefix X - minimumHarmonicPrefixOf (projectedResidualHead N) X| ≤
      Real.sqrt zetaTwo * ‖tail N pResidual‖ := by
  have hR : (X : ℝ) ≤ ((N : ℝ) + 2) ^ 2 := by exact_mod_cast hX
  have hs : Real.sqrt (X : ℝ) ≤ (N : ℝ) + 2 := Real.sqrt_le_iff.mpr ⟨by positivity, hR⟩
  calc
    _ ≤ Real.sqrt (X : ℝ) * Real.sqrt zetaTwo * ‖displacement - projectedResidualHead N‖ :=
      minimumHarmonicPrefixOf_error _ _ _
    _ ≤ ((N : ℝ) + 2) * Real.sqrt zetaTwo * ‖displacement - projectedResidualHead N‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _))
        (norm_nonneg _)
    _ = Real.sqrt zetaTwo * (((N : ℝ) + 2) * ‖displacement - projectedResidualHead N‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (projectedResidualHead_scaled_error N) (Real.sqrt_nonneg _)

/-- The uniform allowance on the square-length window actually tends to zero. -/
theorem projectedResidualHead_harmonic_error_tendsto_zero :
    Tendsto (fun N : ℕ => |minimumHarmonicPrefix ((N + 2) ^ 2) -
      minimumHarmonicPrefixOf (projectedResidualHead N) ((N + 2) ^ 2)|) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => abs_nonneg _)
    (fun N => projectedResidualHead_harmonic_error N _ le_rfl)
  simpa using ((tail_tendsto_zero pResidual).norm.const_mul (Real.sqrt zetaTwo))

end RiemannResearch.RH.QSquarefreeDisplacementRegularity
