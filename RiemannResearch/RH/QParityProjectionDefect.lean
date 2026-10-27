/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QParityConditionalTarget
import RiemannResearch.RH.QParityGeometry
import RiemannResearch.RH.QDivisorLegality
import RiemannResearch.RH.QDivisibilityHilbertMoments
import RiemannResearch.Analysis.ProjectionCompressionDefect
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Exact parity leakage of the actual legal projection

The parity operator is the actual orthogonal projection onto the two-dimensional
space of parity-constant physical sequences. This definition applies to every
Q-Hilbert vector, with no boundedness hypothesis on the optimizer.

For any projection space containing g_2, put r=1-P_V1 and D=||r||^2.
The parity projection of r is exactly 4D times the even indicator, and the
parity leakage of the optimizer is exactly D(1-4D). Containing g_3 gives
the strict bound D<1/4 by its positive pairing with the even indicator.
Thus parity-periodicity of the actual limiting optimizer already requires
the original constant-membership conclusion.

Source: the user-directed CRT/profinite continuation, 20 October 2026.
The proof reuses complete-Q indicator moments and ordinary orthogonal
projection identities, without a Haar replacement or a tail truncation.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QParityProjectionDefect
open ZetaTwoHilbert ZetaTwoProbability QDivisibilityDensity QDivisorLegality
open RiemannResearch.Analysis.ProjectionCompression

/-- The exact parity-cylinder subspace in the complete Q metric. -/
def paritySpace : Submodule ℝ QHilbert :=
  Submodule.span ℝ ({qOne, qResidue 2} : Set QHilbert)

instance paritySpace_finiteDimensional : FiniteDimensional ℝ paritySpace :=
  FiniteDimensional.span_of_finite ℝ
    ((Set.finite_singleton (qResidue 2)).insert qOne)

theorem qOne_mem_paritySpace : qOne ∈ paritySpace :=
  Submodule.subset_span (by simp)

theorem qResidue_two_mem_paritySpace : qResidue 2 ∈ paritySpace :=
  Submodule.subset_span (by simp)

theorem even_mem_paritySpace : qDivisor 2 ∈ paritySpace := by
  rw [qDivisor_two_eq]
  exact paritySpace.sub_mem qOne_mem_paritySpace
    (paritySpace.smul_mem _ qResidue_two_mem_paritySpace)

variable (V : Submodule ℝ QHilbert) [V.HasOrthogonalProjection]

private theorem residual_mean :
    inner ℝ (qOne - V.starProjection qOne) qOne =
      ‖qOne - V.starProjection qOne‖ ^ 2 := by
  have ho := Submodule.starProjection_inner_eq_zero qOne (V.starProjection qOne)
    (V.starProjection_apply_mem qOne)
  calc
    _ = inner ℝ (qOne - V.starProjection qOne) (qOne - V.starProjection qOne) := by
      rw [inner_sub_right, ho, sub_zero]
    _ = _ := real_inner_self_eq_norm_sq _

/-- Complete parity conditioning of an orthogonal target residual. -/
theorem parity_projection_residual (h2 : qResidue 2 ∈ V) :
    paritySpace.starProjection (qOne - V.starProjection qOne) =
      (4 * ‖qOne - V.starProjection qOne‖ ^ 2) • qDivisor 2 := by
  let r := qOne - V.starProjection qOne
  let D := ‖r‖ ^ 2
  have hmean : inner ℝ r qOne = D := residual_mean V
  have hodd : inner ℝ r (qResidue 2) = 0 :=
    Submodule.starProjection_inner_eq_zero qOne (qResidue 2) h2
  have hevenOne : inner ℝ (qDivisor 2) qOne = (1 / 4 : ℝ) := by
    rw [real_inner_comm, qOne_inner_qDivisor 2 (by decide)]
    norm_num
  have hevenOdd : inner ℝ (qDivisor 2) (qResidue 2) = 0 := by
    rw [real_inner_comm]
    exact qResidue_inner_qDivisor_eq_zero 2 2 (by decide) (dvd_refl _)
  change paritySpace.starProjection r = (4 * D) • qDivisor 2
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (paritySpace.smul_mem (4 * D) even_mem_paritySpace)
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · rw [inner_sub_left, real_inner_smul_left, hmean, hevenOne]
        ring
      · rw [inner_sub_left, real_inner_smul_left, hodd, hevenOdd]
        ring
  | zero => simp
  | add y z hy hz ihy ihz => rw [inner_add_right, ihy, ihz, add_zero]
  | smul c y hy ih => rw [real_inner_smul_right, ih, mul_zero]

/-- The actual optimizer's even conditional value is 1-4D, and its odd value is one. -/
theorem parity_projection_optimizer (h2 : qResidue 2 ∈ V) :
    paritySpace.starProjection (V.starProjection qOne) =
      qOne - (4 * ‖qOne - V.starProjection qOne‖ ^ 2) • qDivisor 2 := by
  have he : V.starProjection qOne = qOne - (qOne - V.starProjection qOne) := by abel
  calc
    _ = paritySpace.starProjection (qOne - (qOne - V.starProjection qOne)) :=
      congrArg paritySpace.starProjection he
    _ = _ := by
      rw [map_sub, Submodule.starProjection_eq_self_iff.mpr qOne_mem_paritySpace,
        parity_projection_residual V h2]

/-- All norm-square mass of the parity-conditioned residual is retained exactly. -/
theorem parity_projection_residual_norm_sq (h2 : qResidue 2 ∈ V) :
    ‖paritySpace.starProjection (qOne - V.starProjection qOne)‖ ^ 2 =
      4 * (‖qOne - V.starProjection qOne‖ ^ 2) ^ 2 := by
  rw [parity_projection_residual V h2, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, qDivisor_norm_sq 2 (by decide)]
  norm_num
  ring

/-- Exact variance of the parity-conditioned residual. -/
theorem parity_projection_residual_centered_norm_sq (h2 : qResidue 2 ∈ V) :
    ‖paritySpace.starProjection (qOne - V.starProjection qOne) -
      (‖qOne - V.starProjection qOne‖ ^ 2) • qOne‖ ^ 2 =
        3 * (‖qOne - V.starProjection qOne‖ ^ 2) ^ 2 := by
  have hmean : inner ℝ (qDivisor 2) qOne = (1 / 4 : ℝ) := by
    rw [real_inner_comm, qOne_inner_qDivisor 2 (by decide)]
    norm_num
  rw [norm_sub_sq_real, parity_projection_residual_norm_sq V h2,
    parity_projection_residual V h2, real_inner_smul_left,
    real_inner_smul_right, hmean, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, qOne_norm_sq]
  ring

/-- Mean-independence from parity is exactly target membership, not a
consequence of independent prime valuations. -/
theorem parity_projection_residual_mean_independent_iff (h2 : qResidue 2 ∈ V) :
    paritySpace.starProjection (qOne - V.starProjection qOne) =
      (‖qOne - V.starProjection qOne‖ ^ 2) • qOne ↔ qOne ∈ V := by
  constructor
  · intro h
    have hv := parity_projection_residual_centered_norm_sq V h2
    rw [h, sub_self, norm_zero] at hv
    have hz : ‖qOne - V.starProjection qOne‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg (‖qOne - V.starProjection qOne‖ ^ 2)]
    have hn : ‖qOne - V.starProjection qOne‖ = 0 := by
      nlinarith [norm_nonneg (qOne - V.starProjection qOne)]
    exact Submodule.starProjection_eq_self_iff.mp
      (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm
  · intro h
    simp [Submodule.starProjection_eq_self_iff.mpr h]

/-- Exact complete-Q parity leakage of the actual optimizer. -/
theorem optimizer_parity_leakage_exact (h2 : qResidue 2 ∈ V) :
    ‖V.starProjection qOne - paritySpace.starProjection (V.starProjection qOne)‖ ^ 2 =
      ‖qOne - V.starProjection qOne‖ ^ 2 *
        (1 - 4 * ‖qOne - V.starProjection qOne‖ ^ 2) := by
  have hpy := projection_pythagoras paritySpace (qOne - V.starProjection qOne)
  rw [parity_projection_residual_norm_sq V h2] at hpy
  have he : V.starProjection qOne - paritySpace.starProjection (V.starProjection qOne) =
      -((qOne - V.starProjection qOne) -
        paritySpace.starProjection (qOne - V.starProjection qOne)) := by
    rw [map_sub, Submodule.starProjection_eq_self_iff.mpr qOne_mem_paritySpace]
    abel
  rw [he, norm_neg]
  nlinarith

/-- A positive legal test prevents equality in the elementary parity error cap. -/
theorem even_inner_three_pos : 0 < inner ℝ (qDivisor 2) (qResidue 3) := by
  rw [qInner_weighted]
  refine (qSequence_product_summable (qDivisor 2) (qResidue 3)).tsum_pos
    ?_ 2 ?_
  · intro n
    simp only [qSequence_qDivisor, qSequence_qResidue]
    have hi : 0 ≤ positiveDivisor 2 n := by
      unfold positiveDivisor
      split_ifs <;> norm_num
    have hg : 0 ≤ ArithmeticCumulative.residueFraction 3 n := by
      unfold ArithmeticCumulative.residueFraction
      positivity
    exact mul_nonneg (mul_nonneg (positiveQWeight_nonneg n) hi) hg
  · simp only [qSequence_qDivisor, qSequence_qResidue]
    norm_num [positiveDivisor, ArithmeticCumulative.residueFraction, positiveQWeight]
    positivity [zetaTwo_pos]

/-- Every projection space containing g_2 and g_3 has error strictly below 1/4. -/
theorem error_lt_quarter (h2 : qResidue 2 ∈ V) (h3 : qResidue 3 ∈ V) :
    ‖qOne - V.starProjection qOne‖ ^ 2 < (1 / 4 : ℝ) := by
  have hne : V.starProjection (qDivisor 2) ≠ 0 := by
    intro hz
    have ho := Submodule.starProjection_inner_eq_zero (qDivisor 2) (qResidue 3) h3
    rw [hz, sub_zero] at ho
    exact (ne_of_gt even_inner_three_pos) ho
  have hp := projection_pythagoras V (qDivisor 2)
  have he : qDivisor 2 - V.starProjection (qDivisor 2) =
      qOne - V.starProjection qOne := by
    rw [qDivisor_two_eq, map_sub, map_smul,
      Submodule.starProjection_eq_self_iff.mpr h2]
    abel
  rw [he, qDivisor_norm_sq 2 (by decide)] at hp
  have hpos := sq_pos_of_pos (norm_pos_iff.mpr hne)
  norm_num at hp
  linarith

/-- Periodicity of the actual legal optimizer already implies exact target membership. -/
theorem optimizer_mem_parity_iff (h2 : qResidue 2 ∈ V) (h3 : qResidue 3 ∈ V) :
    V.starProjection qOne ∈ paritySpace ↔ qOne ∈ V := by
  constructor
  · intro h
    have he := optimizer_parity_leakage_exact V h2
    rw [Submodule.starProjection_eq_self_iff.mpr h, sub_self, norm_zero,
      zero_pow (by decide : 2 ≠ 0)] at he
    have hstrict := error_lt_quarter V h2 h3
    have hfactor : 0 < 1 - 4 * ‖qOne - V.starProjection qOne‖ ^ 2 := by linarith
    have hzero : ‖qOne - V.starProjection qOne‖ ^ 2 = 0 :=
      (mul_eq_zero.mp he.symm).resolve_right (ne_of_gt hfactor)
    have hnorm : ‖qOne - V.starProjection qOne‖ = 0 := by nlinarith [norm_nonneg (qOne - V.starProjection qOne)]
    have heq := sub_eq_zero.mp (norm_eq_zero.mp hnorm)
    exact Submodule.starProjection_eq_self_iff.mp heq.symm
  · intro h
    rw [Submodule.starProjection_eq_self_iff.mpr h]
    exact qOne_mem_paritySpace

private theorem qResidue_three_mem_closure :
    qResidue 3 ∈ ZetaTwoOptimizerStage.closure := by
  change qResidue 3 ∈ (Submodule.span ℝ
    (Set.range ZetaTwoOptimizerStage.squarefreeAtom)).topologicalClosure
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  refine ⟨1, ?_⟩
  simp [ZetaTwoOptimizerStage.squarefreeAtom, Nat.prime_three.squarefree]

/-- Exact identity for the actual infinite legal optimizer and its complete residual. -/
theorem limiting_optimizer_parity_leakage_exact :
    ‖ZetaTwoOptimizerStage.closure.starProjection qOne -
      paritySpace.starProjection (ZetaTwoOptimizerStage.closure.starProjection qOne)‖ ^ 2 =
      ‖ZetaTwoOptimizerStage.limitingResidual‖ ^ 2 *
        (1 - 4 * ‖ZetaTwoOptimizerStage.limitingResidual‖ ^ 2) :=
  optimizer_parity_leakage_exact ZetaTwoOptimizerStage.closure
    QParityConditionalTarget.qResidue_two_mem_closure

theorem limiting_error_lt_quarter :
    ‖ZetaTwoOptimizerStage.limitingResidual‖ ^ 2 < (1 / 4 : ℝ) :=
  error_lt_quarter ZetaTwoOptimizerStage.closure
    QParityConditionalTarget.qResidue_two_mem_closure qResidue_three_mem_closure

/-- Parity-periodicity of the actual infinite projection is equivalent to constant membership. -/
theorem limiting_optimizer_two_periodic_iff :
    (∀ n : ℕ, 0 < n →
      qSequence (ZetaTwoOptimizerStage.closure.starProjection qOne) (n + 2) =
        qSequence (ZetaTwoOptimizerStage.closure.starProjection qOne) n) ↔
      qOne ∈ ZetaTwoOptimizerStage.closure := by
  constructor
  · intro hp
    apply (optimizer_mem_parity_iff ZetaTwoOptimizerStage.closure
      QParityConditionalTarget.qResidue_two_mem_closure qResidue_three_mem_closure).mp
    rw [qHilbert_eq_parity_of_two_periodic _ hp]
    exact paritySpace.add_mem (paritySpace.smul_mem _ qOne_mem_paritySpace)
      (paritySpace.smul_mem _ qResidue_two_mem_paritySpace)
  · intro h n hn
    rw [Submodule.starProjection_eq_self_iff.mpr h, qSequence_qOne]
    simp [qOneSequence, Nat.ne_of_gt hn, show n + 2 ≠ 0 by omega]

/-- A conditional RH consumer; parity-periodicity is the unresolved premise. -/
theorem riemannHypothesis_of_limiting_optimizer_two_periodic
    (hp : ∀ n : ℕ, 0 < n →
      qSequence (ZetaTwoOptimizerStage.closure.starProjection qOne) (n + 2) =
        qSequence (ZetaTwoOptimizerStage.closure.starProjection qOne) n) : RiemannHypothesis :=
  ZetaTwoParetoTransfer.riemannHypothesis_of_qOne_mem_squarefree_closure
    (limiting_optimizer_two_periodic_iff.mp hp)

end RiemannResearch.RH.QParityProjectionDefect
