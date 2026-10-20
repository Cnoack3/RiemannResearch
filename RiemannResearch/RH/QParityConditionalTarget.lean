/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QResidueConditional
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoPolygammaResidues
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.RH.ZetaTwoProbability
import Lean.Elab.Tactic.Omega
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.Analysis.ScreenedCarry
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A literal parity-conditional target for squarefree closure

Source: the user-directed infinite-CRT continuation of 20 October 2026.
The conditional values are the complete inverse-square fiber sums already
constructed in `QResidueConditional`; no finite-tail truncation or Haar
replacement occurs. Conditioning the legal atom g_6 onto parity gives a
nonzero constant coefficient plus the old legal atom g_2. Its membership
in the closed squarefree legal span is therefore exactly the original
constant-target closure obligation, not an unconditional solution of it.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QParityConditionalTarget
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative QResidueConditional
open RiemannResearch.Analysis.ScreenedCarry

/-- Reconstruct a parity vector from the two complete conditional values.
For bounded inputs these are the actual Q-conditional means. -/
def parityConditional (f : ℕ → ℝ) : QHilbert :=
  (conditionalValue 2 2 f) • qOne +
    (2 * (conditionalValue 2 1 f - conditionalValue 2 2 f)) • qResidue 2

/-- Exact physical sequence; zero is the auxiliary zero coordinate. -/
theorem parityConditional_sequence (f : ℕ → ℝ) (n : ℕ) :
    qSequence (parityConditional f) n =
      conditionalValue 2 2 f * qOneSequence n +
        (2 * (conditionalValue 2 1 f - conditionalValue 2 2 f)) *
          residueFraction 2 n := by
  change qSequenceLinear ((conditionalValue 2 2 f) • qOne +
    (2 * (conditionalValue 2 1 f - conditionalValue 2 2 f)) • qResidue 2) n = _
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change conditionalValue 2 2 f * qSequence qOne n +
    (2 * (conditionalValue 2 1 f - conditionalValue 2 2 f)) *
      qSequence (qResidue 2) n = _
  rw [qSequence_qOne, qSequence_qResidue]

@[simp] theorem parityConditional_odd_value (f : ℕ → ℝ) :
    qSequence (parityConditional f) 1 = conditionalValue 2 1 f := by
  rw [parityConditional_sequence]
  norm_num [qOneSequence, residueFraction]; ring

@[simp] theorem parityConditional_even_value (f : ℕ → ℝ) :
    qSequence (parityConditional f) 2 = conditionalValue 2 2 f := by
  rw [parityConditional_sequence]
  norm_num [qOneSequence, residueFraction]

/-- Positive physical indices use exactly their parity-class conditional mean. -/
theorem parityConditional_sequence_pos (f : ℕ → ℝ) (n : ℕ) (hn : 0 < n) :
    qSequence (parityConditional f) n =
      if 2 ∣ n then conditionalValue 2 2 f else conditionalValue 2 1 f := by
  rw [parityConditional_sequence]
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  rcases Nat.mod_two_eq_zero_or_one n with hm | hm
  · have hd : 2 ∣ n := Nat.dvd_of_mod_eq_zero hm
    simp [qOneSequence, hn0, residueFraction, hd, hm]
  · have hd : ¬ 2 ∣ n := by
      intro hd
      have := Nat.mod_eq_zero_of_dvd hd
      omega
    simp [qOneSequence, hn0, residueFraction, hd, hm]; ring

/-- Parity conditioning of the squarefree legal conductor six. -/
def paritySix : QHilbert := parityConditional (residueFraction 6)

/-- The even fiber coefficient is the complete Q mean of g_3. -/
theorem paritySix_even_mean :
    conditionalValue 2 2 (residueFraction 6) =
      inversePowerMean 0 (residueFraction 3) := by
  simpa using conditionalValue_zero_residue 2 3 (by norm_num)

theorem paritySix_even_mean_pos :
    0 < conditionalValue 2 2 (residueFraction 6) := by
  rw [paritySix_even_mean]
  exact residue_mean_pos 3 (by norm_num)

/-- Any subspace containing g_2 contains this conditional target exactly
when it contains the constant target. No closedness is required. -/
theorem paritySix_mem_iff (V : Submodule ℝ QHilbert)
    (h2 : qResidue 2 ∈ V) : paritySix ∈ V ↔ qOne ∈ V := by
  constructor
  · intro h
    have hmul : (conditionalValue 2 2 (residueFraction 6)) • qOne ∈ V := by
      have ht := V.sub_mem h (V.smul_mem
        (2 * (conditionalValue 2 1 (residueFraction 6) -
          conditionalValue 2 2 (residueFraction 6))) h2)
      simpa only [paritySix, parityConditional, add_sub_cancel_right] using ht
    have ht := V.smul_mem (conditionalValue 2 2 (residueFraction 6))⁻¹ hmul
    simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt paritySix_even_mean_pos),
      one_smul] using ht
  · intro h
    exact V.add_mem (V.smul_mem _ h) (V.smul_mem _ h2)

/-- The screen is the actual orthogonal residual operator I-P_V. -/
theorem screen_paritySix (V : Submodule ℝ QHilbert) [V.HasOrthogonalProjection]
    (h2 : qResidue 2 ∈ V) :
    screen V paritySix =
      conditionalValue 2 2 (residueFraction 6) • screen V qOne := by
  unfold paritySix parityConditional
  rw [map_add, map_smul, map_smul, screen_of_mem V h2, smul_zero, add_zero]

/-- Exact complete-Q energy scaling, rather than just a one-sided bound. -/
theorem norm_screen_paritySix_sq (V : Submodule ℝ QHilbert)
    [V.HasOrthogonalProjection] (h2 : qResidue 2 ∈ V) :
    ‖screen V paritySix‖ ^ 2 =
      (conditionalValue 2 2 (residueFraction 6)) ^ 2 * ‖screen V qOne‖ ^ 2 := by
  rw [screen_paritySix V h2, norm_smul, Real.norm_eq_abs,
    abs_of_pos paritySix_even_mean_pos, mul_pow]

/-- The finite squarefree stage already contains parity once nonempty. -/
theorem qResidue_two_mem_stage (n : ℕ) (hn : 0 < n) :
    qResidue 2 ∈ ZetaTwoOptimizerStage.stage n := by
  change qResidue 2 ∈ Submodule.span ℝ
    (Set.range (fun i : Fin n => ZetaTwoOptimizerStage.squarefreeAtom i.val))
  apply Submodule.subset_span
  refine ⟨⟨0, hn⟩, ?_⟩
  simp [ZetaTwoOptimizerStage.squarefreeAtom, Nat.prime_two.squarefree]

theorem qResidue_two_mem_closure :
    qResidue 2 ∈ ZetaTwoOptimizerStage.closure := by
  change qResidue 2 ∈ (Submodule.span ℝ
    (Set.range ZetaTwoOptimizerStage.squarefreeAtom)).topologicalClosure
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  refine ⟨0, ?_⟩
  simp [ZetaTwoOptimizerStage.squarefreeAtom, Nat.prime_two.squarefree]

/-- A single conditional image supplies an equivalent closure target. -/
theorem paritySix_mem_closure_iff :
    paritySix ∈ ZetaTwoOptimizerStage.closure ↔
      qOne ∈ ZetaTwoOptimizerStage.closure :=
  paritySix_mem_iff _ qResidue_two_mem_closure

/-- Exact finite-stage errors for the new target. -/
theorem paritySix_stage_error (n : ℕ) (hn : 0 < n) :
    ‖paritySix - (ZetaTwoOptimizerStage.stage n).starProjection paritySix‖ ^ 2 =
      (conditionalValue 2 2 (residueFraction 6)) ^ 2 * ZetaTwoOptimizerStage.error n := by
  simpa only [screen_apply, ZetaTwoOptimizerStage.error,
    ZetaTwoOptimizerStage.residual, ZetaTwoOptimizerStage.optimizer] using
      norm_screen_paritySix_sq (ZetaTwoOptimizerStage.stage n)
        (qResidue_two_mem_stage n hn)

/-- The existing actual-squarefree exhaustion criterion consumes this target. -/
theorem paritySix_mem_closure_iff_error_tendsto_zero :
    paritySix ∈ ZetaTwoOptimizerStage.closure ↔
      Tendsto ZetaTwoOptimizerStage.error atTop (𝓝 0) := by
  rw [paritySix_mem_closure_iff,
    ZetaTwoOptimizerStage.error_tendsto_zero_iff_mem_closure]

/-- The input to the conditional projection is itself a squarefree legal atom. -/
theorem qResidue_six_mem_closure :
    qResidue 6 ∈ ZetaTwoOptimizerStage.closure := by
  change qResidue 6 ∈ (Submodule.span ℝ
    (Set.range ZetaTwoOptimizerStage.squarefreeAtom)).topologicalClosure
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  refine ⟨4, ?_⟩
  have h6 : Squarefree (6 : ℕ) := by
    change Squarefree ((2 : ℕ) * 3)
    exact Nat.squarefree_mul_iff.mpr
      ⟨by decide, Nat.prime_two.squarefree, (by norm_num : Nat.Prime 3).squarefree⟩
  simp only [ZetaTwoOptimizerStage.squarefreeAtom, show 4 + 2 = 6 from rfl,
    if_pos h6]

/-- Preservation of the closed legal span by parity conditioning is
equivalent to the original constant-target closure obligation. -/
theorem parity_preserves_closure_iff :
    (∀ f ∈ ZetaTwoOptimizerStage.closure,
      parityConditional (qSequence f) ∈ ZetaTwoOptimizerStage.closure) ↔
        qOne ∈ ZetaTwoOptimizerStage.closure := by
  constructor
  · intro h
    apply paritySix_mem_closure_iff.mp
    simpa only [qSequence_qResidue, paritySix] using
      h (qResidue 6) qResidue_six_mem_closure
  · intro h f _
    exact ZetaTwoOptimizerStage.closure.add_mem
      (ZetaTwoOptimizerStage.closure.smul_mem _ h)
      (ZetaTwoOptimizerStage.closure.smul_mem _ qResidue_two_mem_closure)

/-- Conditional research reduction: membership of this single actual
conditional image remains Open. The existing Mellin transfer proves RH
once that membership is supplied. -/
theorem riemannHypothesis_of_paritySix_mem_closure
    (h : paritySix ∈ ZetaTwoOptimizerStage.closure) : RiemannHypothesis :=
  ZetaTwoParetoTransfer.riemannHypothesis_of_qOne_mem_squarefree_closure
    (paritySix_mem_closure_iff.mp h)

end RiemannResearch.RH.QParityConditionalTarget
