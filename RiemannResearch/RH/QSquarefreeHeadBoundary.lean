/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import Mathlib.Tactic.Positivity
import RiemannResearch.RH.MobiusResidualEscape
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.RH.SquarefreeMobiusProjection
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoParetoTransfer
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The exact finite squarefree head boundary

Finite Möbius reconstruction supplies all head coordinates up to one linear
slope.  The omitted nonsquarefree coordinates and this single scalar slope
are precisely the constraints for a head to come from the actual stage.
This is a finite-head characterization, not a density or norm estimate.

Source: finite inversion already established in MobiusResidualEscape,
combined with the squarefree-coordinate framework in SquarefreeMobiusProjection.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeHeadBoundary
open Pareto Pareto.CoefficientStabilization ZetaTwoHilbert
open ZetaTwoParetoTransfer SquarefreeMobiusProjection
open RiemannResearch.Analysis.ExhaustiveWalk

def headSynthesis (N : ℕ) (f : QHilbert) : QHilbert :=
  ∑ i : Fin N, qCoefficientCLM (i.val + 2) f • qResidue (i.val + 2)

/-- The one missing slope in finite Möbius reconstruction. -/
def headCharge (N : ℕ) (f : QHilbert) : ℝ :=
  qSequence f 1 - qSequence (headSynthesis N f) 1

theorem toPareto_headSynthesis (N : ℕ) (f : QHilbert) :
    toPareto (headSynthesis N f) = coordinatePartialSum (toPareto f) N := by
  change toParetoLinear (∑ i : Fin N,
    qCoefficientCLM (i.val + 2) f • qResidue (i.val + 2)) = _
  simp only [map_sum, map_smul]
  change (∑ i : Fin N, qCoefficientCLM (i.val + 2) f •
    toPareto (qResidue (i.val + 2))) = _
  simp only [toPareto_residueAtom]
  rfl

theorem headSynthesis_prefix (N : ℕ) (f : QHilbert) (k : ℕ) (hk : k ≤ N + 1) :
    qSequence (headSynthesis N f) k = qSequence f k - (k : ℝ) * headCharge N f := by
  have h := coordinatePartialSum_prefix_linear (toPareto f) N k hk
  rw [← toPareto_headSynthesis] at h
  change hilbertSequenceLinear (toPareto (headSynthesis N f) - toPareto f) k =
    (k : ℝ) * hilbertSequenceLinear (toPareto (headSynthesis N f) - toPareto f) 1 at h
  simp only [map_sub, Pi.sub_apply] at h
  change hilbertSequence (toPareto (headSynthesis N f)) k -
      hilbertSequence (toPareto f) k = (k : ℝ) *
      (hilbertSequence (toPareto (headSynthesis N f)) 1 -
        hilbertSequence (toPareto f) 1) at h
  simp only [toPareto_sequence] at h
  unfold headCharge
  linarith

theorem headCharge_eq_coefficients (N : ℕ) (f : QHilbert) :
    headCharge N f = qSequence f 1 -
      ∑ i : Fin N, qCoefficientCLM (i.val + 2) f / ((i.val + 2 : ℕ) : ℝ) := by
  unfold headCharge headSynthesis
  change qSequence f 1 - qSequenceLinear (∑ i : Fin N,
    qCoefficientCLM (i.val + 2) f • qResidue (i.val + 2)) 1 = _
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  change qCoefficientCLM (i.val + 2) f * qSequence (qResidue (i.val + 2)) 1 = _
  rw [qSequence_qResidue]
  simp [ArithmeticCumulative.residueFraction,
    Nat.mod_eq_of_lt (show 1 < i.val + 2 by omega), div_eq_mul_inv]

theorem headSynthesis_zero (N : ℕ) : headSynthesis N 0 = 0 := by
  simp [headSynthesis]

theorem headSynthesis_add (N : ℕ) (f g : QHilbert) :
    headSynthesis N (f + g) = headSynthesis N f + headSynthesis N g := by
  simp [headSynthesis, map_add, add_smul, Finset.sum_add_distrib]

theorem headSynthesis_smul (N : ℕ) (c : ℝ) (f : QHilbert) :
    headSynthesis N (c • f) = c • headSynthesis N f := by
  simp [headSynthesis, map_smul, mul_smul, Finset.smul_sum]

theorem headSynthesis_sub (N : ℕ) (f g : QHilbert) :
    headSynthesis N (f - g) = headSynthesis N f - headSynthesis N g := by
  simp [headSynthesis, map_sub, sub_smul, Finset.sum_sub_distrib]

theorem headCharge_sub (N : ℕ) (f g : QHilbert) :
    headCharge N (f - g) = headCharge N f - headCharge N g := by
  simp only [headCharge, headSynthesis_sub]
  change qSequenceLinear (f - g) 1 -
      qSequenceLinear (headSynthesis N f - headSynthesis N g) 1 = _
  simp only [map_sub, Pi.sub_apply]
  change (qSequence f 1 - qSequence g 1) -
      (qSequence (headSynthesis N f) 1 - qSequence (headSynthesis N g) 1) = _
  ring

theorem headSynthesis_qResidue (N : ℕ) (j : Fin N) :
    headSynthesis N (qResidue (j.val + 2)) = qResidue (j.val + 2) := by
  classical
  simp only [headSynthesis, q_coordinate_biorthogonal]
  have he (i : Fin N) : (i.val = j.val) ↔ i = j := Fin.ext_iff.symm
  simp only [he, ite_smul, one_smul, zero_smul]
  simp

theorem headSynthesis_eq_self_of_mem_stage (N : ℕ) (f : QHilbert)
    (hf : f ∈ ZetaTwoOptimizerStage.stage N) : headSynthesis N f = f := by
  classical
  unfold ZetaTwoOptimizerStage.stage walkSpan at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨i, rfl⟩ := hf
      change headSynthesis N (ZetaTwoOptimizerStage.squarefreeAtom i.val) = _
      by_cases hi : Squarefree (i.val + 2)
      · simpa only [ZetaTwoOptimizerStage.squarefreeAtom, if_pos hi, id_eq] using
          headSynthesis_qResidue N i
      · simp [ZetaTwoOptimizerStage.squarefreeAtom, hi, headSynthesis_zero]
  | zero => exact headSynthesis_zero N
  | add f g hf hg hif hig => rw [headSynthesis_add, hif, hig]
  | smul c f hf hif => rw [headSynthesis_smul, hif]

theorem headCharge_eq_zero_of_mem_stage (N : ℕ) (f : QHilbert)
    (hf : f ∈ ZetaTwoOptimizerStage.stage N) : headCharge N f = 0 := by
  simp [headCharge, headSynthesis_eq_self_of_mem_stage N f hf]

theorem headSynthesis_coefficient (N : ℕ) (f : QHilbert) (i : Fin N) :
    qCoefficientCLM (i.val + 2) (headSynthesis N f) = qCoefficientCLM (i.val + 2) f := by
  classical
  simp only [headSynthesis, map_sum, map_smul, smul_eq_mul, q_coordinate_biorthogonal]
  have he (j : Fin N) : (i.val = j.val) ↔ i = j := Fin.ext_iff.symm
  simp only [he]
  simp

theorem omitted_coordinate_zero_of_mem_stage (N : ℕ) (f : QHilbert)
    (hf : f ∈ ZetaTwoOptimizerStage.stage N) (i : ℕ) (hi : ¬Squarefree (i + 2)) :
    qCoefficientCLM (i + 2) f = 0 := by
  apply q_omitted_coordinate_zero i hi
  exact (Submodule.span ℝ (Set.range ZetaTwoOptimizerStage.squarefreeAtom)).le_topologicalClosure
    (walkSpan_le ZetaTwoOptimizerStage.squarefreeAtom id N hf)

theorem headSynthesis_mem_stage_iff (N : ℕ) (f : QHilbert) :
    headSynthesis N f ∈ ZetaTwoOptimizerStage.stage N ↔
      ∀ i : Fin N, ¬Squarefree (i.val + 2) → qCoefficientCLM (i.val + 2) f = 0 := by
  classical
  constructor
  · intro h i hi
    rw [← headSynthesis_coefficient N f i]
    exact omitted_coordinate_zero_of_mem_stage N _ h i.val hi
  · intro h
    unfold headSynthesis
    apply Submodule.sum_mem
    intro i hi
    by_cases hs : Squarefree (i.val + 2)
    · apply Submodule.smul_mem
      change qResidue (i.val + 2) ∈ walkSpan ZetaTwoOptimizerStage.squarefreeAtom id N
      apply Submodule.subset_span
      refine ⟨i, ?_⟩
      simp [ZetaTwoOptimizerStage.squarefreeAtom, hs, id_eq]
    · rw [h i hs, zero_smul]
      exact Submodule.zero_mem _

/-- Every coefficient on a prefix depends only on that prefix. -/
theorem coefficient_eq_of_head_eq (N : ℕ) (f g : QHilbert)
    (h : ∀ k : ℕ, k ≤ N + 1 → qSequence f k = qSequence g k)
    (i : Fin N) : qCoefficientCLM (i.val + 2) f = qCoefficientCLM (i.val + 2) g := by
  change -mobiusDifferenceCLM (i.val + 2) (toPareto f) =
    -mobiusDifferenceCLM (i.val + 2) (toPareto g)
  simp only [mobiusDifferenceCLM_apply, toPareto_sequence, mobiusDifference]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  have hle : d ≤ N + 1 := (Nat.le_of_dvd (by omega)
    (Nat.dvd_of_mem_divisors hd)).trans (by omega)
  rw [h d hle, h (d - 1) (by omega)]

theorem headSynthesis_eq_of_head_eq (N : ℕ) (f g : QHilbert)
    (h : ∀ k : ℕ, k ≤ N + 1 → qSequence f k = qSequence g k) :
    headSynthesis N f = headSynthesis N g := by
  unfold headSynthesis
  apply Finset.sum_congr rfl
  intro i hi
  rw [coefficient_eq_of_head_eq N f g h i]

/-- The first N+1 physical sites already determine an actual stage vector. -/
theorem stage_head_injective (N : ℕ) (f g : QHilbert)
    (hf : f ∈ ZetaTwoOptimizerStage.stage N) (hg : g ∈ ZetaTwoOptimizerStage.stage N)
    (h : ∀ k : ℕ, k ≤ N + 1 → qSequence f k = qSequence g k) : f = g := by
  have he := headSynthesis_eq_of_head_eq N f g h
  rwa [headSynthesis_eq_self_of_mem_stage N f hf,
    headSynthesis_eq_self_of_mem_stage N g hg] at he

/-- Complete finite-head characterization: omitted coordinates plus one charge. -/
theorem exists_stage_head_match_iff (N : ℕ) (f : QHilbert) :
    (∃ g ∈ ZetaTwoOptimizerStage.stage N,
      ∀ k : ℕ, k ≤ N + 1 → qSequence g k = qSequence f k) ↔
    (∀ i : Fin N, ¬Squarefree (i.val + 2) → qCoefficientCLM (i.val + 2) f = 0) ∧
      headCharge N f = 0 := by
  constructor
  · rintro ⟨g, hg, h⟩
    have hs := headSynthesis_eq_of_head_eq N g f h
    rw [headSynthesis_eq_self_of_mem_stage N g hg] at hs
    constructor
    · apply (headSynthesis_mem_stage_iff N f).mp
      rw [← hs]
      exact hg
    · unfold headCharge
      rw [← hs, h 1 (by omega), sub_self]
  · rintro ⟨ho, hc⟩
    refine ⟨headSynthesis N f, (headSynthesis_mem_stage_iff N f).mpr ho, ?_⟩
    intro k hk
    rw [headSynthesis_prefix N f k hk, hc, mul_zero, sub_zero]

theorem headCharge_qOne (N : ℕ) :
    headCharge N qOne = 1 + ∑ i : Fin N,
      (ArithmeticFunction.moebius (i.val + 2) : ℝ) / ((i.val + 2 : ℕ) : ℝ) := by
  rw [headCharge_eq_coefficients, qSequence_qOne]
  simp only [qOneSequence, show (1 : ℕ) ≠ 0 by omega, if_false]
  have ht (i : Fin N) := q_target_coordinate (i.val + 2) (by omega)
  simp_rw [ht]
  simp only [neg_div, Finset.sum_neg_distrib, sub_neg_eq_add]

/-- The actual optimizer residual has precisely the target's boundary defect. -/
theorem residual_headCharge (N : ℕ) :
    headCharge N (ZetaTwoOptimizerStage.residual N) = headCharge N qOne := by
  rw [ZetaTwoOptimizerStage.residual, headCharge_sub, ZetaTwoOptimizerStage.optimizer,
    headCharge_eq_zero_of_mem_stage N _
      ((ZetaTwoOptimizerStage.stage N).starProjection_apply_mem qOne), sub_zero]

/-- Every actual smoothed correction obeys the zero-charge boundary condition. -/
theorem movingCorrection_headCharge (N : ℕ) :
    headCharge N (QSquarefreeSmoothedProjection.movingCorrection N) = 0 := by
  apply headCharge_eq_zero_of_mem_stage
  exact (ZetaTwoOptimizerStage.stage N).starProjection_apply_mem _

open ZetaTwoOptimizerStage

/-- The finite boundary charge removes the seemingly last free head value:
the first N physical sites determine the stage with conductors through N+1. -/
theorem stage_eq_zero_of_head_zero (N : ℕ) (hN : 0 < N) (f : QHilbert)
    (hf : f ∈ stage N)
    (hzero : ∀ n : ℕ, n ≤ N → qSequence f n = 0) : f = 0 := by
  classical
  let last : Fin N := ⟨N - 1, by omega⟩
  have hcoef (j : Fin N) (hj : j ≠ last) :
      qCoefficientCLM (j.val + 2) f = 0 := by
    have hjlt : j.val < N - 1 := by
      have hneq : j.val ≠ N - 1 := by
        intro he
        apply hj
        exact Fin.ext he
      omega
    have he := coefficient_eq_of_head_eq (N - 1) f 0
      (fun k hk => by
        rw [hzero k (by omega)]
        change (0 : ℝ) = qSequenceLinear 0 k
        simp)
      (⟨j.val, hjlt⟩ : Fin (N - 1))
    simpa using he
  have hlast : last.val + 2 = N + 1 := by dsimp [last]; omega
  have hs : headSynthesis N f =
      qCoefficientCLM (N + 1) f • qResidue (N + 1) := by
    unfold headSynthesis
    rw [Finset.sum_eq_single last]
    · rw [hlast]
    · intro j hj hjlast
      rw [hcoef j hjlast, zero_smul]
    · simp
  have he : f = qCoefficientCLM (N + 1) f • qResidue (N + 1) :=
    (headSynthesis_eq_self_of_mem_stage N f hf).symm.trans hs
  have hz := hzero 1 (by omega)
  rw [he] at hz
  change qSequenceLinear (qCoefficientCLM (N + 1) f • qResidue (N + 1)) 1 = 0 at hz
  rw [map_smul] at hz
  change qCoefficientCLM (N + 1) f * qSequence (qResidue (N + 1)) 1 = 0 at hz
  rw [qSequence_qResidue] at hz
  simp only [ArithmeticCumulative.residueFraction,
    Nat.mod_eq_of_lt (show 1 < N + 1 by omega), Nat.cast_one] at hz
  have hc : qCoefficientCLM (N + 1) f = 0 :=
    (mul_eq_zero.mp hz).resolve_right (by positivity)
  simpa [hc] using he

theorem stage_le_of_active_cutoff (N D : ℕ) (hD : 2 ≤ D)
    (hcut : ∀ a : Fin N, Squarefree (a.val + 2) → a.val + 2 ≤ D) :
    stage N ≤ stage (D - 1) := by
  change Submodule.span ℝ
    (Set.range (fun a : Fin N => ZetaTwoOptimizerStage.squarefreeAtom a.val)) ≤
      ZetaTwoOptimizerStage.stage (D - 1)
  apply Submodule.span_le.mpr
  rintro f ⟨a, rfl⟩
  change ZetaTwoOptimizerStage.squarefreeAtom a.val ∈
    ZetaTwoOptimizerStage.stage (D - 1)
  by_cases ha : Squarefree (a.val + 2)
  · have haD := hcut a ha
    rw [ZetaTwoOptimizerStage.squarefreeAtom, if_pos ha]
    change qResidue (a.val + 2) ∈ walkSpan ZetaTwoOptimizerStage.squarefreeAtom id (D - 1)
    apply Submodule.subset_span
    refine ⟨(⟨a.val, by omega⟩ : Fin (D - 1)), ?_⟩
    simp [ZetaTwoOptimizerStage.squarefreeAtom, ha, id_eq]
  · rw [ZetaTwoOptimizerStage.squarefreeAtom, if_neg ha]
    exact (stage (D - 1)).zero_mem

end RiemannResearch.RH.QSquarefreeHeadBoundary
