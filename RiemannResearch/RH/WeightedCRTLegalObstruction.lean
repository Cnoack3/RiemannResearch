/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.RH.CRTSquarefreeBoundedTail
import RiemannResearch.RH.QWeightedResidues
import RiemannResearch.RH.QWeightedResidueMaps
import RiemannResearch.RH.SquarefreeWeightedPrimitives
import RiemannResearch.Analysis.FiniteWeightedPushforward
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
/-!
# Weighted residue averaging does not preserve legal primitives

Source: user-provided Cesàro weighted-CRT manuscript, 1 November 2026,
"A six-period counterexample". The source supplies the statement and
explicit input 4 r₂ - 3 r₃. This proof uses the actual positive arithmetic
residue weights. No numerical approximation or independence premise is used.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.WeightedCRTLegalObstruction
open ArithmeticCumulative Pareto QWeightedResidues QWeightedResidueMaps
open SquarefreeWeightedPrimitives
open RiemannResearch.Analysis.FiniteWeightedPushforward
def sixTrial (n : ℕ) : ℝ := 4 * residueFraction 2 n - 3 * residueFraction 3 n
def sixPrimitive : Fin 6 → ℝ := ![0, 1, -1, 1, 0, 0]
theorem sixPrimitive_legal : IsLegalPrimitive 6 sixPrimitive := by
  have h2 : residueFraction 2 ∈ divisorResidueSpan 6 :=
    Submodule.subset_span ⟨2, by decide, by decide, rfl⟩
  have h3 : residueFraction 3 ∈ divisorResidueSpan 6 :=
    Submodule.subset_span ⟨3, by decide, by decide, rfl⟩
  refine ⟨sixTrial, ?_, ?_, ?_⟩
  · change (4 : ℝ) • residueFraction 2 - (3 : ℝ) • residueFraction 3 ∈ _
    exact (divisorResidueSpan 6).sub_mem
      ((divisorResidueSpan 6).smul_mem 4 h2)
      ((divisorResidueSpan 6).smul_mem 3 h3)
  · norm_num [sixTrial, cumulative, residueFraction, Finset.sum_range_succ]
  · intro a
    fin_cases a <;>
      norm_num [sixPrimitive, sixTrial, cumulative, residueFraction, Finset.sum_range_succ]
theorem average_even_exact :
    residueAverage 2 6 (by decide) sixPrimitive ⟨0, by decide⟩ =
      -residueWeight 6 ⟨2, by decide⟩ / residueWeight 2 ⟨0, by decide⟩ := by
  change pushWeight (fun b : Fin 6 => residueWeight 6 b * sixPrimitive b)
      (reduction 2 6 (by decide)) ⟨0, by decide⟩ /
      pushWeight (residueWeight 6) (reduction 2 6 (by decide)) ⟨0, by decide⟩ = _
  rw [pushed_residueWeight 2 6 (by decide) (by decide) (by decide)]
  congr 1
  norm_num [pushWeight, tsum_fintype, Fin.sum_univ_succ, reduction, sixPrimitive]
  congr 1
theorem average_even_negative :
    residueAverage 2 6 (by decide) sixPrimitive ⟨0, by decide⟩ < 0 := by
  rw [average_even_exact]
  exact div_neg_of_neg_of_pos
    (neg_lt_zero.mpr (residueWeight_pos 6 (by decide) ⟨2, by decide⟩))
    (residueWeight_pos 2 (by decide) ⟨0, by decide⟩)
theorem weighted_adjoint_not_legal :
    IsLegalPrimitive 6 sixPrimitive ∧
      ¬ IsLegalPrimitive 2 (residueAverage 2 6 (by decide) sixPrimitive) := by
  refine ⟨sixPrimitive_legal, ?_⟩
  intro h
  have hz := legalPrimitive_zero 2 (by decide)
    (residueAverage 2 6 (by decide) sixPrimitive) h
  have hn := average_even_negative
  linarith
end RiemannResearch.RH.WeightedCRTLegalObstruction
