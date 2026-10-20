/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QParityProjectionDefect
import RiemannResearch.RH.QResidueConditional
import Mathlib.Tactic.IntervalCases

/-!
# An exact six-period trial and quantitative parity leakage

The legal trial g_2+g_3+g_6 has residual (0,0,0,0,-1,1) on the
positive residues 1,...,6. Its complete-Q error is w_6(5)+1/36.
Termwise comparison with the progression of positive multiples of five
gives w_6(5) <= 1/25, hence error <= 61/900.

Combined with the exact parity projection identity this gives a uniform
comparison between the actual legal error and the optimizer's parity
leakage. No tail truncation, coefficient restriction, or RH assumption occurs.
Source: the user-directed CRT/profinite continuation, 20 October 2026.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSixAtomTrialBound
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative QResidueConditional
open QParityProjectionDefect
open RiemannResearch.Analysis.ProjectionCompression

/-- Spreading a positive progression can only decrease its complete-Q mass. -/
theorem residueWeight_le_inverse_square (L a : ℕ) (ha : 0 < a) (haL : a ≤ L) :
    residuePowerWeight 0 L a ≤ 1 / (a : ℝ) ^ 2 := by
  have hL : 0 < L := lt_of_lt_of_le ha haL
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have haLR : (a : ℝ) ≤ L := by exact_mod_cast haL
  calc
    residuePowerWeight 0 L a ≤ residuePowerWeight 0 a a := by
      apply Summable.tsum_le_tsum ?_ (residuePowerWeight_summable 0 hLR haR)
        (residuePowerWeight_summable 0 haR haR)
      intro j
      change 1 / (zetaTwo * ((a : ℝ) + (j : ℝ) * L) ^ 2) ≤
        1 / (zetaTwo * ((a : ℝ) + (j : ℝ) * a) ^ 2)
      apply one_div_le_one_div_of_le
      · positivity [zetaTwo_pos]
      · have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        have harg := mul_le_mul_of_nonneg_left haLR hj
        have hja : 0 ≤ (j : ℝ) * a := mul_nonneg hj haR.le
        have hjL : 0 ≤ (j : ℝ) * L := mul_nonneg hj hLR.le
        have hsq : ((a : ℝ) + (j : ℝ) * a) ^ 2 ≤
            ((a : ℝ) + (j : ℝ) * L) ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_left hsq zetaTwo_pos.le
    _ = _ := residuePowerWeight_zeroClass a

def sixTrial : QHilbert := qResidue 2 + qResidue 3 + qResidue 6

def sixResidual (n : ℕ) : ℝ :=
  1 - (residueFraction 2 n + residueFraction 3 n + residueFraction 6 n)

theorem sixResidual_period (n : ℕ) : sixResidual (n + 6) = sixResidual n := by
  simp [sixResidual, residueFraction, Nat.add_mod]

theorem sixResidual_abs_le_one (n : ℕ) : |sixResidual n| ≤ 1 := by
  have h2 : n % 2 = (n % 6) % 2 := by omega
  have h3 : n % 3 = (n % 6) % 3 := by omega
  have h6 : n % 6 < 6 := Nat.mod_lt n (by decide)
  interval_cases hn : n % 6 <;> norm_num [sixResidual, residueFraction, h2, h3, hn]

theorem sixTrial_residual_sequence (n : ℕ) :
    qSequence (qOne - sixTrial) (n + 1) = sixResidual (n + 1) := by
  have he : qSequence (qOne - sixTrial) = qSequence qOne -
      (qSequence (qResidue 2) + qSequence (qResidue 3) + qSequence (qResidue 6)) := by
    change qSequenceLinear (qOne - (qResidue 2 + qResidue 3 + qResidue 6)) =
      qSequenceLinear qOne -
        (qSequenceLinear (qResidue 2) + qSequenceLinear (qResidue 3) +
          qSequenceLinear (qResidue 6))
    simp only [map_sub, map_add]
  simp only [qSequence_qOne, qSequence_qResidue] at he
  simpa [qOneSequence, sixResidual] using congrFun he (n + 1)

/-- The six-residue computation retains the entire infinite Q tail. -/
theorem sixTrial_error_exact :
    ‖qOne - sixTrial‖ ^ 2 = residuePowerWeight 0 6 5 + 1 / 36 := by
  have he : ‖qOne - sixTrial‖ ^ 2 =
      inversePowerMean 0 (fun n => (sixResidual n) ^ 2) := by
    rw [← real_inner_self_eq_norm_sq, qInner_eq_inversePowerMean]
    unfold inversePowerMean
    apply tsum_congr
    intro n
    simp only [sixTrial_residual_sequence]
    ring
  have hb : ∀ n, |(sixResidual n) ^ 2| ≤ (1 : ℝ) := by
    intro n
    rw [abs_of_nonneg (sq_nonneg _)]
    have h := abs_le.mp (sixResidual_abs_le_one n)
    nlinarith
  have hp : ∀ n, (sixResidual (n + 6)) ^ 2 = (sixResidual n) ^ 2 := by
    intro n
    rw [sixResidual_period]
  rw [he, periodic_inversePowerMean 0 6 (by decide) _ hb hp]
  norm_num [Fin.sum_univ_succ, sixResidual, residueFraction]
  have hz := residuePowerWeight_zeroClass 6
  norm_num at hz
  rw [hz]

theorem sixTrial_error_le : ‖qOne - sixTrial‖ ^ 2 ≤ (61 / 900 : ℝ) := by
  rw [sixTrial_error_exact]
  have h := residueWeight_le_inverse_square 6 5 (by decide) (by decide)
  norm_num at h
  linarith

variable (V : Submodule ℝ QHilbert) [V.HasOrthogonalProjection]

/-- A universal complete-Q bound once the three legal conductors are present. -/
theorem error_le_sixty_one (h2 : qResidue 2 ∈ V) (h3 : qResidue 3 ∈ V)
    (h6 : qResidue 6 ∈ V) :
    ‖qOne - V.starProjection qOne‖ ^ 2 ≤ (61 / 900 : ℝ) := by
  have ht : sixTrial ∈ V := V.add_mem (V.add_mem h2 h3) h6
  have he : (qOne - sixTrial) - V.starProjection (qOne - sixTrial) =
      qOne - V.starProjection qOne := by
    rw [map_sub, Submodule.starProjection_eq_self_iff.mpr ht]
    abel
  have hn := defect_norm_le V (qOne - sixTrial)
  rw [he] at hn
  exact le_trans ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn) sixTrial_error_le

/-- Parity leakage and legal error are uniformly comparable, with explicit constants. -/
theorem optimizer_parity_leakage_bounds (h2 : qResidue 2 ∈ V)
    (h3 : qResidue 3 ∈ V) (h6 : qResidue 6 ∈ V) :
    (164 / 225 : ℝ) * ‖qOne - V.starProjection qOne‖ ^ 2 ≤
      ‖V.starProjection qOne - paritySpace.starProjection (V.starProjection qOne)‖ ^ 2 ∧
      ‖V.starProjection qOne - paritySpace.starProjection (V.starProjection qOne)‖ ^ 2 ≤
        ‖qOne - V.starProjection qOne‖ ^ 2 := by
  rw [optimizer_parity_leakage_exact V h2]
  have hb := error_le_sixty_one V h2 h3 h6
  have hd : 0 ≤ ‖qOne - V.starProjection qOne‖ ^ 2 := sq_nonneg _
  have hm := mul_nonneg hd (sub_nonneg.mpr hb)
  constructor <;> nlinarith [sq_nonneg (‖qOne - V.starProjection qOne‖ ^ 2)]

private theorem qResidue_three_mem_closure : qResidue 3 ∈ ZetaTwoOptimizerStage.closure := by
  change qResidue 3 ∈ (Submodule.span ℝ
    (Set.range ZetaTwoOptimizerStage.squarefreeAtom)).topologicalClosure
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  refine ⟨1, ?_⟩
  simp [ZetaTwoOptimizerStage.squarefreeAtom, Nat.prime_three.squarefree]

/-- The explicit comparison applies to the actual infinite squarefree optimizer. -/
theorem limiting_optimizer_parity_leakage_bounds :
    (164 / 225 : ℝ) * ‖ZetaTwoOptimizerStage.limitingResidual‖ ^ 2 ≤
      ‖ZetaTwoOptimizerStage.closure.starProjection qOne -
        paritySpace.starProjection (ZetaTwoOptimizerStage.closure.starProjection qOne)‖ ^ 2 ∧
      ‖ZetaTwoOptimizerStage.closure.starProjection qOne -
        paritySpace.starProjection (ZetaTwoOptimizerStage.closure.starProjection qOne)‖ ^ 2 ≤
      ‖ZetaTwoOptimizerStage.limitingResidual‖ ^ 2 :=
  optimizer_parity_leakage_bounds ZetaTwoOptimizerStage.closure
    QParityConditionalTarget.qResidue_two_mem_closure qResidue_three_mem_closure
    QParityConditionalTarget.qResidue_six_mem_closure

end RiemannResearch.RH.QSixAtomTrialBound
