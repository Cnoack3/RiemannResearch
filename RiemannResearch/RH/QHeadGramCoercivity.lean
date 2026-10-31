/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteGramCoercivity
import RiemannResearch.RH.QSquarefreeTailResponse
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.RH.QAnnihilatorTailEscape
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Coercivity of the complete squarefree head Schur Gram

Source: SquarefreeShortHeadSchurResearch20261030.md, sections 2--3.
The head-vanishing projection is the actual complete-squarefree tailStage.
The finite head is used for coercivity only; the Schur norm and inverse use
the entire Q inner product. This module supplies the transfer machinery;
the divisor-coercivity provider is a separate arithmetic result.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QHeadGramCoercivity
open ZetaTwoHilbert ZetaTwoProbability QFiniteSupportDualCriterion
open QSquarefreeTailResponse QAnnihilatorTailEscape
open RiemannResearch.Analysis.FiniteGramCoercivity
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteGramCapacity

theorem finiteHead_norm_sq_eq_sum (H : ℕ) (f : QHilbert) :
    ‖finiteHead H f‖ ^ 2 = ∑ i ∈ Finset.range H, (f i) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_finiteHead_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [finiteHead_apply_of_lt H f i (Finset.mem_range.mp hi)]
  ring

/-- Exact conversion between physical reciprocal coordinates and the Q head. -/
theorem physical_head_energy (H : ℕ) (f : QHilbert) :
    (∑ n ∈ Finset.range (H + 1), (qSequence f n / (n : ℝ)) ^ 2) =
      zetaTwo * ‖finiteHead H f‖ ^ 2 := by
  rw [Finset.sum_range_succ']
  simp only [qSequence_zero, Nat.cast_zero, zero_div,
    zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero]
  rw [finiteHead_norm_sq_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hiR : ((i + 1 : ℕ): ℝ) ≠ 0 := by positivity
  calc
    (qSequence f (i + 1) / ((i + 1 : ℕ): ℝ)) ^ 2 =
        zetaTwo * (positiveQWeight (i + 1) * (qSequence f (i + 1)) ^ 2) := by
      rw [div_pow, positiveQWeight]
      field_simp [ne_of_gt zetaTwo_pos, hiR]
    _ = _ := by rw [qSequence_weighted_square]

/-- Projecting away every actual head-null legal direction preserves the head. -/
theorem finiteHead_screened (N H : ℕ) (f : QHilbert) :
    finiteHead H (f - (tailStage N H).starProjection f) = finiteHead H f := by
  apply lp.ext
  funext i
  by_cases hi : i < H
  · rw [finiteHead_apply_of_lt H _ i hi, finiteHead_apply_of_lt H f i hi]
    change f i - ((tailStage N H).starProjection f) i = f i
    rw [((tailStage N H).starProjection_apply_mem f).2 i hi, sub_zero]
  · rw [finiteHead_apply_eq_zero H _ i (by omega),
      finiteHead_apply_eq_zero H _ i (by omega)]

variable {ι : Type*} [Fintype ι]

/-- The complete tail square is retained in the Schur energy identity. -/
theorem screened_energy_head_tail_exact (N H : ℕ) (v : ι → QHilbert)
    (c : ι → ℝ) :
    ‖Fintype.linearCombination ℝ (screened (tailStage N H) v) c‖ ^ 2 =
      ‖finiteHead H (Fintype.linearCombination ℝ v c)‖ ^ 2 +
      ‖tail H (Fintype.linearCombination ℝ (screened (tailStage N H) v) c)‖ ^ 2 := by
  have h := finiteHead_norm_sq_split H
    (Fintype.linearCombination ℝ (screened (tailStage N H) v) c)
  have he : finiteHead H (Fintype.linearCombination ℝ (screened (tailStage N H) v) c) =
      finiteHead H (Fintype.linearCombination ℝ v c) := by
    rw [synthesis_screened, finiteHead_screened]
  change ‖Fintype.linearCombination ℝ (screened (tailStage N H) v) c‖ ^ 2 =
    ‖finiteHead H (Fintype.linearCombination ℝ v c)‖ ^ 2 +
      ‖Fintype.linearCombination ℝ (screened (tailStage N H) v) c -
        finiteHead H (Fintype.linearCombination ℝ (screened (tailStage N H) v) c)‖ ^ 2
  rw [← he]
  exact h

theorem screened_head_coercivity (N H : ℕ) (v : ι → QHilbert)
    (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ c : ι → ℝ,
      (∑ i, (c i) ^ 2) ≤ C * ‖finiteHead H (Fintype.linearCombination ℝ v c)‖ ^ 2) :
    ∀ c : ι → ℝ,
      (∑ i, (c i) ^ 2) ≤
        C * ‖Fintype.linearCombination ℝ (screened (tailStage N H) v) c‖ ^ 2 := by
  exact screened_coercive (tailStage N H) (finiteHead H)
    (finiteHead_norm_le H) (finiteHead_screened N H) v C hC hc

theorem screened_head_linearIndependent (N H : ℕ) (v : ι → QHilbert)
    (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ c : ι → ℝ,
      (∑ i, (c i) ^ 2) ≤ C * ‖finiteHead H (Fintype.linearCombination ℝ v c)‖ ^ 2) :
    LinearIndependent ℝ (screened (tailStage N H) v) :=
  linearIndependent_of_coercive _ C (screened_head_coercivity N H v C hC hc)

/-- Literal inverse-Gram quadratic bound, with independence supplied from the
head estimate and the complete actual squarefree projection. -/
theorem screened_head_inverseGram_le [DecidableEq ι]
    (N H : ℕ) (v : ι → QHilbert) (C : ℝ) (hC : 0 < C)
    (hc : ∀ c : ι → ℝ,
      (∑ i, (c i) ^ 2) ≤ C * ‖finiteHead H (Fintype.linearCombination ℝ v c)‖ ^ 2)
    (b : ι → ℝ) :
    dotProduct b ((gramMatrix (screened (tailStage N H) v))⁻¹.mulVec b) ≤
      C * (∑ i, (b i) ^ 2) := by
  exact inverseGram_quadratic_le (screened_head_linearIndependent N H v C hC.le hc)
    C hC (screened_head_coercivity N H v C hC.le hc) b

end RiemannResearch.RH.QHeadGramCoercivity
