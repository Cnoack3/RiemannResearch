/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteGramRankOne
import RiemannResearch.Analysis.FiniteGramScalarConstraint
import RiemannResearch.Analysis.FiniteGramCapacity
import RiemannResearch.Analysis.FiniteHilbertGram
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import RiemannResearch.RH.QTailGram
import RiemannResearch.RH.QSquarefreeConstrainedMinimum
import RiemannResearch.RH.QLargeConductorCapacity
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Tail-only optimizer for the squarefree constrained Q minimum

Source: user-provided rank-one head-removal deduction, 16 October 2026,
and QLCMConstrainedMinimumResearch20261016.md, priority 2. The tail Gram
inverse is justified by periodicity and actual independence. The coefficient
optimizer and complete error agree exactly with the published full-Q problem.
Uniform bounds on these errors remain open.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QTailConstrainedMinimum
open ZetaTwoHilbert ZetaTwoProbability QLargeConductorCapacity QTailGram
open QSquarefreeConstrainedMinimum
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteGramCapacity

variable {ι : Type*} [Fintype ι]

def tailCapacity (H : ℕ) (d : ι → ℕ) (hd2 : ∀ i, 1 < d i)
    (hinj : Function.Injective d) : ℝ :=
  capacity (tailResidue_linearIndependent H d hd2 hinj) (normalizationSource d)

def tailCoefficients (H : ℕ) (d : ι → ℕ) (hd2 : ∀ i, 1 < d i)
    (hinj : Function.Injective d) (f : QHilbert) (s : ℝ) : ι → ℝ :=
  scalarCoefficients (tailResidue_linearIndependent H d hd2 hinj)
    (normalizationSource d) (tailMap H f) s

theorem tailCapacity_pos [Nonempty ι] (H : ℕ) (d : ι → ℕ)
    (hd2 : ∀ i, 1 < d i) (hinj : Function.Injective d) : 0 < tailCapacity H d hd2 hinj :=
  capacity_pos _ _ (normalizationSource_ne_zero d (fun i => lt_trans Nat.zero_lt_one (hd2 i)))

theorem full_capacity_eq_tail (H : ℕ) (d : ι → ℕ)
    (hd2 : ∀ i, 1 < d i) (hinj : Function.Injective d)
    (hv : LinearIndependent ℝ (fun i => qResidue (d i))) (hd : ∀ i, H < d i) :
    capacity hv (normalizationSource d) =
      tailCapacity H d hd2 hinj / (1 + (H : ℝ) / zetaTwo * tailCapacity H d hd2 hinj) :=
  capacity_rank_one hv (tailResidue_linearIndependent H d hd2 hinj)
    (normalizationSource d) ((H : ℝ) / zetaTwo)
    (div_nonneg (Nat.cast_nonneg H) zetaTwo_pos.le) (gram_head_tail H d hd)

/-- Sherman--Morrison for the actual complete and tail matrix inverses, on every source. -/
theorem full_inverse_mulVec_eq_tail [DecidableEq ι] (H : ℕ) (d : ι → ℕ)
    (hd2 : ∀ i, 1 < d i) (hinj : Function.Injective d)
    (hv : LinearIndependent ℝ (fun i => qResidue (d i))) (hd : ∀ i, H < d i)
    (y : ι → ℝ) :
    (gramMatrix (fun i => qResidue (d i)))⁻¹.mulVec y =
      (tailGram H d)⁻¹.mulVec y -
        (((H : ℝ) / zetaTwo) *
          (∑ j, ((tailGram H d)⁻¹.mulVec y) j * normalizationSource d j) /
            (1 + ((H : ℝ) / zetaTwo) * tailCapacity H d hd2 hinj)) •
              (tailGram H d)⁻¹.mulVec (normalizationSource d) := by
  unfold tailGram
  simp_rw [gramMatrix_inverseSource hv,
    gramMatrix_inverseSource (tailResidue_linearIndependent H d hd2 hinj)]
  exact inverseSource_rank_one_apply hv (tailResidue_linearIndependent H d hd2 hinj)
    (normalizationSource d) y ((H : ℝ) / zetaTwo)
    (div_nonneg (Nat.cast_nonneg H) zetaTwo_pos.le) (gram_head_tail H d hd)

/-- Exact reciprocal capacity, with the compulsory head cost removed. -/
theorem inverse_full_capacity_eq_tail [Nonempty ι] (H : ℕ) (d : ι → ℕ)
    (hd2 : ∀ i, 1 < d i) (hinj : Function.Injective d)
    (hv : LinearIndependent ℝ (fun i => qResidue (d i))) (hd : ∀ i, H < d i) :
    1 / capacity hv (normalizationSource d) =
      (H : ℝ) / zetaTwo + 1 / tailCapacity H d hd2 hinj :=
  inverse_capacity_rank_one hv (tailResidue_linearIndependent H d hd2 hinj)
    (normalizationSource d)
    (normalizationSource_ne_zero d (fun i => lt_trans Nat.zero_lt_one (hd2 i)))
    ((H : ℝ) / zetaTwo) (div_nonneg (Nat.cast_nonneg H) zetaTwo_pos.le) (gram_head_tail H d hd)

theorem tailCoefficients_source [Nonempty ι] (H : ℕ) (d : ι → ℕ)
    (hd2 : ∀ i, 1 < d i) (hinj : Function.Injective d) (f : QHilbert) (s : ℝ) :
    (∑ i, tailCoefficients H d hd2 hinj f s i * normalizationSource d i) = s :=
  scalarCoefficients_source _ _ (normalizationSource_ne_zero d
    (fun i => lt_trans Nat.zero_lt_one (hd2 i))) _ _

/-- Literal equality of coefficients, stronger than equality of minimum values. -/
theorem tailCoefficients_eq_full [Nonempty ι] (H : ℕ) (d : ι → ℕ)
    (hd2 : ∀ i, 1 < d i) (hinj : Function.Injective d)
    (hv : LinearIndependent ℝ (fun i => qResidue (d i))) (hd : ∀ i, H < d i)
    (f : QHilbert) (s : ℝ)
    (hf : ∀ n, 0 < n → n ≤ H → qSequence f n = (n : ℝ) * s) :
    tailCoefficients H d hd2 hinj f s = scalarCoefficients hv (normalizationSource d) f s :=
  (scalarCoefficients_rank_one hv (tailResidue_linearIndependent H d hd2 hinj)
    (normalizationSource d)
    (normalizationSource_ne_zero d (fun i => lt_trans Nat.zero_lt_one (hd2 i)))
    ((H : ℝ) / zetaTwo) (div_nonneg (Nat.cast_nonneg H) zetaTwo_pos.le) (gram_head_tail H d hd)
    f (tailMap H f) s (cross_head_tail H d hd f s hf)).symm

theorem mismatch_full_eq_tail (H : ℕ) (d : ι → ℕ)
    (hd2 : ∀ i, 1 < d i) (hinj : Function.Injective d)
    (hv : LinearIndependent ℝ (fun i => qResidue (d i))) (hd : ∀ i, H < d i)
    (f : QHilbert) (s : ℝ)
    (hf : ∀ n, 0 < n → n ≤ H → qSequence f n = (n : ℝ) * s) :
    scalarMismatch hv (normalizationSource d) f s =
      scalarMismatch (tailResidue_linearIndependent H d hd2 hinj)
        (normalizationSource d) (tailMap H f) s /
          (1 + (H : ℝ) / zetaTwo * tailCapacity H d hd2 hinj) :=
  scalarMismatch_rank_one hv (tailResidue_linearIndependent H d hd2 hinj)
    (normalizationSource d) ((H : ℝ) / zetaTwo) (div_nonneg (Nat.cast_nonneg H) zetaTwo_pos.le)
    (gram_head_tail H d hd) f (tailMap H f) s (cross_head_tail H d hd f s hf)

theorem unconstrained_error_eq_tail [Nonempty ι] (H : ℕ) (d : ι → ℕ)
    (hd2 : ∀ i, 1 < d i) (hinj : Function.Injective d)
    (hv : LinearIndependent ℝ (fun i => qResidue (d i))) (hd : ∀ i, H < d i)
    (f : QHilbert) (s : ℝ)
    (hf : ∀ n, 0 < n → n ≤ H → qSequence f n = (n : ℝ) * s) :
    ‖f - Fintype.linearCombination ℝ (fun i => qResidue (d i)) (inverseCoeff hv f)‖ ^ 2 =
      ‖tailMap H f - Fintype.linearCombination ℝ (tailResidue H d)
        (inverseCoeff (tailResidue_linearIndependent H d hd2 hinj) (tailMap H f))‖ ^ 2 +
          ((H : ℝ) / zetaTwo) *
            scalarMismatch (tailResidue_linearIndependent H d hd2 hinj)
              (normalizationSource d) (tailMap H f) s ^ 2 /
                (1 + ((H : ℝ) / zetaTwo) * tailCapacity H d hd2 hinj) := by
  apply residual_rank_one_value hv (tailResidue_linearIndependent H d hd2 hinj)
    (normalizationSource d)
    (normalizationSource_ne_zero d (fun i => lt_trans Nat.zero_lt_one (hd2 i)))
    ((H : ℝ) / zetaTwo) (div_nonneg (Nat.cast_nonneg H) zetaTwo_pos.le)
    (gram_head_tail H d hd) f (tailMap H f) s (cross_head_tail H d hd f s hf)
  intro c
  rw [residual_head_tail H d hd f s hf c]
  ring

theorem normalizationPenalty_eq_tail [Nonempty ι] (H : ℕ) (d : ι → ℕ)
    (hd2 : ∀ i, 1 < d i) (hinj : Function.Injective d)
    (hv : LinearIndependent ℝ (fun i => qResidue (d i))) (hd : ∀ i, H < d i)
    (f : QHilbert) (s : ℝ)
    (hf : ∀ n, 0 < n → n ≤ H → qSequence f n = (n : ℝ) * s) :
    scalarMismatch hv (normalizationSource d) f s ^ 2 / capacity hv (normalizationSource d) =
      scalarMismatch (tailResidue_linearIndependent H d hd2 hinj)
        (normalizationSource d) (tailMap H f) s ^ 2 /
          (tailCapacity H d hd2 hinj *
            (1 + ((H : ℝ) / zetaTwo) * tailCapacity H d hd2 hinj)) :=
  scalarPenalty_rank_one hv (tailResidue_linearIndependent H d hd2 hinj)
    (normalizationSource d)
    (normalizationSource_ne_zero d (fun i => lt_trans Nat.zero_lt_one (hd2 i)))
    ((H : ℝ) / zetaTwo) (div_nonneg (Nat.cast_nonneg H) zetaTwo_pos.le)
    (gram_head_tail H d hd) f (tailMap H f) s (cross_head_tail H d hd f s hf)

theorem feasible_energy_eq_tail (H : ℕ) (d : ι → ℕ) (hd : ∀ i, H < d i)
    (f : QHilbert) (s : ℝ)
    (hf : ∀ n, 0 < n → n ≤ H → qSequence f n = (n : ℝ) * s)
    (c : ι → ℝ) (hc : (∑ i, c i * normalizationSource d i) = s) :
    ‖f - Fintype.linearCombination ℝ (fun i => qResidue (d i)) c‖ ^ 2 =
      ‖tailMap H f - Fintype.linearCombination ℝ (tailResidue H d) c‖ ^ 2 := by
  rw [residual_head_tail H d hd f s hf c, hc]
  simp

theorem tailCoefficients_energy [Nonempty ι] (H : ℕ) (d : ι → ℕ)
    (hd2 : ∀ i, 1 < d i) (hinj : Function.Injective d) (hd : ∀ i, H < d i)
    (f : QHilbert) (s : ℝ)
    (hf : ∀ n, 0 < n → n ≤ H → qSequence f n = (n : ℝ) * s) :
    ‖f - Fintype.linearCombination ℝ (fun i => qResidue (d i))
      (tailCoefficients H d hd2 hinj f s)‖ ^ 2 =
      ‖tailMap H f‖ ^ 2 -
        ∑ i, inverseCoeff (tailResidue_linearIndependent H d hd2 hinj) (tailMap H f) i *
          cross (tailResidue H d) (tailMap H f) i +
        scalarMismatch (tailResidue_linearIndependent H d hd2 hinj)
          (normalizationSource d) (tailMap H f) s ^ 2 / tailCapacity H d hd2 hinj := by
  rw [feasible_energy_eq_tail H d hd f s hf _
    (tailCoefficients_source H d hd2 hinj f s)]
  exact scalarCoefficients_energy _ _ (normalizationSource_ne_zero d
    (fun i => lt_trans Nat.zero_lt_one (hd2 i))) _ _

theorem seedResidual_head (H : ℕ) (n : ℕ) (hn : 0 < n) (hnH : n ≤ H) :
    qSequence (qOne - mobiusSeed H) n = (n : ℝ) * Pareto.mobiusReciprocalSum H := by
  change qSequenceLinear (qOne - mobiusSeed H) n = _
  rw [map_sub]
  change qSequence qOne n - qSequence (mobiusSeed H) n = _
  rw [qSequence_qOne, mobiusSeed_head H n hn hnH]
  simp only [qOneSequence, if_neg (ne_of_gt hn)]
  ring

/-- The tail formula constructs the already formalized complete-Q optimizer. -/
def tailOptimizer (H : ℕ) (d : ι → ℕ) (hd2 : ∀ i, 1 < d i)
    (hinj : Function.Injective d) : QHilbert :=
  mobiusSeed H + Fintype.linearCombination ℝ (fun i => qResidue (d i))
    (tailCoefficients H d hd2 hinj (qOne - mobiusSeed H) (Pareto.mobiusReciprocalSum H))

theorem tailOptimizer_eq_full [Nonempty ι] (H : ℕ) (d : ι → ℕ)
    (hd2 : ∀ i, 1 < d i) (hinj : Function.Injective d)
    (hv : LinearIndependent ℝ (fun i => qResidue (d i))) (hd : ∀ i, H < d i) :
    tailOptimizer H d hd2 hinj = optimizer H d hv := by
  unfold tailOptimizer optimizer
  rw [tailCoefficients_eq_full H d hd2 hinj hv hd _ _ (seedResidual_head H)]

/-- Actual complete minimum expressed using only complete-tail Gram data. -/
theorem minimumError_tail_formula [Nonempty ι] (H : ℕ) (d : ι → ℕ)
    (hd2 : ∀ i, 1 < d i) (hinj : Function.Injective d)
    (hv : LinearIndependent ℝ (fun i => qResidue (d i))) (hd : ∀ i, H < d i) :
    minimumError H d hv =
      ‖tailMap H (qOne - mobiusSeed H)‖ ^ 2 -
        ∑ i, inverseCoeff (tailResidue_linearIndependent H d hd2 hinj)
          (tailMap H (qOne - mobiusSeed H)) i *
            cross (tailResidue H d) (tailMap H (qOne - mobiusSeed H)) i +
        scalarMismatch (tailResidue_linearIndependent H d hd2 hinj)
          (normalizationSource d) (tailMap H (qOne - mobiusSeed H))
            (Pareto.mobiusReciprocalSum H) ^ 2 / tailCapacity H d hd2 hinj := by
  unfold minimumError
  rw [← tailOptimizer_eq_full H d hd2 hinj hv hd]
  unfold tailOptimizer
  rw [sub_add_eq_sub_sub]
  exact tailCoefficients_energy H d hd2 hinj hd _ _ (seedResidual_head H)

/-- Exact completion on the complete tail, including the full signed remainder. -/
theorem minimumError_tail_completion [Nonempty ι] (H : ℕ) (d : ι → ℕ)
    (hd2 : ∀ i, 1 < d i) (hinj : Function.Injective d)
    (hv : LinearIndependent ℝ (fun i => qResidue (d i))) (hd : ∀ i, H < d i)
    (c : ι → ℝ) (hc : (∑ i, c i * normalizationSource d i) = Pareto.mobiusReciprocalSum H) :
    ‖tailMap H (qOne - mobiusSeed H) -
      Fintype.linearCombination ℝ (tailResidue H d) c‖ ^ 2 =
        minimumError H d hv +
          ‖Fintype.linearCombination ℝ (tailResidue H d)
            (c - tailCoefficients H d hd2 hinj (qOne - mobiusSeed H)
              (Pareto.mobiusReciprocalSum H))‖ ^ 2 := by
  rw [scalarCoefficients_completion (tailResidue_linearIndependent H d hd2 hinj)
    (normalizationSource d) (normalizationSource_ne_zero d
      (fun i => lt_trans Nat.zero_lt_one (hd2 i))) _ _ c hc]
  congr 1
  rw [minimumError_tail_formula H d hd2 hinj hv hd]
  exact scalarCoefficients_energy _ _ (normalizationSource_ne_zero d
    (fun i => lt_trans Nat.zero_lt_one (hd2 i))) _ _

end RiemannResearch.RH.QTailConstrainedMinimum
