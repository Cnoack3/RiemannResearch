/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QLargeConductorCapacity
import RiemannResearch.RH.QSquarefreeExactHeadAverages
import RiemannResearch.RH.QMobiusExactHead
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.QCovarianceInvertibility
import RiemannResearch.NumberTheory.MobiusReciprocalSum
import RiemannResearch.Analysis.FiniteGramScalarConstraint
import RiemannResearch.Analysis.FiniteHilbertGram
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The actual squarefree Möbius seed and its constrained Q minimum

Source: user-provided `Q_LCM_Periods_RH_Criterion_and_Research_Agenda_2026-10-16.md`,
Sections 7--8, for the seed, scalar constraint, and optimizer formula.
This assembles the actual optimizer with the existing bounded exact-head
consumer of Mathlib RH. The uniform bound on the complete constrained error
is an explicit open arithmetic provider, not a proved estimate. A stage can
contain any finite nonempty distinct squarefree family above the head, in
particular all free squarefree divisors in the manuscript's LCM stage.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.QSquarefreeConstrainedMinimum

open ZetaTwoHilbert ZetaTwoProbability QCovarianceInvertibility QLargeConductorCapacity
open QSquarefreeExactHeadAverages
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteGramCapacity

/-- The fixed low-conductor seed, with its original signed Möbius coefficients. -/
def mobiusSeed (H : ℕ) : QHilbert :=
  -(∑ d ∈ Finset.Icc 1 H, (ArithmeticFunction.moebius d : ℝ) • qResidue d)

private theorem legal_atom (d : ℕ) (hd : 2 ≤ d) (hsf : Squarefree d) :
    qResidue d ∈ qSquarefreeCRTSpan :=
  Submodule.subset_span ⟨⟨d, hd, hsf⟩, rfl⟩

theorem mobiusSeed_mem_squarefreeSpan (H : ℕ) : mobiusSeed H ∈ qSquarefreeCRTSpan := by
  classical
  apply qSquarefreeCRTSpan.neg_mem
  apply qSquarefreeCRTSpan.sum_mem
  intro d hd
  by_cases hsf : Squarefree d
  · by_cases hd2 : 2 ≤ d
    · exact qSquarefreeCRTSpan.smul_mem _ (legal_atom d hd2 hsf)
    · have hd1 : d = 1 := by have := (Finset.mem_Icc.mp hd).1; omega
      rw [hd1, qResidue_one, smul_zero]
      exact qSquarefreeCRTSpan.zero_mem
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
    simp only [Int.cast_zero, zero_smul]
    exact qSquarefreeCRTSpan.zero_mem

/-- Exact physical head of the fixed seed; the free atoms must add n*S_H. -/
theorem mobiusSeed_head (H n : ℕ) (hn : 0 < n) (hnH : n ≤ H) :
    qSequence (mobiusSeed H) n = 1 - (n : ℝ) * Pareto.mobiusReciprocalSum H := by
  have he := QMobiusExactHead.exactHead_exact H n hn hnH
  change qSequenceLinear (mobiusSeed H +
    (((H + 1 : ℕ) : ℝ) * Pareto.mobiusReciprocalSum H) • qResidue (H + 1)) n = 1 at he
  rw [map_add, map_smul] at he
  change qSequence (mobiusSeed H) n +
    (((H + 1 : ℕ) : ℝ) * Pareto.mobiusReciprocalSum H) *
      qSequence (qResidue (H + 1)) n = 1 at he
  rw [qSequence_qResidue] at he
  have hnlt : n < H + 1 := by omega
  simp only [ArithmeticCumulative.residueFraction, Nat.mod_eq_of_lt hnlt] at he
  have hden : ((H + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hc : (((H + 1 : ℕ) : ℝ) * Pareto.mobiusReciprocalSum H) *
      ((n : ℝ) / ((H + 1 : ℕ) : ℝ)) =
      (n : ℝ) * Pareto.mobiusReciprocalSum H := by field_simp
  rw [hc] at he
  linarith

variable {ι : Type*} [Fintype ι]

/-- Actual optimized legal candidate, including the fixed low-conductor seed. -/
def optimizer (H : ℕ) (d : ι → ℕ)
    (hv : LinearIndependent ℝ (fun i => qResidue (d i))) : QHilbert :=
  mobiusSeed H + Fintype.linearCombination ℝ (fun i => qResidue (d i))
    (scalarCoefficients hv (normalizationSource d) (qOne - mobiusSeed H)
      (Pareto.mobiusReciprocalSum H))

def minimumError (H : ℕ) (d : ι → ℕ)
    (hv : LinearIndependent ℝ (fun i => qResidue (d i))) : ℝ :=
  ‖qOne - optimizer H d hv‖ ^ 2

theorem optimizer_mem_squarefreeSpan (H : ℕ) (d : ι → ℕ)
    (hv : LinearIndependent ℝ (fun i => qResidue (d i)))
    (hd2 : ∀ i, 2 ≤ d i) (hsf : ∀ i, Squarefree (d i)) :
    optimizer H d hv ∈ qSquarefreeCRTSpan := by
  apply qSquarefreeCRTSpan.add_mem (mobiusSeed_mem_squarefreeSpan H)
  rw [Fintype.linearCombination_apply]
  exact qSquarefreeCRTSpan.sum_mem (fun i _ =>
    qSquarefreeCRTSpan.smul_mem _ (legal_atom (d i) (hd2 i) (hsf i)))

theorem optimizer_head [Nonempty ι] (H : ℕ) (d : ι → ℕ)
    (hv : LinearIndependent ℝ (fun i => qResidue (d i)))
    (hd0 : ∀ i, 0 < d i) (hd : ∀ i, H < d i)
    (n : ℕ) (hn : 0 < n) (hnH : n ≤ H) : qSequence (optimizer H d hv) n = 1 := by
  have hb := normalizationSource_ne_zero d hd0
  change qSequenceLinear (mobiusSeed H + _) n = 1
  rw [map_add]
  change qSequence (mobiusSeed H) n + qSequence
    (Fintype.linearCombination ℝ (fun i => qResidue (d i))
      (scalarCoefficients hv (normalizationSource d) (qOne - mobiusSeed H)
        (Pareto.mobiusReciprocalSum H))) n = 1
  rw [mobiusSeed_head H n hn hnH, synthesis_head d H hd _ n hnH,
    scalarCoefficients_source hv (normalizationSource d) hb]
  ring

/-- Literal formula (8.1), specialized to the actual Q seed and atoms. -/
theorem minimumError_formula [Nonempty ι] (H : ℕ) (d : ι → ℕ)
    (hv : LinearIndependent ℝ (fun i => qResidue (d i))) (hd0 : ∀ i, 0 < d i) :
    minimumError H d hv = ‖qOne - mobiusSeed H‖ ^ 2 -
      ∑ i, inverseCoeff hv (qOne - mobiusSeed H) i *
        cross (fun i => qResidue (d i)) (qOne - mobiusSeed H) i +
      scalarMismatch hv (normalizationSource d) (qOne - mobiusSeed H)
        (Pareto.mobiusReciprocalSum H) ^ 2 / capacity hv (normalizationSource d) := by
  unfold minimumError optimizer
  rw [sub_add_eq_sub_sub]
  exact scalarCoefficients_energy hv (normalizationSource d)
    (normalizationSource_ne_zero d hd0) _ _

/-- All feasible free coefficients retain an exact nonnegative excess energy. -/
theorem minimumError_completion [Nonempty ι] (H : ℕ) (d : ι → ℕ)
    (hv : LinearIndependent ℝ (fun i => qResidue (d i))) (hd0 : ∀ i, 0 < d i)
    (c : ι → ℝ) (hc : (∑ i, c i * normalizationSource d i) =
      Pareto.mobiusReciprocalSum H) :
    ‖qOne - (mobiusSeed H + Fintype.linearCombination ℝ (fun i => qResidue (d i)) c)‖ ^ 2 =
      minimumError H d hv +
        ‖Fintype.linearCombination ℝ (fun i => qResidue (d i))
          (c - scalarCoefficients hv (normalizationSource d) (qOne - mobiusSeed H)
            (Pareto.mobiusReciprocalSum H))‖ ^ 2 := by
  unfold minimumError optimizer
  simp only [sub_add_eq_sub_sub]
  exact scalarCoefficients_completion hv (normalizationSource d)
    (normalizationSource_ne_zero d hd0) _ _ c hc

/-- Conditional research reduction with an explicit actual optimizer.
Open provider: the displayed uniform bound on minimumError. -/
theorem riemannHypothesis_of_bounded_minimumError
    {κ : ℕ → Type*} [∀ H, Fintype (κ H)] [∀ H, Nonempty (κ H)]
    (d : ∀ H, κ H → ℕ) (hd2 : ∀ H i, 1 < d H i)
    (hinj : ∀ H, Function.Injective (d H))
    (hsf : ∀ H i, Squarefree (d H i)) (hlarge : ∀ H i, H < d H i)
    (B : ℝ)
    (hbudget : ∀ H, minimumError H (d H)
      (qResidue_linearIndependent (d H) (hd2 H) (hinj H)) ≤ B) : RiemannHypothesis := by
  let F : ℕ → QHilbert := fun H => optimizer H (d H)
    (qResidue_linearIndependent (d H) (hd2 H) (hinj H))
  have hlegal : ∀ H, F H ∈ qSquarefreeCRTSpan := fun H =>
    optimizer_mem_squarefreeSpan H (d H) _ (fun i => hd2 H i) (hsf H)
  have hbound : ∀ H, ‖qOne - F H‖ ^ 2 ≤ B := hbudget
  have hhead : ∀ H n, 0 < n → n ≤ H → qSequence (F H) n = 1 := fun H n hn hnH =>
    optimizer_head H (d H) _ (fun i => lt_trans Nat.zero_lt_one (hd2 H i))
      (hlarge H) n hn hnH
  exact (squarefree_closure_capacity_and_rh_of_bounded_exact_heads
    F hlegal hbound hhead).2.2

end RiemannResearch.RH.QSquarefreeConstrainedMinimum
