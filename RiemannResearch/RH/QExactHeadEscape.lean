/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.ExactHeadCharges
import Mathlib.Tactic.NormNum
import RiemannResearch.RH.QMobiusExactHead
import RiemannResearch.RH.QDivisorHilbertBasis
import RiemannResearch.RH.NormalizedResidueExactHeadCharges
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Exact heads and escaping Q energy

Source: user-provided CRT/Parseval construction request, 13 October 2026.
The construction and counterexample below distinguish exact cancellation on
every growing finite head from control of the complete Q norm. No RH is assumed.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.QExactHeadEscape
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative

/-- A legal direction invisible on the first N positive coordinates. -/
def nullHead (N : ℕ) : QHilbert :=
  ((N + 1 : ℕ) : ℝ) • qResidue (N + 1) -
    ((N + 2 : ℕ) : ℝ) • qResidue (N + 2)

theorem nullHead_sequence (N n : ℕ) :
    qSequence (nullHead N) n =
      ((N + 1 : ℕ) : ℝ) * residueFraction (N + 1) n -
        ((N + 2 : ℕ) : ℝ) * residueFraction (N + 2) n := by
  change qSequenceLinear (nullHead N) n = _
  simp [nullHead, map_sub, map_smul, qSequenceLinear, qSequence_qResidue]

theorem nullHead_head (N n : ℕ) (hn : n ≤ N) :
    qSequence (nullHead N) n = 0 := by
  rw [nullHead_sequence]
  unfold residueFraction
  rw [Nat.mod_eq_of_lt (by omega : n < N + 1),
    Nat.mod_eq_of_lt (by omega : n < N + 2)]
  have h1 : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have h2 : ((N + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  simp

theorem nullHead_boundary (N : ℕ) :
    qSequence (nullHead N) (N + 1) = -((N + 1 : ℕ) : ℝ) := by
  rw [nullHead_sequence]
  unfold residueFraction
  rw [Nat.mod_self, Nat.mod_eq_of_lt (by omega : N + 1 < N + 2)]
  have h2 : ((N + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  simp

private theorem residue_mem (d : ℕ) (hd : 0 < d) :
    qResidue d ∈ QFullResidueProjection.legalSpan := by
  by_cases h : d = 1
  · simp [h]
  · change qResidue d ∈ Submodule.span ℝ (Set.range (fun i : ℕ => qResidue (i + 2)))
    apply Submodule.subset_span
    refine ⟨d - 2, ?_⟩
    have he : d - 2 + 2 = d := by omega
    change qResidue (d - 2 + 2) = qResidue d
    rw [he]

theorem nullHead_mem (N : ℕ) :
    nullHead N ∈ QFullResidueProjection.legalSpan := by
  exact Submodule.sub_mem _
    (Submodule.smul_mem _ _ (residue_mem _ (by omega)))
    (Submodule.smul_mem _ _ (residue_mem _ (by omega)))

/-- Prescribe the first coordinate beyond an otherwise unchanged exact head. -/
def prescribe (N : ℕ) (T : ℝ) : QHilbert :=
  QMobiusExactHead.exactHead N +
    ((qSequence (QMobiusExactHead.exactHead N) (N + 1) - T) /
      ((N + 1 : ℕ) : ℝ)) • nullHead N

theorem prescribe_sequence (N n : ℕ) (T : ℝ) :
    qSequence (prescribe N T) n =
      qSequence (QMobiusExactHead.exactHead N) n +
      ((qSequence (QMobiusExactHead.exactHead N) (N + 1) - T) /
        ((N + 1 : ℕ) : ℝ)) * qSequence (nullHead N) n := by
  change qSequenceLinear (prescribe N T) n = _
  simp [prescribe, map_add, map_smul, qSequenceLinear]

theorem prescribe_head (N n : ℕ) (T : ℝ) (hn : 0 < n) (hnN : n ≤ N) :
    qSequence (prescribe N T) n = 1 := by
  rw [prescribe_sequence, nullHead_head N n hnN,
    QMobiusExactHead.exactHead_exact N n hn hnN]
  ring

theorem prescribe_boundary (N : ℕ) (T : ℝ) :
    qSequence (prescribe N T) (N + 1) = T := by
  rw [prescribe_sequence, nullHead_boundary]
  have h : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem prescribe_mem (N : ℕ) (T : ℝ) :
    prescribe N T ∈ QFullResidueProjection.legalSpan :=
  Submodule.add_mem _ (QMobiusExactHead.exactHead_mem_legalSpan N)
    (Submodule.smul_mem _ _ (nullHead_mem N))

theorem prescribe_error_lower (N : ℕ) (T : ℝ) :
    positiveQWeight (N + 1) * (1 - T) ^ 2 ≤ ‖qOne - prescribe N T‖ ^ 2 := by
  rw [qNorm_weighted_sq]
  have h := (qSequence_square_summable (qOne - prescribe N T)).le_tsum (N + 1)
    (fun k _ => mul_nonneg (positiveQWeight_nonneg k) (sq_nonneg _))
  have he : qSequence (qOne - prescribe N T) (N + 1) = 1 - T := by
    change qSequenceLinear (qOne - prescribe N T) (N + 1) = 1 - T
    rw [map_sub]
    change qSequence qOne (N + 1) - qSequence (prescribe N T) (N + 1) = 1 - T
    rw [qSequence_qOne, prescribe_boundary]
    simp only [qOneSequence, if_neg (Nat.succ_ne_zero N)]
  simpa only [he] using h

/-- The escaping family has exact growing heads but error at least (N+1)^2. -/
def escaping (N : ℕ) : QHilbert :=
  prescribe N (1 + ((N + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt zetaTwo)

theorem escaping_error_lower (N : ℕ) :
    ((N + 1 : ℕ) : ℝ) ^ 2 ≤ ‖qOne - escaping N‖ ^ 2 := by
  have h := prescribe_error_lower N
    (1 + ((N + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt zetaTwo)
  have hn : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hz : zetaTwo ≠ 0 := ne_of_gt zetaTwo_pos
  have he : positiveQWeight (N + 1) *
      (1 - (1 + ((N + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt zetaTwo)) ^ 2 =
      ((N + 1 : ℕ) : ℝ) ^ 2 := by
    have hs := Real.sq_sqrt zetaTwo_pos.le
    unfold positiveQWeight
    field_simp
    rw [show 1 - (1 + ((N + 1 : ℕ) : ℝ)^2 * Real.sqrt zetaTwo) =
      -(((N + 1 : ℕ) : ℝ)^2 * Real.sqrt zetaTwo) by ring,
      neg_sq, mul_pow, hs]
    ring
  rw [he] at h
  exact h

theorem escaping_pointwise (n : ℕ) (hn : 0 < n) :
    Tendsto (fun N => qSequence (escaping N) n) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with N hN
  exact (prescribe_head N n _ hn hN).symm

theorem escaping_error_not_tendsto_zero :
    ¬ Tendsto (fun N => ‖qOne - escaping N‖ ^ 2) atTop (𝓝 0) := by
  intro h
  have he : ∀ᶠ N : ℕ in atTop, 1 ≤ ‖qOne - escaping N‖ ^ 2 := by
    apply Filter.Eventually.of_forall
    intro N
    have hn : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
    exact (by nlinarith : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ)^2).trans (escaping_error_lower N)
  have : (1 : ℝ) ≤ 0 := ge_of_tendsto h he
  norm_num at this

/-- The usual continuous residue coefficient extractor, for d greater than one. -/
def residueCoefficient (F : QHilbert) (d : ℕ) : ℝ :=
  -Pareto.mobiusDifference d (qSequence F)

theorem residueCoefficient_atom (m d : ℕ) (hm : 1 < m) :
    residueCoefficient (qResidue d) m = if m = d then 1 else 0 := by
  simp only [residueCoefficient, qSequence_qResidue,
    Pareto.mobiusDifference_residueFraction m d hm]
  split_ifs <;> norm_num

theorem prescribe_coefficient (N m : ℕ) (T : ℝ) (hm : 1 < m) (hmN : m ≤ N) :
    residueCoefficient (prescribe N T) m = -(ArithmeticFunction.moebius m : ℝ) := by
  have hhead := fun k hk hkN => prescribe_head N k T hk hkN
  have he := Pareto.exact_head_mobiusDifference
    (qSequence_zero (prescribe N T)) hhead (by omega : 0 < m) hmN
  exact congrArg Neg.neg he

theorem escaping_coefficient_eventually (d : ℕ) (hd : 1 < d) :
    ∀ᶠ N in atTop, residueCoefficient (escaping N) d =
      -(ArithmeticFunction.moebius d : ℝ) := by
  filter_upwards [eventually_ge_atTop d] with N hN
  exact prescribe_coefficient N d _ hd hN

theorem escaping_parseval_lower (N : ℕ) :
    ((N + 1 : ℕ) : ℝ)^2 ≤
      ∑' r : ℕ+, (inner ℝ (qOne - escaping N)
        (QDivisorHilbert.divisorWavelet (r : ℕ)))^2 /
          qJordanTwo (r : ℕ) := by
  rw [QDivisorHilbert.divisorWavelet_parseval_norm]
  exact escaping_error_lower N

end RiemannResearch.RH.QExactHeadEscape
