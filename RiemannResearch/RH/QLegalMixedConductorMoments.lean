/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QLegalMixedConductor
import RiemannResearch.RH.ZetaTwoOptimizerStage

/-!
# Actual forcing moments and finite squarefree legality

Source: LegalSubspaceProjectionObstruction.md, supplied by the user.
The positive forcing lower bound retains the complete Q inner product and
uses its physical n=2 term. Prime conductor spaces consist of finite legal
squarefree combinations and contain the parity atom.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QLegalMixedConductor
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative
open QDivisorLegality QDivisibilityDensity QShiftedReciprocal ZetaTwoOptimizerStage
open RiemannResearch.Analysis.OrthogonalPairCorrection

theorem qResidue_sequence_nonneg (d n : ℕ) : 0 ≤ qSequence (qResidue d) n := by
  rw [qSequence_qResidue]; unfold residueFraction; positivity

theorem evenTarget_sequence_nonneg (n : ℕ) : 0 ≤ qSequence evenTarget n := by
  rw [qSequence_qDivisor]; unfold positiveDivisor; split_ifs <;> norm_num

theorem B_evenTarget_sequence_nonneg (n : ℕ) : 0 ≤ qSequence (B evenTarget) n := by
  rw [qSequence_B]; exact div_nonneg (evenTarget_sequence_nonneg n) (by positivity)

theorem parityAtom_inner_B_evenTarget : inner ℝ parityAtom (B evenTarget) = 0 := by
  rw [qInner_weighted]
  have hz (n : ℕ) : positiveQWeight n * qSequence parityAtom n *
      qSequence (B evenTarget) n = 0 := by
    rw [qSequence_B, qSequence_qResidue, qSequence_qDivisor]
    by_cases hn : n = 0
    · simp [hn, positiveDivisor]
    by_cases hd : 2 ∣ n
    · simp [residueFraction, Nat.mod_eq_zero_of_dvd hd]
    · simp [positiveDivisor, hn, hd]
  simp only [hz, tsum_zero]

theorem qResidue_inner_B_evenTarget_nonneg (d : ℕ) :
    0 ≤ inner ℝ (qResidue d) (B evenTarget) := by
  rw [qInner_weighted]
  exact tsum_nonneg (fun n => mul_nonneg
    (mul_nonneg (positiveQWeight_nonneg n) (qResidue_sequence_nonneg d n))
    (B_evenTarget_sequence_nonneg n))

/-- One actual physical coordinate gives a positive lower bound on forcing. -/
theorem conductor_three_source_lower :
    1 / (18 * zetaTwo) ≤ inner ℝ (qResidue 3) (B evenTarget) := by
  have h := (qSequence_product_summable (qResidue 3) (B evenTarget)).le_tsum 2
    (fun n _ => mul_nonneg
      (mul_nonneg (positiveQWeight_nonneg n) (qResidue_sequence_nonneg 3 n))
      (B_evenTarget_sequence_nonneg n))
  rw [← qInner_weighted] at h
  have he : positiveQWeight 2 * qSequence (qResidue 3) 2 *
      qSequence (B evenTarget) 2 = 1 / (18 * zetaTwo) := by
    rw [qSequence_B, qSequence_qResidue, qSequence_qDivisor]
    norm_num [residueFraction, positiveDivisor, positiveQWeight]
    ring
  rwa [he] at h

theorem sourceMoment_eq (d : ℕ) :
    sourceMoment d = inner ℝ (qResidue 3) (B evenTarget) +
      10 * Real.sqrt (d : ℝ) * inner ℝ (qResidue d) (B evenTarget) := by
  unfold sourceMoment orthogonalVector mixedVector highPart
  rw [inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    parityAtom_inner_B_evenTarget, mul_zero, sub_zero]

theorem sourceMoment_lower (d : ℕ) : 1 / (18 * zetaTwo) ≤ sourceMoment d := by
  rw [sourceMoment_eq]
  exact le_add_of_le_of_nonneg conductor_three_source_lower
    (mul_nonneg (by positivity) (qResidue_inner_B_evenTarget_nonneg d))

theorem targetMoment_eq (d : ℕ) :
    targetMoment d = inner ℝ evenTarget (qResidue 3) +
      10 * Real.sqrt (d : ℝ) * inner ℝ evenTarget (qResidue d) := by
  unfold targetMoment orthogonalVector mixedVector highPart
  rw [inner_sub_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    evenTarget_inner_parityAtom, mul_zero, sub_zero]

theorem targetMoment_nonneg (d : ℕ) : 0 ≤ targetMoment d := by
  rw [targetMoment_eq]
  have hp (k : ℕ) : 0 ≤ inner ℝ evenTarget (qResidue k) := by
    rw [qInner_weighted]
    exact tsum_nonneg (fun n => mul_nonneg
      (mul_nonneg (positiveQWeight_nonneg n) (evenTarget_sequence_nonneg n))
      (qResidue_sequence_nonneg k n))
  exact add_nonneg (hp 3) (mul_nonneg (by positivity) (hp d))

/-- Every squarefree residue with conductor at least two occurs literally
in the masked legal dictionary. -/
theorem squarefree_residue_mem_span {d : ℕ} (hd : 2 ≤ d) (hs : Squarefree d) :
    qResidue d ∈ Submodule.span ℝ (Set.range squarefreeAtom) := by
  apply Submodule.subset_span
  refine ⟨d - 2, ?_⟩
  have he : d - 2 + 2 = d := Nat.sub_add_cancel hd
  simp only [squarefreeAtom, he, if_pos hs]

/-- The constructed spaces consist of finite legal squarefree combinations. -/
theorem mixedSpace_le_legalSpan {d : ℕ} (hd : Nat.Prime d) :
    mixedSpace d ≤ Submodule.span ℝ (Set.range squarefreeAtom) := by
  rw [mixedSpace_eq_span]
  apply Submodule.span_le.mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact squarefree_residue_mem_span (by norm_num) Nat.prime_two.squarefree
  · exact Submodule.add_mem _
      (squarefree_residue_mem_span (by norm_num) Nat.prime_three.squarefree)
      (Submodule.smul_mem _ _ (squarefree_residue_mem_span hd.two_le hd.squarefree))

theorem parityAtom_mem_mixedSpace (d : ℕ) : parityAtom ∈ mixedSpace d :=
  left_mem_pairSpace _ _

theorem actualResidual_orthogonal (d : ℕ) : actualResidual d ∈ (mixedSpace d)ᗮ :=
  Submodule.sub_starProjection_mem_orthogonal qOne

end RiemannResearch.RH.QLegalMixedConductor
