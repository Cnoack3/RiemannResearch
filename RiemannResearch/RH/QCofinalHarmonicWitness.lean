/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QSquarefreeDisplacementSignedTails
import RiemannResearch.RH.QSquarefreeResidualTail
import RiemannResearch.RH.QSquarefreeDisplacementRigidity
import RiemannResearch.RH.QSignedTailRigidity
import RiemannResearch.RH.QShiftedReciprocal

/-!
# Harmonic prefixes of the actual displacement and its faithful witness

The positive part of either signed displacement transfers to the opposite signed
charge of the witness with a uniform error. The normalization by ζ(2) comes
from the physical Q weights. The legal exact heads and prime probes give the
two exact signed series needed to bound the witness mean.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.QSquarefreeDisplacementRigidity
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage
open QSignedTailRigidity QShiftedReciprocal QAnnihilatorTailEscape

/-- One signed physical harmonic prefix, including its endpoint. -/
def harmonicSide (ε : ℝ) (X : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (X + 1), max (ε * qSequence displacement n) 0 / (n : ℝ)

/-- The first absolute moment of the reciprocal-smoothed source. -/
def smoothingMoment : ℝ :=
  ∑' n : ℕ, |signedCoefficient (B pResidual) n| * (n : ℝ)

theorem smoothingMoment_nonneg : 0 ≤ smoothingMoment :=
  tsum_nonneg (fun n => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg n))

/-- Exact conversion of the normalized charge prefix to the physical harmonic sum. -/
theorem displacement_charge_prefix_eq (ε : ℝ) (X : ℕ) :
    (∑ n ∈ Finset.range (X + 1), max (ε * signedCoefficient displacement n) 0 * (n : ℝ)) =
      harmonicSide ε X / zetaTwo := by
  rw [harmonicSide, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n _
  have hpos := positiveQWeight_nonneg n
  have hpart : max (ε * signedCoefficient displacement n) 0 =
      positiveQWeight n * max (ε * qSequence displacement n) 0 := by
    rw [signedCoefficient, mul_left_comm ε (positiveQWeight n)]
    rcases le_total 0 (ε * qSequence displacement n) with h | h
    · rw [max_eq_left h, max_eq_left (mul_nonneg hpos h)]
    · rw [max_eq_right h, max_eq_right (mul_nonpos_of_nonneg_of_nonpos hpos h), mul_zero]
  rw [hpart]
  by_cases h : n = 0
  · simp [h]
  · have hn : (n : ℝ) ≠ 0 := by exact_mod_cast h
    unfold positiveQWeight
    field_simp [hn, zetaTwo_pos.ne']

/-- The sign may be selected separately at every cutoff. -/
theorem witness_prefix_le (ε : ℝ) (hε : |ε| = 1) (X : ℕ) :
    (∑ n ∈ Finset.range (X + 1), max ((-ε) * signedCoefficient witness n) 0 * (n : ℝ)) ≤ smoothingMoment + harmonicSide ε X / zetaTwo := by
  have hfirst : Summable (fun n : ℕ => |signedCoefficient (B pResidual) n| * (n : ℝ)) := by
    apply (signedCoefficient_B_firstMoment pResidual).abs.congr
    intro n
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n), mul_comm]
  have hpoint (n : ℕ) : max ((-ε) * signedCoefficient witness n) 0 ≤
      |signedCoefficient (B pResidual) n| + max (ε * signedCoefficient displacement n) 0 := by
    apply max_le
    · have hb := neg_le_abs (ε * signedCoefficient (B pResidual) n)
      rw [abs_mul, hε, one_mul] at hb
      rw [witness, signedCoefficient_sub]
      linarith [le_max_left (ε * signedCoefficient displacement n) 0]
    · exact add_nonneg (abs_nonneg _) (le_max_right _ _)
  calc
    _ ≤ ∑ n ∈ Finset.range (X + 1),
        (|signedCoefficient (B pResidual) n| * (n : ℝ) + max (ε * signedCoefficient displacement n) 0 * (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro n _
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right (hpoint n) (Nat.cast_nonneg n)
    _ ≤ _ := by
      rw [Finset.sum_add_distrib, displacement_charge_prefix_eq]
      exact add_le_add (hfirst.sum_le_tsum _
        (fun n _ => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg n))) le_rfl

/-- Raw prime remainders have exactly zero charge against every squarefree annihilator. -/
theorem annihilator_prime_hasSum (u : QHilbert) (hu : u ∈ closureᗮ) (p : ℕ) (hp : p.Prime) :
    HasSum (fun n : ℕ => signedCoefficient u n * ((n % p : ℕ) : ℝ)) 0 := by
  apply residue_charge_hasSum_zero u p hp.pos
  rw [real_inner_comm]
  exact Submodule.inner_right_of_mem_orthogonal
    (QSquarefreeDimension.qResidue_mem_of_squarefree hp.two_le hp.squarefree) hu

/-- Exact pairing of each legal Möbius defect with the untruncated signed charge. -/
theorem annihilator_defect_hasSum (u : QHilbert) (hu : u ∈ closureᗮ)
    (N : ℕ) (hN : Squarefree (N + 1)) :
    HasSum (fun n : ℕ => signedCoefficient u n * qSequence (defect N) n)
      (inner ℝ qOne u) := by
  have hz := Submodule.inner_right_of_mem_orthogonal
    (QSquarefreeResidualTail.squarefree_exactHead_mem_closure N hN) hu
  have he : inner ℝ u (defect N) = inner ℝ qOne u := by
    rw [real_inner_comm, defect, inner_sub_left, hz, sub_zero]
  rw [← he, qInner_weighted]
  exact (qSequence_product_summable u (defect N)).hasSum

/-- The physical witness detects the vanishing of the complete Q residual. -/
theorem riemannHypothesis_of_witness_mean_zero (h : inner ℝ qOne witness = 0) :
    RiemannHypothesis := by
  have hr := residual_eq_zero_of_witness_mean_zero h
  have hm : qOne ∈ closure := Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hr).symm
  exact QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
    (QSquarefreeCapacity.capacity_tendsto_iff_optimizer_closure.mpr hm)

end RiemannResearch.RH.QSquarefreeDisplacementRigidity
