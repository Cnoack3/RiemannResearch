import RiemannResearch.RH.QReciprocalCostEquivalence
import RiemannResearch.RH.QParetoMetric
import RiemannResearch.RH.ExactHeadResidualTail
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import RiemannResearch.RH.CRTCarryArithmetic

/-!
# Finite-coordinate certificates for complete D-cost

A finite coordinate sum is supplemented by explicit bounds on both infinite tails. Arbitrary finite residue coefficients are covered by their absolute coefficient sum. The exact head still retains signed cross terms. This bound is a certificate for a fixed stage, not a uniform RH provider.

Research agenda: D_Residue_Density_PQ_Nyman_Beurling_2026-11-11.pdf, Section 9.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QReciprocalCostCertificates
open Pareto ZetaTwoHilbert ZetaTwoProbability QReciprocalMetric QReciprocalCostEquivalence

def headCost (α : ℝ) (v : QHilbert) (H : ℕ) : ℝ :=
  ∑ n ∈ Finset.range H, (((D (v-qOne)) n)^2 + α*(v n)^2)

theorem cost_eq_head_add_tails (α : ℝ) (v : QHilbert) (H : ℕ) :
    cost α qOne v = headCost α v H +
      ‖hilbertTailShift (D (v-qOne)) H‖^2 + α*‖hilbertTailShift v H‖^2 := by
  rw [hilbertTailShift_norm_sq, hilbertTailShift_norm_sq]
  simp only [cost, headCost, Finset.sum_add_distrib, mul_sub, Finset.mul_sum]
  ring

theorem headCost_le (α : ℝ) (hα : 0 ≤ α) (v : QHilbert) (H : ℕ) :
    headCost α v H ≤ cost α qOne v := by
  rw [cost_eq_head_add_tails]
  nlinarith [sq_nonneg ‖hilbertTailShift (D (v-qOne)) H‖,
    mul_nonneg hα (sq_nonneg ‖hilbertTailShift v H‖)]

theorem reciprocal_tail_sq_le (f : QHilbert) (H : ℕ) :
    ‖hilbertTailShift (D f) H‖^2 ≤
      ‖hilbertTailShift f H‖^2 / ((H : ℝ)+1)^2 := by
  rw [hilbert_norm_sq, hilbert_norm_sq, ← tsum_div_const]
  apply Summable.tsum_le_tsum _ (hilbert_coordinate_square_summable _)
    ((hilbert_coordinate_square_summable _).div_const _)
  intro n
  change (D f (n+H))^2 ≤ (f (n+H))^2 / ((H : ℝ)+1)^2
  rw [D_apply, div_pow]
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  push_cast
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem cost_certificate (α : ℝ) (hα : 0 ≤ α) (v : QHilbert)
    (H : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hv : ∀ n, 0 < n → |qSequence v n| ≤ A) :
    cost α qOne v ≤ headCost α v H +
      ((1+1/((H : ℝ)+1))/zetaTwo) *
        ((A+1)^2/((H : ℝ)+1)^3 + α*A^2/((H : ℝ)+1)) := by
  have he : ∀ n, 0 < n → |qSequence (v-qOne) n| ≤ A+1 := by
    intro n hn
    change |qSequenceLinear (v-qOne) n| ≤ _
    rw [map_sub]
    change |qSequence v n-qSequence qOne n| ≤ _
    have h1 : qSequence qOne n = 1 := by
      rw [qSequence_qOne]
      simp [qOneSequence, Nat.ne_of_gt hn]
    rw [h1]
    exact (abs_sub _ _).trans (by simpa using add_le_add_right (hv n hn) 1)
  have ht := QParetoMetric.tail_norm_sq_le_of_bounded v H A hA hv
  have hte := QParetoMetric.tail_norm_sq_le_of_bounded (v-qOne) H (A+1)
    (by linarith) he
  have hd := (reciprocal_tail_sq_le (v-qOne) H).trans
    (div_le_div_of_nonneg_right hte (by positivity))
  rw [cost_eq_head_add_tails]
  have hs := add_le_add hd (mul_le_mul_of_nonneg_left ht hα)
  have hr : ((1+1/((H : ℝ)+1))/zetaTwo)*(A+1)^2/((H : ℝ)+1)/((H : ℝ)+1)^2 +
      α*(((1+1/((H : ℝ)+1))/zetaTwo)*A^2/((H : ℝ)+1)) =
      ((1+1/((H : ℝ)+1))/zetaTwo) *
        ((A+1)^2/((H : ℝ)+1)^3 + α*A^2/((H : ℝ)+1)) := by
    field_simp <;> ring
  rw [hr] at hs
  linarith

theorem finite_residue_sequence_bound {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (c : ι → ℝ) (n : ℕ) :
    |qSequence (Fintype.linearCombination ℝ (fun i => qResidue (d i)) c) n| ≤
      ∑ i, |c i| := by
  have hg (i : ι) : |qSequence (qResidue (d i)) n| ≤ 1 := by
    rw [qSequence_qResidue]
    exact CRTCarryArithmetic.residueFraction_abs_le_one (d i) n
  change |qSequenceLinear (Fintype.linearCombination ℝ (fun i => qResidue (d i)) c) n| ≤ _
  simp only [Fintype.linearCombination_apply, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    _ ≤ ∑ i, |c i*qSequence (qResidue (d i)) n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |c i| := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hg i)

theorem finite_residue_cost_certificate {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (c : ι → ℝ)
    (α : ℝ) (hα : 0 ≤ α) (H : ℕ) :
    let v := Fintype.linearCombination ℝ (fun i => qResidue (d i)) c
    let A := ∑ i, |c i|
    cost α qOne v ≤ headCost α v H +
      ((1+1/((H : ℝ)+1))/zetaTwo) *
        ((A+1)^2/((H : ℝ)+1)^3 + α*A^2/((H : ℝ)+1)) := by
  dsimp only
  apply cost_certificate α hα _ H _ (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  intro n _
  exact finite_residue_sequence_bound d c n

end RiemannResearch.RH.QReciprocalCostCertificates
