/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoRadicalRowCriterion
import RiemannResearch.RH.SquarefreeParetoTransfer

/-!
# Actual inverse-square to Pareto closure transfer

Source: user-provided exact optimizer-cancellation argument, 8 October 2026.
The pointwise comparison is `P(k) ≤ ζ(2) Q(k)` at every physical coordinate.
The map preserves the complete sequence, its constant target, and every
legal fractional-part atom. The resulting RH implication uses the existing
Mellin separation theorem. No RH-to-squarefree-density implication or
asymptotic cancellation provider is presumed.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.ZetaTwoParetoTransfer
open ZetaTwoProbability ZetaTwoHilbert
open Pareto
open Pareto.CoefficientStabilization
open RiemannResearch.Analysis.ExhaustiveWalk

theorem paretoWeight_le_zetaTwo_mul_QWeight (k : ℕ) :
    positiveWeight k ≤ zetaTwo * positiveQWeight k := by
  by_cases hk : k = 0
  · subst k
    simp [positiveWeight, positiveQWeight]
  · have hkR : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    have he : zetaTwo * positiveQWeight k = 1 / (k : ℝ) ^ 2 := by
      unfold positiveQWeight
      field_simp [ne_of_gt zetaTwo_pos, ne_of_gt hkR]
    rw [he]
    unfold positiveWeight
    apply one_div_le_one_div_of_le (sq_pos_of_pos hkR)
    nlinarith

theorem qSequence_pareto_square_summable (f : QHilbert) :
    Summable (fun k => positiveWeight k * (qSequence f k) ^ 2) := by
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (positiveWeight_nonneg k) (sq_nonneg _)) _
    ((qSequence_square_summable f).mul_left zetaTwo)
  intro k
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (paretoWeight_le_zetaTwo_mul_QWeight k) (sq_nonneg (qSequence f k))

/-- Reencode the same complete physical sequence with the Pareto weights. -/
def toPareto (f : QHilbert) : ThresholdHilbert :=
  sequenceHilbert (qSequence f) (qSequence_pareto_square_summable f)

@[simp] theorem toPareto_sequence (f : QHilbert) :
    hilbertSequence (toPareto f) = qSequence f :=
  hilbertSequence_sequenceHilbert _ _ (qSequence_zero f)

def toParetoLinear : QHilbert →ₗ[ℝ] ThresholdHilbert where
  toFun := toPareto
  map_add' f g := by
    apply hilbertSequence_injective
    change hilbertSequence (toPareto (f + g)) =
      hilbertSequenceLinear (toPareto f + toPareto g)
    rw [map_add]
    change hilbertSequence (toPareto (f + g)) =
      hilbertSequence (toPareto f) + hilbertSequence (toPareto g)
    simp only [toPareto_sequence]
    exact qSequenceLinear.map_add f g
  map_smul' c f := by
    apply hilbertSequence_injective
    change hilbertSequence (toPareto (c • f)) =
      hilbertSequenceLinear (c • toPareto f)
    rw [map_smul]
    change hilbertSequence (toPareto (c • f)) = c • hilbertSequence (toPareto f)
    simp only [toPareto_sequence]
    exact qSequenceLinear.map_smul c f

/-- Every infinite tail is included in the norm comparison. -/
theorem toPareto_norm_sq_le (f : QHilbert) :
    ‖toPareto f‖ ^ 2 ≤ zetaTwo * ‖f‖ ^ 2 := by
  rw [hilbert_norm_weighted_sq, toPareto_sequence, qNorm_weighted_sq,
    ← tsum_mul_left]
  apply Summable.tsum_le_tsum _ (qSequence_pareto_square_summable f)
    ((qSequence_square_summable f).mul_left zetaTwo)
  intro k
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (paretoWeight_le_zetaTwo_mul_QWeight k) (sq_nonneg (qSequence f k))

theorem toPareto_norm_le (f : QHilbert) :
    ‖toPareto f‖ ≤ Real.sqrt zetaTwo * ‖f‖ := by
  have hs : ‖toPareto f‖ ^ 2 ≤ (Real.sqrt zetaTwo * ‖f‖) ^ 2 := by
    simpa only [mul_pow, Real.sq_sqrt zetaTwo_pos.le] using toPareto_norm_sq_le f
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp hs

def toParetoCLM : QHilbert →L[ℝ] ThresholdHilbert :=
  toParetoLinear.mkContinuous (Real.sqrt zetaTwo) toPareto_norm_le

@[simp] theorem toParetoCLM_apply (f : QHilbert) : toParetoCLM f = toPareto f := rfl

@[simp] theorem toPareto_qOne : toPareto qOne = hilbertOne := by
  apply hilbertSequence_injective
  rw [toPareto_sequence, qSequence_qOne, hilbertOne_sequence] <;>
    funext k <;> simp [qOneSequence, zeroAnchor]

@[simp] theorem toPareto_qResidue (d : ℕ) (hd : 0 < d) :
    toPareto (qResidue d) = Pareto.BaezDuarte.residueVector d := by
  apply hilbertSequence_injective
  rw [toPareto_sequence, qSequence_qResidue, Pareto.BaezDuarte.residueVector,
    dif_pos hd, normalizedResidueHilbert_sequence]

theorem toPareto_residueAtom (i : ℕ) :
    toPareto (qResidue (i + 2)) = residueAtom i := by
  rw [toPareto_qResidue (i + 2) (by omega)] <;>
    simp [Pareto.BaezDuarte.residueVector, residueAtom]

/-- Finite legal trials are preserved with precisely the same coefficients. -/
theorem toPareto_finiteResidueSum (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ d ∈ s, 0 < d) :
    toPareto (∑ d ∈ s, a d • qResidue d) = Pareto.BaezDuarte.finiteResidueSum s a := by
  change toParetoLinear (∑ d ∈ s, a d • qResidue d) = _
  rw [map_sum]
  unfold Pareto.BaezDuarte.finiteResidueSum
  apply Finset.sum_congr rfl
  intro d hd
  rw [map_smul]
  change a d • toPareto (qResidue d) = _
  rw [toPareto_qResidue d (hs d hd)]

private theorem mapped_squarefreeAtom_mem (i : ℕ) :
    toParetoCLM (ZetaTwoOptimizerStage.squarefreeAtom i) ∈ closedSpace := by
  change toPareto (ZetaTwoOptimizerStage.squarefreeAtom i) ∈ closedSpace
  unfold ZetaTwoOptimizerStage.squarefreeAtom
  split_ifs with hi
  · rw [toPareto_residueAtom]
    exact (Submodule.span ℝ (Set.range residueAtom)).le_topologicalClosure
      (Submodule.subset_span ⟨i, rfl⟩)
  · change toParetoLinear 0 ∈ closedSpace
    rw [map_zero]
    exact Submodule.zero_mem _

/-- The existing complete Q-to-Pareto map transports every squarefree-closed
vector, not only the constant target. -/
theorem toPareto_mem_closedSpace {f : QHilbert}
    (hf : f ∈ ZetaTwoOptimizerStage.closure) : toPareto f ∈ closedSpace := by
  let K : Submodule ℝ QHilbert := closedSpace.comap toParetoCLM.toLinearMap
  have hspan : Submodule.span ℝ (Set.range ZetaTwoOptimizerStage.squarefreeAtom) ≤ K := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    change toPareto (ZetaTwoOptimizerStage.squarefreeAtom i) ∈ closedSpace
    unfold ZetaTwoOptimizerStage.squarefreeAtom
    split_ifs with hi
    · rw [toPareto_residueAtom]
      exact (Submodule.span ℝ (Set.range residueAtom)).le_topologicalClosure
        (Submodule.subset_span ⟨i, rfl⟩)
    · change toParetoLinear 0 ∈ closedSpace
      rw [map_zero]
      exact Submodule.zero_mem _
  have hclosed : IsClosed (closedSpace : Set ThresholdHilbert) := by
    change IsClosed (_root_.closure
      (Submodule.span ℝ (Set.range residueAtom) : Set ThresholdHilbert))
    exact isClosed_closure
  have hKclosed : IsClosed (K : Set QHilbert) := hclosed.preimage toParetoCLM.continuous
  have hf' : f ∈ _root_.closure
      (Submodule.span ℝ (Set.range ZetaTwoOptimizerStage.squarefreeAtom) : Set QHilbert) := hf
  exact (closure_minimal hspan hKclosed) hf'

/-- The inverse-square squarefree approximation transfers into the complete
Pareto residue closure. -/
theorem paretoOne_mem_closedSpace_of_qOne_mem_closure
    (h : qOne ∈ ZetaTwoOptimizerStage.closure) : hilbertOne ∈ closedSpace := by
  let K : Submodule ℝ QHilbert := closedSpace.comap toParetoCLM.toLinearMap
  have hspan : Submodule.span ℝ (Set.range ZetaTwoOptimizerStage.squarefreeAtom) ≤ K := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact mapped_squarefreeAtom_mem i
  have hpclosed : IsClosed (closedSpace : Set ThresholdHilbert) := by
    change IsClosed (_root_.closure (Submodule.span ℝ (Set.range residueAtom) : Set ThresholdHilbert))
    exact isClosed_closure
  have hKclosed : IsClosed (K : Set QHilbert) :=
    hpclosed.preimage toParetoCLM.continuous
  have hqclosure : qOne ∈ _root_.closure
      (Submodule.span ℝ (Set.range ZetaTwoOptimizerStage.squarefreeAtom) : Set QHilbert) := h
  have hm : qOne ∈ K := (closure_minimal hspan hKclosed) hqclosure
  change toParetoCLM qOne ∈ closedSpace at hm
  simpa only [toParetoCLM_apply, toPareto_qOne] using hm

/-- The exact norm-transfer assembly into the existing Mellin RH theorem.
The squarefree closure membership is the remaining substantive input. -/
theorem riemannHypothesis_of_qOne_mem_squarefree_closure
    (h : qOne ∈ ZetaTwoOptimizerStage.closure) : RiemannHypothesis := by
  apply Pareto.riemannHypothesis_of_hilbertOne_mem_legalClosure {n : ℕ | 0 < n}
    (fun _ hn => hn)
  exact closedSpace_le_legalClosure (paretoOne_mem_closedSpace_of_qOne_mem_closure h)

/-- Conditional research reduction: only the positive signed optimizer
correction remains as a substantive asymptotic hypothesis. The quartic
floor normalization and complete norm transfer are discharged internally. -/
theorem riemannHypothesis_of_cofinal_positiveCorrection_decay
    (κ : ℕ → ℕ) (hκ : Tendsto κ atTop atTop)
    (hcorrection : Tendsto
      (fun j => max (ZetaTwoOptimizerStage.signedCorrection (κ j)) 0 /
        ZetaTwoOptimizerStage.error (κ j)) atTop (𝓝 0)) : RiemannHypothesis :=
  riemannHypothesis_of_qOne_mem_squarefree_closure
    (ZetaTwoOptimizerStage.mem_closure_of_cofinal_positiveCorrection_decay
      κ hκ hcorrection)

/-- Conditional research reduction: all fixed squarefree signed reciprocal
base differences vanish along one common cofinal sequence. The actual strong
limit, inverse-square summability, and Mellin transfer are supplied internally.
The base-decay hypothesis remains an Open arithmetic provider. -/
theorem riemannHypothesis_of_cofinal_squarefree_reciprocal_differences
    (κ : ℕ → ℕ) (hκ : Tendsto κ atTop atTop)
    (hbase : ∀ a : ℕ, 2 ≤ a → Squarefree a →
      Tendsto (fun j =>
        SquarefreeRadicalDifference.qDifference
          (reciprocalD (ZetaTwoOptimizerStage.residual (κ j))) a)
        atTop (𝓝 0)) : RiemannHypothesis :=
  riemannHypothesis_of_qOne_mem_squarefree_closure
    (ZetaTwoRadicalRowCriterion.mem_closure_of_cofinal_squarefree_reciprocal_differences
      κ hκ hbase)

end RiemannResearch.RH.ZetaTwoParetoTransfer
noncomputable section
open scoped BigOperators Topology
namespace RiemannResearch.RH.ZetaTwoParetoTransfer
open ZetaTwoProbability ZetaTwoHilbert
open Pareto
open Pareto.CoefficientStabilization
open RiemannResearch.Analysis.ExhaustiveWalk

/-- Converse pointwise comparison of the two complete weights. -/
theorem zetaTwo_mul_QWeight_le_two_mul_paretoWeight (k : ℕ) :
    zetaTwo * positiveQWeight k ≤ 2 * positiveWeight k := by
  by_cases hk : k = 0
  · subst k
    simp [positiveWeight, positiveQWeight]
  · have hkR : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    have hkR1 : (1 : ℝ) ≤ k := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk)
    have he : zetaTwo * positiveQWeight k = 1 / (k : ℝ) ^ 2 := by
      unfold positiveQWeight
      field_simp [ne_of_gt zetaTwo_pos, ne_of_gt hkR]
    rw [he]
    unfold positiveWeight
    change 1 / (k : ℝ) ^ 2 ≤ 2 * (1 / ((k : ℝ) * ((k : ℝ) + 1)))
    rw [show 2 * (1 / ((k : ℝ) * ((k : ℝ) + 1))) =
      2 / ((k : ℝ) * ((k : ℝ) + 1)) by ring]
    apply (div_le_div_iff₀ (sq_pos_of_pos hkR)
      (mul_pos hkR (by positivity : (0 : ℝ) < (k : ℝ) + 1))).mpr
    nlinarith

/-- The reverse complete norm comparison. Together with
toPareto_norm_sq_le, this gives
‖x‖_P² ≤ ζ(2) ‖x‖_Q² ≤ 2 ‖x‖_P² for the same physical sequence. -/
theorem zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq (f : QHilbert) :
    zetaTwo * ‖f‖ ^ 2 ≤ 2 * ‖toPareto f‖ ^ 2 := by
  rw [qNorm_weighted_sq, hilbert_norm_weighted_sq, toPareto_sequence]
  rw [← tsum_mul_left]
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum _
    ((qSequence_square_summable f).mul_left zetaTwo)
    ((qSequence_pareto_square_summable f).mul_left 2)
  intro k
  calc
    zetaTwo * (positiveQWeight k * (qSequence f k) ^ 2) =
        (zetaTwo * positiveQWeight k) * (qSequence f k) ^ 2 := by ring
    _ ≤ (2 * positiveWeight k) * (qSequence f k) ^ 2 :=
      mul_le_mul_of_nonneg_right (zetaTwo_mul_QWeight_le_two_mul_paretoWeight k)
        (sq_nonneg (qSequence f k))
    _ = 2 * (positiveWeight k * (qSequence f k) ^ 2) := by ring


/-- Exact positive change-of-law correction, including the infinite tail. -/
def normCorrection (f : QHilbert) : ℝ :=
  ∑' k, (positiveQWeight k / ((k : ℝ) + 1)) * (qSequence f k) ^ 2

theorem normCorrection_summable (f : QHilbert) :
    Summable (fun k => (positiveQWeight k / ((k : ℝ) + 1)) * (qSequence f k) ^ 2) := by
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (div_nonneg (positiveQWeight_nonneg k) (by positivity))
      (sq_nonneg _)) _ (qSequence_square_summable f)
  intro k
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact div_le_self (positiveQWeight_nonneg k) (by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith)

theorem paretoWeight_eq_zetaTwo_QWeight_sub (k : ℕ) :
    positiveWeight k = zetaTwo * positiveQWeight k -
      zetaTwo * (positiveQWeight k / ((k : ℝ) + 1)) := by
  by_cases hk : k = 0
  · subst k
    simp [positiveWeight, positiveQWeight]
  · have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    unfold positiveWeight positiveQWeight
    field_simp [hkR, hk1, ne_of_gt zetaTwo_pos]
    ring

theorem toPareto_norm_sq_exact (f : QHilbert) :
    ‖toPareto f‖ ^ 2 = zetaTwo * ‖f‖ ^ 2 - zetaTwo * normCorrection f := by
  calc
    ‖toPareto f‖ ^ 2 = ∑' k,
        (zetaTwo * (positiveQWeight k * (qSequence f k) ^ 2) -
          zetaTwo * ((positiveQWeight k / ((k : ℝ) + 1)) *
            (qSequence f k) ^ 2)) := by
      rw [hilbert_norm_weighted_sq, toPareto_sequence]
      apply tsum_congr
      intro k
      rw [paretoWeight_eq_zetaTwo_QWeight_sub]
      ring
    _ = (∑' k, zetaTwo * (positiveQWeight k * (qSequence f k) ^ 2)) -
        ∑' k, zetaTwo * ((positiveQWeight k / ((k : ℝ) + 1)) *
          (qSequence f k) ^ 2) :=
      ((qSequence_square_summable f).mul_left zetaTwo).tsum_sub
        ((normCorrection_summable f).mul_left zetaTwo)
    _ = zetaTwo * ‖f‖ ^ 2 - zetaTwo * normCorrection f := by
      rw [tsum_mul_left, tsum_mul_left, ← qNorm_weighted_sq]
      rfl

end RiemannResearch.RH.ZetaTwoParetoTransfer
