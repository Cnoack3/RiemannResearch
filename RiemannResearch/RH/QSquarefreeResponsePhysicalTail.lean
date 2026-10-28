/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeResponseEndpoint
import RiemannResearch.RH.QSquarefreeResponseSeries
import RiemannResearch.RH.QCanonicalInnovation
import RiemannResearch.RH.QHilbertConvergence
import RiemannResearch.RH.QShiftedReciprocalBessel
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import RiemannResearch.RH.SquarefreeRadicalDifference
import RiemannResearch.RH.QSievePrimeJump
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Quantitative physical tails of the squarefree response series

Source: the user-provided argument and item 2 of
`InfiniteSquarefreeResponseResearch20261027.md`, commit
abd42dee58b969ce9c28ecfbf3cfec1e974c8b1a, for the quantitative tail estimate.
The sublinear finite-head argument below uses only membership in QHilbert;
periodicity is unnecessary. All infinite canonical and physical tails are
retained, and no arithmetic regularity or residual-vanishing premise is used.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.ZetaTwoHilbert

/-- Individual complete-Q vectors are sublinear at physical infinity. -/
theorem qSequence_div_nat_tendsto_zero (f : QHilbert) :
    Tendsto (fun k : ℕ => qSequence f k / (k : ℝ)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hs := (SquarefreeRadicalDifference.qNormalized_square_summable f).tendsto_atTop_zero
  have ht := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero, Real.norm_eq_abs] using ht

end RiemannResearch.RH.ZetaTwoHilbert

namespace RiemannResearch.RH.QCanonicalInnovation
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage
open QShiftedReciprocal QSquarefreeSmoothedProjection

def responseEnergyTail (N : ℕ) : ℝ := ∑' j, (responseCoefficient (j + N)) ^ 2
def physicalAbsoluteTail (N k : ℕ) : ℝ :=
  ∑' j, |qSequence (movingCorrection (j + N + 1) - movingCorrection (j + N)) k|

theorem targetCoefficient_tail_sq_summable (N : ℕ) :
    Summable (fun j => (targetCoefficient (j + N)) ^ 2) :=
  targetCoefficient_sq_summable.comp_injective
    (i := fun j : ℕ => j + N) (fun _ _ h => Nat.add_right_cancel h)

theorem responseCoefficient_tail_sq_summable (N : ℕ) :
    Summable (fun j => (responseCoefficient (j + N)) ^ 2) :=
  responseCoefficient_sq_summable.comp_injective
    (i := fun j : ℕ => j + N) (fun _ _ h => Nat.add_right_cancel h)

theorem targetEnergyTail_nonneg (N : ℕ) : 0 ≤ targetEnergyTail N :=
  tsum_nonneg (fun _ => sq_nonneg _)

theorem responseEnergyTail_nonneg (N : ℕ) : 0 ≤ responseEnergyTail N :=
  tsum_nonneg (fun _ => sq_nonneg _)

theorem smoothingTail_nonneg (N : ℕ) : 0 ≤ smoothingTail N :=
  tsum_nonneg (fun _ => sq_nonneg _)

theorem responseEnergyTail_le (N : ℕ) :
    responseEnergyTail N ≤ error N * smoothingTail N := by
  have hv : Summable (fun j =>
      ‖movingCorrection (j + N + 1) - movingCorrection (j + N)‖ ^ 2) :=
    movingCorrection_variation.1.comp_injective
      (i := fun j : ℕ => j + N) (fun _ _ h => Nat.add_right_cancel h)
  have hle (j : ℕ) : (responseCoefficient (j + N)) ^ 2 ≤
      ‖movingCorrection (j + N + 1) - movingCorrection (j + N)‖ ^ 2 := by
    rw [movingCorrection_increment_norm_sq]
    exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  exact ((responseCoefficient_tail_sq_summable N).tsum_le_tsum hle hv).trans
    (movingCorrection_variation_tail_le N)

private theorem finite_abs_mul_le_sqrt {ι : Type*} (s : Finset ι)
    (f g : ι → ℝ) (A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hf : (∑ i ∈ s, f i ^ 2) ≤ A) (hg : (∑ i ∈ s, g i ^ 2) ≤ D) :
    (∑ i ∈ s, |f i| * |g i|) ≤ Real.sqrt (A * D) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => |f i|) (fun i => |g i|)
  simp only [sq_abs] at hcs
  have hmul := mul_le_mul hf hg
    (Finset.sum_nonneg (fun i hi => sq_nonneg (g i))) hA
  have hs := Real.sq_sqrt (mul_nonneg hA hD)
  have hn := Real.sqrt_nonneg (A * D)
  have hp : 0 ≤ ∑ i ∈ s, |f i| * |g i| :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  nlinarith

/-- Original-index Bessel, retaining zero and dependent innovations. -/
theorem direction_coordinate_finite_bessel (s : Finset ℕ) (k : ℕ) :
    (∑ j ∈ s, (direction j k) ^ 2) ≤ 1 := by
  classical
  have h := orthonormal_coordinate_square_sum_le_one
    (fun i : Active => direction i) active_orthonormal
    (s.subtype (fun j => direction j ≠ 0)) k
  have he (j : ℕ) :
      (if direction j ≠ 0 then (direction j k) ^ 2 else 0) = (direction j k) ^ 2 := by
    by_cases hj : direction j = 0 <;> simp [hj]
  have hs := Finset.sum_subtype_eq_sum_filter
    (s := s) (p := fun j => direction j ≠ 0)
    (fun j : ℕ => (direction j k) ^ 2)
  have hf : (∑ j ∈ s with direction j ≠ 0, (direction j k) ^ 2) ≤ 1 :=
    hs.symm.trans_le h
  simpa only [Finset.sum_filter, he] using hf

/-- The exact physical evaluation Bessel constant, with the zero anchor. -/
theorem direction_physical_finite_bessel (s : Finset ℕ) (k : ℕ) :
    (∑ j ∈ s, (qSequence (direction j) k) ^ 2) ≤ zetaTwo * (k : ℝ) ^ 2 := by
  cases k with
  | zero => simp
  | succ k =>
      simp_rw [qSequence_succ, div_pow, Real.sq_sqrt (qWeight_pos k).le]
      rw [← Finset.sum_div]
      calc
        _ ≤ 1 / qWeight k := div_le_div_of_nonneg_right
          (direction_coordinate_finite_bessel s k) (qWeight_pos k).le
        _ = zetaTwo * ((k + 1 : ℕ) : ℝ) ^ 2 := by
          simp [qWeight, positiveQWeight]

theorem direction_physical_finite_tail_bessel (s : Finset ℕ) (N k : ℕ) :
    (∑ j ∈ s, (qSequence (direction (j + N)) k) ^ 2) ≤ zetaTwo * (k : ℝ) ^ 2 := by
  classical
  have h := direction_physical_finite_bessel (s.image (fun j => j + N)) k
  rw [Finset.sum_image] at h
  · exact h
  · intro i hi j hj hij
    exact Nat.add_right_cancel hij

theorem orthogonalTerm_physical_finite_tail_le (s : Finset ℕ) (N k : ℕ) :
    (∑ j ∈ s, |qSequence (orthogonalTerm (j + N)) k|) ≤
      Real.sqrt zetaTwo * (k : ℝ) * Real.sqrt (responseEnergyTail N) := by
  have hc : (∑ j ∈ s, (responseCoefficient (j + N)) ^ 2) ≤ responseEnergyTail N :=
    (responseCoefficient_tail_sq_summable N).sum_le_tsum s (fun j hj => sq_nonneg _)
  have hb := direction_physical_finite_tail_bessel s N k
  have h := finite_abs_mul_le_sqrt s (fun j => responseCoefficient (j + N))
    (fun j => qSequence (direction (j + N)) k)
    (responseEnergyTail N) (zetaTwo * (k : ℝ)^2)
    (responseEnergyTail_nonneg N) (mul_nonneg zetaTwo_pos.le (sq_nonneg _)) hc hb
  have he (j : ℕ) : |qSequence (orthogonalTerm (j + N)) k| =
      |responseCoefficient (j + N)| * |qSequence (direction (j + N)) k| := by
    simp only [orthogonalTerm, ← qEvalCLM_apply, map_smul, smul_eq_mul, abs_mul]
  simp_rw [he]
  have hs : Real.sqrt (responseEnergyTail N * (zetaTwo * (k : ℝ)^2)) =
      Real.sqrt zetaTwo * (k : ℝ) * Real.sqrt (responseEnergyTail N) := by
    rw [Real.sqrt_mul (responseEnergyTail_nonneg N), Real.sqrt_mul zetaTwo_pos.le,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (Nat.cast_nonneg k)]
    ring
  rwa [hs] at h

theorem correctionTerm_finite_tail_norm_le (s : Finset ℕ) (N : ℕ) :
    (∑ j ∈ s, ‖correctionTerm (j + N)‖) ≤
      Real.sqrt (targetEnergyTail N * smoothingTail N) := by
  have ha : (∑ j ∈ s, (targetCoefficient (j + N)) ^ 2) ≤ targetEnergyTail N :=
    (targetCoefficient_tail_sq_summable N).sum_le_tsum s (fun j hj => sq_nonneg _)
  have hb : (∑ j ∈ s, ‖B (direction (j + N))‖ ^ 2) ≤ smoothingTail N :=
    (B_direction_tail_summable N).sum_le_tsum s (fun j hj => sq_nonneg _)
  calc
    _ ≤ ∑ j ∈ s, |targetCoefficient (j + N)| * ‖B (direction (j + N))‖ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [correctionTerm, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (Submodule.norm_starProjection_apply_le _ _)
        (abs_nonneg _)
    _ ≤ Real.sqrt (targetEnergyTail N * smoothingTail N) := by
      simpa only [abs_of_nonneg (norm_nonneg _)] using
        finite_abs_mul_le_sqrt s (fun j => targetCoefficient (j + N))
          (fun j => ‖B (direction (j + N))‖) (targetEnergyTail N) (smoothingTail N)
          (targetEnergyTail_nonneg N) (smoothingTail_nonneg N) ha hb

theorem correctionTerm_physical_finite_tail_le (s : Finset ℕ) (N k : ℕ) :
    (∑ j ∈ s, |qSequence (correctionTerm (j + N)) k|) ≤
      Real.sqrt zetaTwo * (k : ℝ) * Real.sqrt (targetEnergyTail N * smoothingTail N) := by
  calc
    _ ≤ ∑ j ∈ s, (Real.sqrt zetaTwo * (k : ℝ)) * ‖correctionTerm (j + N)‖ := by
      exact Finset.sum_le_sum (fun j hj => QPrimePowerSieve.qSequence_abs_le _ _)
    _ = (Real.sqrt zetaTwo * (k : ℝ)) * ∑ j ∈ s, ‖correctionTerm (j + N)‖ :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (correctionTerm_finite_tail_norm_le s N)
      (by positivity)

/-- Complete infinite physical absolute tail; no physical truncation is used. -/
theorem physicalAbsoluteTail_le (N k : ℕ) :
    physicalAbsoluteTail N k ≤ Real.sqrt zetaTwo * (k : ℝ) *
      (Real.sqrt (responseEnergyTail N) + Real.sqrt (targetEnergyTail N * smoothingTail N)) := by
  apply Real.tsum_le_of_sum_le (fun j => abs_nonneg _)
  intro s
  calc
    _ ≤ (∑ j ∈ s, |qSequence (orthogonalTerm (j + N)) k|) +
        ∑ j ∈ s, |qSequence (correctionTerm (j + N)) k| := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro j hj
      rw [movingCorrection_increment, ← qEvalCLM_apply, map_sub]
      simpa only [qEvalCLM_apply, sub_zero, zero_sub, abs_neg] using
        abs_sub_le (qSequence (orthogonalTerm (j + N)) k) 0
          (qSequence (correctionTerm (j + N)) k)
    _ ≤ _ := by
      have ho := orthogonalTerm_physical_finite_tail_le s N k
      have hc := correctionTerm_physical_finite_tail_le s N k
      nlinarith

private theorem real_series_tail_tendsto_zero (f : ℕ → ℝ) (hf : Summable f) :
    Tendsto (fun N => ∑' j, f (j + N)) atTop (𝓝 0) := by
  have he (N : ℕ) : (∑' j, f (j + N)) = (∑' j, f j) - ∑ j ∈ Finset.range N, f j := by
    have h := hf.sum_add_tsum_nat_add N
    linarith
  simp_rw [he]
  have hc : Tendsto (fun _ : ℕ => ∑' j, f j) atTop (𝓝 (∑' j, f j)) :=
    tendsto_const_nhds
  simpa only [sub_self] using hc.sub hf.hasSum.tendsto_sum_nat

theorem targetEnergyTail_tendsto_zero : Tendsto targetEnergyTail atTop (𝓝 0) :=
  real_series_tail_tendsto_zero _ targetCoefficient_sq_summable

theorem responseEnergyTail_tendsto_zero : Tendsto responseEnergyTail atTop (𝓝 0) :=
  real_series_tail_tendsto_zero _ responseCoefficient_sq_summable

def physicalTailBound (N : ℕ) : ℝ := Real.sqrt zetaTwo *
  (Real.sqrt (responseEnergyTail N) + Real.sqrt (targetEnergyTail N * smoothingTail N))

theorem physicalTailBound_tendsto_zero : Tendsto physicalTailBound atTop (𝓝 0) := by
  change Tendsto (fun N => physicalTailBound N) atTop (𝓝 0)
  have hc := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp responseEnergyTail_tendsto_zero
  have ha := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp
    (show Tendsto (fun N => targetEnergyTail N * smoothingTail N) atTop (𝓝 0) by
      simpa only [mul_zero] using targetEnergyTail_tendsto_zero.mul smoothingTail_tendsto_zero)
  simpa only [physicalTailBound, Function.comp_def, Real.sqrt_zero, add_zero, mul_zero]
    using (hc.add ha).const_mul (Real.sqrt zetaTwo)

theorem physicalAbsoluteTail_nonneg (N k : ℕ) : 0 ≤ physicalAbsoluteTail N k :=
  tsum_nonneg (fun _ => abs_nonneg _)

theorem physicalAbsoluteTail_div_nat_le (N k : ℕ) :
    physicalAbsoluteTail N k / (k : ℝ) ≤ physicalTailBound N := by
  by_cases hk : k = 0
  · subst k
    simp only [Nat.cast_zero, div_zero]
    unfold physicalTailBound
    positivity
  · have hkR : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
    apply (div_le_iff₀ hkR).mpr
    have h := physicalAbsoluteTail_le N k
    simpa only [physicalTailBound, mul_assoc, mul_left_comm, mul_comm] using h

/-- Uniformity covers every physical site, including the zero anchor. -/
theorem physicalAbsoluteTail_div_nat_uniform :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      ∀ k : ℕ, |physicalAbsoluteTail N k / (k : ℝ)| < ε := by
  intro ε hε
  filter_upwards [physicalTailBound_tendsto_zero.eventually_lt_const hε] with N hN
  intro k
  rw [abs_of_nonneg (div_nonneg (physicalAbsoluteTail_nonneg N k) (Nat.cast_nonneg k))]
  exact (physicalAbsoluteTail_div_nat_le N k).trans_lt hN

theorem physicalAbsoluteTail_summable (N k : ℕ) :
    Summable (fun j => |qSequence
      (movingCorrection (j + N + 1) - movingCorrection (j + N)) k|) :=
  (movingCorrection_increment_physical_abs_summable k).comp_injective
    (i := fun j : ℕ => j + N) (fun _ _ h => Nat.add_right_cancel h)

/-- Exact canonical head/tail split retains all physical and stage tails. -/
theorem physicalAbsoluteTail_head_tail (N k : ℕ) :
    physicalAbsoluteTail 0 k =
      (∑ j ∈ Finset.range N,
        |qSequence (movingCorrection (j + 1) - movingCorrection j) k|) +
      physicalAbsoluteTail N k := by
  have h := (movingCorrection_increment_physical_abs_summable k).sum_add_tsum_nat_add N
  simpa only [physicalAbsoluteTail, Nat.add_zero] using h.symm

/-- The finite head is sublinear because each complete-Q vector is sublinear;
no periodicity hypothesis is required. -/
theorem physicalAbsoluteHead_div_nat_tendsto_zero (N : ℕ) :
    Tendsto (fun k : ℕ =>
      (∑ j ∈ Finset.range N,
        |qSequence (movingCorrection (j + 1) - movingCorrection j) k|) / (k : ℝ))
      atTop (𝓝 0) := by
  have h := tendsto_finsetSum (Finset.range N) (fun j _ =>
    (qSequence_div_nat_tendsto_zero
      (movingCorrection (j + 1) - movingCorrection j)).abs)
  have hcast (k : ℕ) : |(k : ℝ)| = (k : ℝ) :=
    abs_of_nonneg (Nat.cast_nonneg k)
  simpa only [abs_zero, Finset.sum_const_zero, abs_div, hcast, Finset.sum_div] using h

/-- Total temporal variation is sublinear at physical infinity. -/
theorem physicalTotalVariation_div_nat_tendsto_zero :
    Tendsto (fun k : ℕ => physicalAbsoluteTail 0 k / (k : ℝ)) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun k => ha.trans_le
      (div_nonneg (physicalAbsoluteTail_nonneg 0 k) (Nat.cast_nonneg k)))
  · intro ε hε
    have hhalf : 0 < ε / 2 := by positivity
    obtain ⟨N, hN⟩ :=
      (physicalTailBound_tendsto_zero.eventually_lt_const hhalf).exists
    filter_upwards [(physicalAbsoluteHead_div_nat_tendsto_zero N).eventually_lt_const hhalf]
      with k hk
    rw [physicalAbsoluteTail_head_tail N k, add_div]
    have ht := physicalAbsoluteTail_div_nat_le N k
    linarith

end RiemannResearch.RH.QCanonicalInnovation
