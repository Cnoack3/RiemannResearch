/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.ExactHeadResidualTail
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ParetoWeights
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Exact metric correction and sharper head-tail transfer to Q

Source: user-requested Pareto-to-Q transfer, 15 October 2026.
All equalities retain the complete infinite energy. The reciprocal diagonal
acts on the common raw l2 carrier; when applied to a Pareto encoding it
multiplies its physical coordinate k by 1/k.

The global factor two improves to 1 + 1/(H+1) on vectors vanishing through H.
This improves comparisons, not the unresolved uniform arithmetic bound.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.QParetoMetric
open Pareto ZetaTwoProbability ZetaTwoHilbert ZetaTwoParetoTransfer QParetoEquivalence

/-- The complete, exact Radon--Nikodym identity, including the anchored zero. -/
theorem weight_identity (k : ℕ) :
    zetaTwo * positiveQWeight k =
      positiveWeight k + positiveWeight k / (k : ℝ) := by
  by_cases hk : k = 0
  · subst k
    simp [positiveQWeight, positiveWeight]
  · have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    unfold positiveQWeight positiveWeight
    field_simp [ne_of_gt zetaTwo_pos, hkR, hk1]

theorem scaled_coordinate_sq (f : QHilbert) (n : ℕ) :
    zetaTwo * (f n) ^ 2 =
      (toPareto f n) ^ 2 + (toPareto f n) ^ 2 / ((n : ℝ) + 1) := by
  have hp := hilbertSequence_weighted_square (toPareto f) n
  rw [toPareto_sequence] at hp
  calc
    zetaTwo * (f n) ^ 2 =
        (zetaTwo * positiveQWeight (n + 1)) * (qSequence f (n + 1)) ^ 2 := by
      rw [mul_assoc, qSequence_weighted_square]
    _ = (positiveWeight (n + 1) + positiveWeight (n + 1) / ((n : ℝ) + 1)) *
        (qSequence f (n + 1)) ^ 2 := by
      rw [weight_identity]
      simp only [Nat.cast_add, Nat.cast_one]
    _ = _ := by rw [add_mul, div_mul_eq_mul_div, hp]

theorem reciprocal_energy_summable (g : ThresholdHilbert) :
    Summable (fun n : ℕ => (g n) ^ 2 / ((n : ℝ) + 1)) := by
  apply (hilbert_coordinate_mul_summable g (reciprocalD g)).congr
  intro n
  rw [reciprocalD_apply]
  ring

/-- Positive correction beyond the Pareto norm. -/
def metricCorrection (f : QHilbert) : ℝ :=
  inner ℝ (toPareto f) (reciprocalD (toPareto f))

theorem metricCorrection_nonneg (f : QHilbert) : 0 ≤ metricCorrection f :=
  reciprocalD_positive _

theorem metricCorrection_eq_tsum (f : QHilbert) :
    metricCorrection f = ∑' n : ℕ, (toPareto f n) ^ 2 / ((n : ℝ) + 1) :=
  reciprocalD_inner_tsum _

/-- No signed or positive term has been discarded in changing measures. -/
theorem norm_identity (f : QHilbert) :
    zetaTwo * ‖f‖ ^ 2 = ‖toPareto f‖ ^ 2 + metricCorrection f := by
  rw [qNorm_sq, ← tsum_mul_left, metricCorrection_eq_tsum, hilbert_norm_sq,
    ← (hilbert_coordinate_square_summable (toPareto f)).tsum_add
      (reciprocal_energy_summable (toPareto f))]
  exact tsum_congr (scaled_coordinate_sq f)


/-- The signed correction pairing; mixed terms need not be positive. -/
def metricPairing (f g : QHilbert) : ℝ :=
  inner ℝ (toPareto f) (reciprocalD (toPareto g))

theorem metricPairing_symmetric (f g : QHilbert) :
    metricPairing f g = metricPairing g f := by
  unfold metricPairing
  rw [← reciprocalD_symmetric, real_inner_comm]

theorem metricCorrection_add (f g : QHilbert) :
    metricCorrection (f + g) =
      metricCorrection f + metricCorrection g + 2 * metricPairing f g := by
  have he : toPareto (f + g) = toPareto f + toPareto g :=
    toParetoLinear.map_add f g
  have hs := metricPairing_symmetric f g
  unfold metricPairing at hs
  unfold metricCorrection metricPairing
  rw [he, map_add, inner_add_left, inner_add_right, inner_add_right]
  nlinarith only [hs]

/-- Every signed pairing, hence every Gram entry and signed energy budget,
has an exact transfer identity with its mixed correction retained. -/
theorem inner_identity (f g : QHilbert) :
    zetaTwo * inner ℝ f g =
      inner ℝ (toPareto f) (toPareto g) + metricPairing f g := by
  have h := norm_identity (f + g)
  have hf := norm_identity f
  have hg := norm_identity g
  have he : toPareto (f + g) = toPareto f + toPareto g :=
    toParetoLinear.map_add f g
  rw [norm_add_sq_real, he, norm_add_sq_real, metricCorrection_add] at h
  nlinarith only [h, hf, hg]

/-- Literal physical-coordinate formula for the complete correction. -/
theorem metricCorrection_eq_physical (f : QHilbert) :
    metricCorrection f = ∑' n : ℕ, (qSequence f (n + 1)) ^ 2 /
      (((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2)) := by
  rw [metricCorrection_eq_tsum]
  apply tsum_congr
  intro n
  rw [← hilbertSequence_weighted_square (toPareto f) n, toPareto_sequence,
    positiveWeight_succ]
  unfold paretoWeight
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp [h1, h2]

theorem metricCorrection_eq_zero_iff (f : QHilbert) :
    metricCorrection f = 0 ↔ f = 0 := by
  constructor
  · intro h
    have hh := reciprocalD_faithful (toPareto f) h
    apply paretoEquiv.injective
    simpa only [paretoEquiv_apply, map_zero] using hh
  · rintro rfl
    change inner ℝ (toParetoLinear 0) (reciprocalD (toParetoLinear 0)) = 0
    simp

/-- The reciprocal correction on a tail is controlled by its first multiplier. -/
theorem reciprocal_energy_le_of_head_zero (g : ThresholdHilbert) (H : ℕ)
    (hhead : ∀ n < H, g n = 0) :
    inner ℝ g (reciprocalD g) ≤ ‖g‖ ^ 2 / ((H : ℝ) + 1) := by
  rw [reciprocalD_inner_tsum, hilbert_norm_sq, ← tsum_div_const]
  apply Summable.tsum_le_tsum _ (reciprocal_energy_summable g)
    ((hilbert_coordinate_square_summable g).div_const _)
  intro n
  by_cases hn : n < H
  · simp [hhead n hn]
  · exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      (by exact_mod_cast Nat.add_le_add_right (Nat.le_of_not_gt hn) 1)

theorem toPareto_head_zero (f : QHilbert) (H : ℕ)
    (hhead : ∀ k, 0 < k → k ≤ H → qSequence f k = 0) :
    ∀ n < H, toPareto f n = 0 := by
  intro n hn
  change Real.sqrt (paretoWeight n) * qSequence f (n + 1) = 0
  rw [hhead (n + 1) (by omega) (by omega), mul_zero]

theorem metricCorrection_le_of_head_zero (f : QHilbert) (H : ℕ)
    (hhead : ∀ k, 0 < k → k ≤ H → qSequence f k = 0) :
    metricCorrection f ≤ ‖toPareto f‖ ^ 2 / ((H : ℝ) + 1) :=
  reciprocal_energy_le_of_head_zero _ _ (toPareto_head_zero f H hhead)

/-- The factor two is replaced by a factor tending to one on growing heads. -/
theorem norm_sq_le_of_head_zero (f : QHilbert) (H : ℕ)
    (hhead : ∀ k, 0 < k → k ≤ H → qSequence f k = 0) :
    zetaTwo * ‖f‖ ^ 2 ≤
      (1 + 1 / ((H : ℝ) + 1)) * ‖toPareto f‖ ^ 2 := by
  rw [norm_identity]
  have h := metricCorrection_le_of_head_zero f H hhead
  simp only [div_eq_mul_inv] at h ⊢
  nlinarith only [h]

/-- Bounded growing-head residuals have vanishing discrepancy between the
two scaled complete energies. This does not imply that either error vanishes. -/
theorem energy_discrepancy_tendsto_zero (f : ℕ → QHilbert)
    (hhead : ∀ H k, 0 < k → k ≤ H → qSequence (f H) k = 0)
    {C : ℝ} (hbounded : ∀ H, ‖toPareto (f H)‖ ^ 2 ≤ C) :
    Tendsto (fun H => zetaTwo * ‖f H‖ ^ 2 - ‖toPareto (f H)‖ ^ 2)
      atTop (𝓝 0) := by
  have hinv : Tendsto (fun H : ℕ => 1 / ((H : ℝ) + 1)) atTop (𝓝 0) := by
    have ht := tendsto_inv_atTop_zero.comp
      ((tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp (tendsto_add_atTop_nat 1))
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, one_div] using ht
  have hb : Tendsto (fun H : ℕ => C / ((H : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_one_div] using hinv.const_mul C
  apply squeeze_zero (fun H => ?_) (fun H => ?_) hb
  · rw [norm_identity]
    simpa only [add_sub_cancel_left] using metricCorrection_nonneg (f H)
  · rw [norm_identity]
    have ht := (metricCorrection_le_of_head_zero (f H) H (hhead H)).trans
      (div_le_div_of_nonneg_right (hbounded H) (by positivity))
    simpa only [add_sub_cancel_left] using ht

/-- Pointwise tail comparison with the exact head-dependent factor. -/
theorem QWeight_le_after (H k : ℕ) (hk : H < k) :
    positiveQWeight k ≤
      ((1 + 1 / ((H : ℝ) + 1)) / zetaTwo) * positiveWeight k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_le H).trans_lt hk
  have hHk : (H : ℝ) + 1 ≤ k := by exact_mod_cast hk
  have hr : 1 / (k : ℝ) ≤ 1 / ((H : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) hHk
  have h := mul_le_mul_of_nonneg_left hr (positiveWeight_nonneg k)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ zetaTwo_pos).mpr
  rw [mul_comm (positiveQWeight k), weight_identity]
  simp only [div_eq_mul_inv] at h ⊢
  nlinarith only [h]

/-- A sharper complete Q tail bound than the global comparison gives. -/
theorem tail_norm_sq_le_of_bounded (f : QHilbert) (H : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hf : ∀ n, 0 < n → |qSequence f n| ≤ A) :
    ‖hilbertTailShift f H‖ ^ 2 ≤
      ((1 + 1 / ((H : ℝ) + 1)) / zetaTwo) * A ^ 2 / ((H : ℝ) + 1) := by
  have hs : Summable (fun k : ℕ => positiveQWeight (k + H + 1) *
      qSequence f (k + H + 1) ^ 2) := by
    simpa only [Nat.add_assoc] using
      (summable_nat_add_iff (H + 1)).mpr (qSequence_square_summable f)
  have hw : Summable (fun k : ℕ => positiveWeight (k + H + 1)) := by
    simpa only [Nat.add_assoc] using
      (summable_nat_add_iff (H + 1)).mpr positiveWeight_summable
  calc
    ‖hilbertTailShift f H‖ ^ 2 =
        ∑' k : ℕ, positiveQWeight (k + H + 1) * qSequence f (k + H + 1) ^ 2 := by
      rw [hilbert_norm_sq]
      exact tsum_congr (fun k => (qSequence_weighted_square f (k + H)).symm)
    _ ≤ ∑' k : ℕ, positiveWeight (k + H + 1) *
        (((1 + 1 / ((H : ℝ) + 1)) / zetaTwo) * A ^ 2) := by
      apply Summable.tsum_le_tsum _ hs (hw.mul_right _)
      intro k
      have hsq : qSequence f (k + H + 1) ^ 2 ≤ A ^ 2 := by
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg _) hA).mpr (hf _ (by omega))
      exact (mul_le_mul_of_nonneg_left hsq (positiveQWeight_nonneg _)).trans
        ((mul_le_mul_of_nonneg_right (QWeight_le_after H _ (by omega))
          (sq_nonneg A)).trans_eq (by ring))
    _ = _ := by
      rw [tsum_mul_right]
      have ht : (∑' k : ℕ, positiveWeight (k + H + 1)) = 1 / ((H : ℝ) + 1) := by
        simpa only [Nat.add_assoc, Nat.cast_add, Nat.cast_one] using
          positiveWeight_tail_tsum (H + 1) (Nat.succ_pos _)
      rw [ht]
      ring

/-- Exact Gram comparison for any finite family, with every cross term retained. -/
theorem synthesis_norm_identity {ι : Type*} [Fintype ι]
    (v : ι → QHilbert) (c : ι → ℝ) :
    zetaTwo * ‖∑ i, c i • v i‖ ^ 2 =
      ‖∑ i, c i • toPareto (v i)‖ ^ 2 + metricCorrection (∑ i, c i • v i) := by
  have h := norm_identity (∑ i, c i • v i)
  have he : toPareto (∑ i, c i • v i) = ∑ i, c i • toPareto (v i) := by
    change toParetoLinear (∑ i, c i • v i) = _
    simp only [map_sum, map_smul]
    rfl
  rwa [he] at h

end RiemannResearch.RH.QParetoMetric
