/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QTriangularCharge
import RiemannResearch.RH.ThresholdHilbertMean
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact native-Q triangular Riesz energy

Source: the ordinary argument in BalazardTriangularResearch20261019.md,
extending the dual system of Michel Balazard, arXiv:1812.04309,
Propositions 6--7. The concrete overlap and Pareto energy proofs are reused.
The repository's Pareto triangular vector is minus the paper's S_N.
Accordingly riesz below is minus the paper's D_N; it represents charge
with a positive sign. Norms and both exact nonnegative remainders agree.
No closure or RH assumption is used.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QTriangularCharge
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer

def rieszSequence (N k : ℕ) : ℝ :=
  zetaTwo * (k : ℝ) / ((k : ℝ) + 1) *
    hilbertSequence (triangularChargeRiesz N) k

theorem rieszSequence_zero_of_le (N k : ℕ) (h : N ≤ k) :
    rieszSequence N k = 0 := by
  simp [rieszSequence, triangularChargeRiesz_sequence_zero_of_le N k h]

private theorem rieszSequence_summable (N : ℕ) :
    Summable (fun k => positiveQWeight k * rieszSequence N k ^ 2) := by
  apply summable_of_ne_finset_zero (s := Finset.range N)
  intro k hk
  rw [rieszSequence_zero_of_le N k (by simpa using hk)]
  simp

/-- The actual native-Q Riesz vector of the triangular charge. -/
def riesz (N : ℕ) : QHilbert :=
  encodeQ (rieszSequence N) (rieszSequence_summable N)

@[simp] theorem riesz_sequence (N : ℕ) :
    qSequence (riesz N) = rieszSequence N :=
  qSequence_encodeQ _ _ (by simp [rieszSequence])

/-- Correct change of metric, coordinate by coordinate, including the anchor. -/
theorem riesz_weighted_coordinate (N k : ℕ) :
    positiveQWeight k * rieszSequence N k =
      positiveWeight k * hilbertSequence (triangularChargeRiesz N) k := by
  by_cases hk : k = 0
  · subst k
    simp [rieszSequence, positiveQWeight, positiveWeight]
  · have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    unfold rieszSequence positiveQWeight positiveWeight
    field_simp [ne_of_gt zetaTwo_pos, hkR]

theorem riesz_inner (N : ℕ) (h : QHilbert) :
    inner ℝ (riesz N) h = charge N h := by
  rw [qInner_weighted, riesz_sequence, charge, hilbert_inner_weighted]
  unfold paretoInner
  rw [toPareto_sequence]
  apply tsum_congr
  intro k
  rw [riesz_weighted_coordinate]
  ring

/-- Exact finite metric-change remainder W_N, with physical cutoff retained. -/
def metricRemainder (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N,
    hilbertSequence (triangularChargeRiesz N) k ^ 2 /
      ((k : ℝ) * ((k : ℝ) + 1) ^ 2)

theorem metricRemainder_nonneg (N : ℕ) : 0 ≤ metricRemainder N := by
  apply Finset.sum_nonneg
  intro k hk
  positivity

/-- Complete native-Q energy, with no tail truncation assumption. -/
theorem riesz_norm_sq (N : ℕ) :
    ‖riesz N‖ ^ 2 =
      zetaTwo * ∑ k ∈ Finset.range N,
        hilbertSequence (triangularChargeRiesz N) k ^ 2 / ((k : ℝ) + 1) ^ 2 := by
  rw [qNorm_weighted_sq, riesz_sequence]
  rw [tsum_eq_sum (s := Finset.range N) (by
    intro k hk
    rw [rieszSequence_zero_of_le N k (by simpa using hk)]
    simp)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    simp [rieszSequence, positiveQWeight]
  · have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
    unfold positiveQWeight rieszSequence
    field_simp [ne_of_gt zetaTwo_pos, hkR]

/-- Exact metric decomposition before any term is discarded. -/
theorem riesz_metric_identity (N : ℕ) :
    ‖riesz N‖ ^ 2 + zetaTwo * metricRemainder N =
      zetaTwo * ‖triangularChargeRiesz N‖ ^ 2 := by
  rw [riesz_norm_sq, hilbert_norm_weighted_sq]
  rw [tsum_eq_sum (s := Finset.range N) (by
    intro k hk
    rw [triangularChargeRiesz_sequence_zero_of_le N k (by simpa using hk)]
    simp)]
  unfold metricRemainder
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    simp [positiveWeight]
  · have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
    unfold positiveWeight
    field_simp [hkR]

/-- The full Balazard triangular identity in the actual Q geometry.
Here N=n+1; the variance uses exactly the existing reciprocal overlap. -/
theorem riesz_energy_identity (n : ℕ) :
    zetaTwo * reciprocalMobiusCesaroEnergy (n + 1) =
      ‖riesz (n + 1)‖ ^ 2 + zetaTwo * triangularChargeVariance n +
        zetaTwo * metricRemainder (n + 1) := by
  rw [triangularChargeRiesz_energy_identity]
  have hm := riesz_metric_identity (n + 1)
  nlinarith

theorem riesz_norm_sq_le (N : ℕ) :
    ‖riesz N‖ ^ 2 ≤ zetaTwo * reciprocalMobiusCesaroEnergy N := by
  have hm := riesz_metric_identity N
  have hw := metricRemainder_nonneg N
  have he := mul_le_mul_of_nonneg_left (triangularChargeRiesz_norm_sq_le N)
    zetaTwo_pos.le
  nlinarith [mul_nonneg zetaTwo_pos.le hw]

theorem riesz_tendsto_zero :
    Tendsto riesz atTop (𝓝 (0 : QHilbert)) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply RiemannResearch.Analysis.BoundedSquareEnergy.tendsto_zero_of_square_le
    (fun N => ‖riesz N‖)
    (fun N => zetaTwo * reciprocalMobiusCesaroEnergy N)
  · simpa using reciprocalMobiusCesaroEnergy_tendsto_zero.const_mul zetaTwo
  · exact riesz_norm_sq_le

/-- Sharper moving-test bound retaining both nonnegative remainders. -/
theorem charge_sq_le_exact (n : ℕ) (h : QHilbert) :
    charge (n + 1) h ^ 2 ≤
      (zetaTwo * reciprocalMobiusCesaroEnergy (n + 1) -
        zetaTwo * triangularChargeVariance n -
        zetaTwo * metricRemainder (n + 1)) * ‖h‖ ^ 2 := by
  have hc := real_inner_mul_inner_self_le (riesz (n + 1)) h
  rw [riesz_inner, ← pow_two, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq] at hc
  have he := riesz_energy_identity n
  have hh : zetaTwo * reciprocalMobiusCesaroEnergy (n + 1) -
      zetaTwo * triangularChargeVariance n -
      zetaTwo * metricRemainder (n + 1) = ‖riesz (n + 1)‖ ^ 2 := by linarith
  rw [hh]
  exact hc

end RiemannResearch.RH.QTriangularCharge
