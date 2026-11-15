/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QHyperplaneFiniteRepairs
import RiemannResearch.RH.NearbyDilationGram
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Actual Q tail masses along the quadratic finite-support schedule

Source: the reciprocal-head investigation, 7 November 2026, Section 7.
The mass comparison is proved from the actual complete Q and Pareto weights.
No tail regularity or asymptotic hypothesis is introduced.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QHyperplaneCountermodel
open ZetaTwoHilbert ZetaTwoProbability Pareto QFiniteSupportDualCriterion

theorem qOne_coordinate_sq (n : ℕ) : (qOne n) ^ 2 = qWeight n := by
  have h := qSequence_weighted_square qOne n
  rw [qSequence_qOne] at h
  simpa [qOneSequence, qWeight] using h.symm

theorem residualTail_mass (N : ℕ) :
    ‖residualTail N‖ ^ 2 = ∑' k : ℕ, positiveQWeight (k + (N + 1)) := by
  have hsum := (qCoordinate_square_summable qOne).sum_add_tsum_nat_add N
  have hhead : ‖finiteHead N qOne‖ ^ 2 =
      ∑ n ∈ Finset.range N, (qOne n) ^ 2 := by
    have hi := finiteHead_inner N qOne (finiteHead N qOne)
    rw [finiteHead_idem, real_inner_self_eq_norm_sq] at hi
    rw [hi, inner_finiteHead_eq_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have hsplit := finiteHead_norm_sq_split N qOne
  rw [hhead, qNorm_sq qOne] at hsplit
  have ht : ‖residualTail N‖ ^ 2 = ∑' k : ℕ, (qOne (k + N)) ^ 2 := by
    change ‖qOne - finiteHead N qOne‖ ^ 2 = _
    linarith
  rw [ht]
  apply tsum_congr
  intro k
  rw [qOne_coordinate_sq]
  simp only [qWeight, Nat.add_assoc]

/-- The actual normalized Q and Pareto point masses are uniformly equivalent. -/
theorem qWeight_pareto_comparison (m : ℕ) (_hm : 0 < m) :
    (1 / zetaTwo) * positiveWeight m ≤ positiveQWeight m ∧
      positiveQWeight m ≤ (2 / zetaTwo) * positiveWeight m := by
  constructor
  · have h : positiveWeight m / zetaTwo ≤ positiveQWeight m := by
      apply (div_le_iff₀ zetaTwo_pos).mpr
      simpa only [mul_comm] using
        ZetaTwoParetoTransfer.paretoWeight_le_zetaTwo_mul_QWeight m
    simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using h
  · have h : positiveQWeight m ≤ (2 * positiveWeight m) / zetaTwo := by
      apply (le_div_iff₀ zetaTwo_pos).mpr
      simpa only [mul_comm] using
        ZetaTwoParetoTransfer.zetaTwo_mul_QWeight_le_two_mul_paretoWeight m
    simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

theorem residualTail_mass_lower (N : ℕ) :
    (1 / zetaTwo) / ((N : ℝ) + 1) ≤ ‖residualTail N‖ ^ 2 := by
  have hsP : Summable (fun k : ℕ => positiveWeight (k + (N + 1))) :=
    (summable_nat_add_iff (N + 1)).mpr positiveWeight_summable
  have hsQ : Summable (fun k : ℕ => positiveQWeight (k + (N + 1))) :=
    (summable_nat_add_iff (N + 1)).mpr positiveQWeight_summable
  have h := Summable.tsum_le_tsum
    (fun k => (qWeight_pareto_comparison (k + (N + 1)) (by omega)).1)
    (hsP.mul_left (1 / zetaTwo)) hsQ
  rw [tsum_mul_left, positiveWeight_tail_tsum (N + 1) (by omega), ← residualTail_mass] at h
  simpa only [Nat.cast_add, Nat.cast_one, mul_one_div] using h

theorem residualTail_mass_upper (N : ℕ) :
    ‖residualTail N‖ ^ 2 ≤ (2 / zetaTwo) / ((N : ℝ) + 1) := by
  have hsP : Summable (fun k : ℕ => positiveWeight (k + (N + 1))) :=
    (summable_nat_add_iff (N + 1)).mpr positiveWeight_summable
  have hsQ : Summable (fun k : ℕ => positiveQWeight (k + (N + 1))) :=
    (summable_nat_add_iff (N + 1)).mpr positiveQWeight_summable
  have h := Summable.tsum_le_tsum
    (fun k => (qWeight_pareto_comparison (k + (N + 1)) (by omega)).2)
    hsQ (hsP.mul_left (2 / zetaTwo))
  rw [tsum_mul_left, positiveWeight_tail_tsum (N + 1) (by omega), ← residualTail_mass] at h
  simpa only [Nat.cast_add, Nat.cast_one, mul_one_div] using h

/-- A quantitative ratio bound sufficient for the explicit M=N² schedule. -/
theorem quadratic_tail_mass_ratio_bound (N : ℕ) :
    ‖residualTail (N ^ 2)‖ ^ 2 / ‖residualTail N‖ ^ 2 ≤ 4 / ((N : ℝ) + 1) := by
  have hN : 0 < (N : ℝ) + 1 := by positivity
  have hN2 : 0 < (N : ℝ) ^ 2 + 1 := by positivity
  have hZ := zetaTwo_pos
  have hlo := residualTail_mass_lower N
  have hup := residualTail_mass_upper (N ^ 2)
  simp only [Nat.cast_pow] at hup
  apply (div_le_iff₀ (residualTail_norm_sq_pos N)).mpr
  calc
    _ ≤ (2 / zetaTwo) / ((N : ℝ) ^ 2 + 1) := hup
    _ ≤ (4 / ((N : ℝ) + 1)) * ((1 / zetaTwo) / ((N : ℝ) + 1)) := by
      have he : (4 / ((N : ℝ) + 1)) * ((1 / zetaTwo) / ((N : ℝ) + 1)) =
          (4 / zetaTwo) / ((N : ℝ) + 1) ^ 2 := by
        field_simp [ne_of_gt hN, ne_of_gt hZ]
        <;> ring
      rw [he]
      apply (div_le_div_iff₀ hN2 (sq_pos_of_pos hN)).mpr
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right
        (by nlinarith [sq_nonneg ((N : ℝ) - 1)]) hZ.le
    _ ≤ (4 / ((N : ℝ) + 1)) * ‖residualTail N‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hlo (by positivity)

theorem quadratic_tail_mass_ratio_tendsto :
    Tendsto (fun N : ℕ => ‖residualTail (N ^ 2)‖ ^ 2 / ‖residualTail N‖ ^ 2)
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun N : ℕ => (4 : ℝ) / ((N : ℝ) + 1)) atTop (𝓝 0) := by
    have hshift : Tendsto (fun N : ℕ => N + 1) atTop atTop := by
      apply tendsto_atTop.mpr
      intro b
      filter_upwards [eventually_ge_atTop b] with N hN
      omega
    have h := (tendsto_const_div_atTop_nhds_zero_nat (4 : ℝ)).comp
      hshift
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using h
  exact squeeze_zero (fun N => div_nonneg (sq_nonneg _) (sq_nonneg _))
    quadratic_tail_mass_ratio_bound hlim

theorem blockTail_mass (N M : ℕ) (hNM : N ≤ M) :
    ‖blockTail N M‖ ^ 2 = ‖residualTail N‖ ^ 2 - ‖residualTail M‖ ^ 2 := by
  have hN := residualTail_mean N
  have hM := residualTail_mean M
  unfold residualTail at hN hM
  rw [inner_sub_right, real_inner_self_eq_norm_sq, qOne_norm_sq] at hN hM
  rw [← blockTail_mean N M hNM]
  unfold blockTail residualTail
  rw [inner_sub_right]
  linarith

/-- The finite block includes asymptotically all of the complete residual tail. -/
theorem quadratic_block_mass_ratio_tendsto :
    Tendsto (fun N : ℕ => ‖blockTail N (N ^ 2)‖ ^ 2 / ‖residualTail N‖ ^ 2)
      atTop (𝓝 1) := by
  have hlim := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
    quadratic_tail_mass_ratio_tendsto
  simp only [sub_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNM : N ≤ N ^ 2 := by nlinarith
  rw [blockTail_mass N (N ^ 2) hNM, sub_div,
    div_self (ne_of_gt (residualTail_norm_sq_pos N))]

end RiemannResearch.RH.QHyperplaneCountermodel
