/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ReciprocalChargeDilationCorrelation

/-!
# Explicit geometric cancellation of actual reciprocal charges

Source: the exact signed dilation correlations already proved in
ReciprocalChargeDilationCorrelation, combined in the directed continuation
of 24 September 2026. No external arithmetic assumption or novelty claim
is used. Square factors annihilate the Mobius dilation correlation.

On powers of two, the limiting Gram matrix has diagonal 15/pi^2,
nearest-neighbor entries -6/pi^2, and all more distant entries zero.
The mean of L+1 successive vectors therefore has limiting squared norm
(3L+15)/(pi^2 (L+1)^2). The limits are taken first in the common cutoff N,
then in L; no uniform diagonal rate is asserted.

These are dual charge vectors. Their small norm is not a legal approximation
to the RH target. See ReciprocalChargeInnovations for their exact
orthogonality to each finite legal space.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto

private theorem tendsto_nat_mul_left_pos (a : ℕ) (ha : 0 < a) :
    Tendsto (fun N : ℕ => a * N) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop b] with N hN
  nlinarith

theorem reciprocalChargeRiesz_four_dvd_dilation_inner_tendsto
    (h : ℕ) (hh : 0 < h) (h4 : 4 ∣ h) :
    Tendsto (fun N => inner ℝ (reciprocalChargeRiesz N)
      (reciprocalChargeRiesz (h * N))) atTop (𝓝 0) := by
  have hz (d : ℕ) : mobiusDilationCorrelation h d = 0 := by
    have hmu : ArithmeticFunction.moebius (h * d) = 0 := by
      apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
      intro hs
      have hu := hs 2 (h4.trans (dvd_mul_right h d))
      norm_num at hu
    simp [mobiusDilationCorrelation, hmu]
  simpa only [hz, tsum_zero, mul_zero] using
    reciprocalChargeRiesz_dilation_inner_tendsto h hh

theorem reciprocalChargeRiesz_dyadic_far_inner_tendsto
    (i j : ℕ) (hij : i + 2 ≤ j) :
    Tendsto (fun N => inner ℝ (reciprocalChargeRiesz (2 ^ i * N))
      (reciprocalChargeRiesz (2 ^ j * N))) atTop (𝓝 0) := by
  have h4 : 4 ∣ 2 ^ (j - i) := by
    exact pow_dvd_pow 2 (show 2 ≤ j - i by omega)
  have ht := (reciprocalChargeRiesz_four_dvd_dilation_inner_tendsto
    (2 ^ (j - i)) (by positivity) h4).comp
      (tendsto_nat_mul_left_pos (2 ^ i) (by positivity))
  have he (N : ℕ) : 2 ^ (j - i) * (2 ^ i * N) = 2 ^ j * N := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (by omega : i ≤ j)]
  simpa only [Function.comp_def, he] using ht

theorem reciprocalChargeRiesz_dyadic_neighbor_inner_tendsto (i : ℕ) :
    Tendsto (fun N => inner ℝ (reciprocalChargeRiesz (2 ^ i * N))
      (reciprocalChargeRiesz (2 ^ (i + 1) * N))) atTop (𝓝 (-6 / Real.pi ^ 2)) := by
  have ht := reciprocalChargeRiesz_two_dilation_inner_tendsto.comp
    (tendsto_nat_mul_left_pos (2 ^ i) (by positivity))
  have he (N : ℕ) : 2 * (2 ^ i * N) = 2 ^ (i + 1) * N := by
    rw [pow_succ]
    ring
  simpa only [Function.comp_def, he] using ht

def dyadicReciprocalChargeSum (L N : ℕ) : ThresholdHilbert :=
  ∑ i ∈ Finset.range (L + 1), reciprocalChargeRiesz (2 ^ i * N)

theorem dyadicReciprocalChargeSum_succ (L N : ℕ) :
    dyadicReciprocalChargeSum (L + 1) N =
      dyadicReciprocalChargeSum L N + reciprocalChargeRiesz (2 ^ (L + 1) * N) := by
  exact Finset.sum_range_succ _ _

theorem dyadicReciprocalChargeSum_next_inner_tendsto (L : ℕ) :
    Tendsto (fun N => inner ℝ (dyadicReciprocalChargeSum L N)
      (reciprocalChargeRiesz (2 ^ (L + 1) * N))) atTop (𝓝 (-6 / Real.pi ^ 2)) := by
  have ht := tendsto_finsetSum (Finset.range (L + 1))
    (f := fun i N => inner ℝ (reciprocalChargeRiesz (2 ^ i * N))
      (reciprocalChargeRiesz (2 ^ (L + 1) * N)))
    (a := fun i => if i = L then -6 / Real.pi ^ 2 else 0) (by
      intro i hi
      by_cases h : i = L
      · subst i
        simpa using reciprocalChargeRiesz_dyadic_neighbor_inner_tendsto L
      · simp only [if_neg h]
        exact reciprocalChargeRiesz_dyadic_far_inner_tendsto i (L + 1)
          (by have hi' := Finset.mem_range.mp hi; omega))
  simpa [dyadicReciprocalChargeSum, sum_inner] using ht

/-- Exact energy limit retaining the negative nearest-neighbor correlations. -/
theorem dyadicReciprocalChargeSum_norm_sq_tendsto (L : ℕ) :
    Tendsto (fun N => ‖dyadicReciprocalChargeSum L N‖ ^ 2)
      atTop (𝓝 ((3 * (L : ℝ) + 15) / Real.pi ^ 2)) := by
  induction L with
  | zero => simpa [dyadicReciprocalChargeSum] using reciprocalChargeRiesz_norm_sq_tendsto
  | succ L ih =>
    have hnext := reciprocalChargeRiesz_norm_sq_tendsto.comp
      (tendsto_nat_mul_left_pos (2 ^ (L + 1)) (by positivity))
    have ht := (ih.add hnext).add ((dyadicReciprocalChargeSum_next_inner_tendsto L).const_mul 2)
    have he : (3 * (L : ℝ) + 15) / Real.pi ^ 2 + 15 / Real.pi ^ 2 +
        2 * (-6 / Real.pi ^ 2) = (3 * ((L + 1 : ℕ) : ℝ) + 15) / Real.pi ^ 2 := by
      push_cast
      ring
    rw [he] at ht
    simpa only [dyadicReciprocalChargeSum_succ, norm_add_sq_real, Function.comp_def,
      add_right_comm] using ht

def dyadicReciprocalChargeAverage (L N : ℕ) : ThresholdHilbert :=
  ((L : ℝ) + 1)⁻¹ • dyadicReciprocalChargeSum L N

theorem dyadicReciprocalChargeAverage_norm_sq_tendsto (L : ℕ) :
    Tendsto (fun N => ‖dyadicReciprocalChargeAverage L N‖ ^ 2)
      atTop (𝓝 ((3 * (L : ℝ) + 15) / (Real.pi ^ 2 * ((L : ℝ) + 1)^2))) := by
  have ht := (dyadicReciprocalChargeSum_norm_sq_tendsto L).const_mul
    (((L : ℝ) + 1)⁻¹ ^ 2)
  have he : ((L : ℝ) + 1)⁻¹ ^ 2 * ((3 * (L : ℝ) + 15) / Real.pi ^ 2) =
      (3 * (L : ℝ) + 15) / (Real.pi ^ 2 * ((L : ℝ) + 1)^2) := by
    field_simp
  rw [he] at ht
  simpa only [dyadicReciprocalChargeAverage, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs] using ht

theorem dyadicReciprocalChargeAverage_limit_energy_tendsto_zero :
    Tendsto (fun L : ℕ =>
      (3 * (L : ℝ) + 15) / (Real.pi ^ 2 * ((L : ℝ) + 1)^2)) atTop (𝓝 0) := by
  have hi : Tendsto (fun L : ℕ => ((L : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    apply tendsto_inv_atTop_zero.comp
    apply tendsto_atTop.2
    intro b
    have hn : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    filter_upwards [(tendsto_atTop.1 hn) b] with L hL
    linarith
  have ht := ((hi.const_mul 3).add ((hi.pow 2).const_mul 12)).div_const (Real.pi ^ 2)
  have he (L : ℕ) : (3 * ((L : ℝ) + 1)⁻¹ + 12 * (((L : ℝ) + 1)⁻¹)^2) /
      Real.pi ^ 2 = (3 * (L : ℝ) + 15) / (Real.pi ^ 2 * ((L : ℝ) + 1)^2) := by
    have hL : (L : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  simpa only [he, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero, zero_div] using ht

/-- A fixed sufficiently long geometric average has arbitrarily small eventual energy.
The two cutoffs are not interchanged and no uniform rate is asserted. -/
theorem dyadicReciprocalChargeAverage_eventually_small (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℕ, ∀ᶠ N : ℕ in atTop, ‖dyadicReciprocalChargeAverage L N‖ ^ 2 < ε := by
  have h := (tendsto_order.1 dyadicReciprocalChargeAverage_limit_energy_tendsto_zero).2 ε hε
  obtain ⟨L, hL⟩ := h.exists
  exact ⟨L, (tendsto_order.1 (dyadicReciprocalChargeAverage_norm_sq_tendsto L)).2 ε hL⟩


end RiemannResearch.RH.Pareto
