/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ReciprocalChargeDyadicAverages
import RiemannResearch.RH.ReciprocalChargeInnovations

/-!
# Geometric charge certificates for full innovations

Source: the user-provided lateral-arithmetic handoff, using its proved
signed dyadic charge correlations and charge/step biorthogonality.
The weighted certificate has coefficients 1, 1/2, ..., 1/2^L and pairs
exactly to one with the full innovation. Its energy tends to
(12 + 3/4^L)/pi^2. Consequently every number below pi^2/12 is eventually
a lower bound for the full innovation energy.

This controls the full-space innovation, not the screened denominator in
the capacity gain. No source divergence or unconditional RH is asserted.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.RH.Pareto

private theorem geometric_nat_mul_tendsto (a : ℕ) (ha : 0 < a) :
    Tendsto (fun N : ℕ => a * N) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop b] with N hN
  nlinarith

private theorem geometric_nat_succ_tendsto :
    Tendsto (fun M : ℕ => M + 1) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop b] with M hM
  omega

def geometricDyadicCharge (L N : ℕ) : ThresholdHilbert :=
  ∑ i ∈ Finset.range (L + 1), (1 / 2 : ℝ) ^ i •
    reciprocalChargeRiesz (2 ^ i * N)

theorem geometricDyadicCharge_succ (L N : ℕ) :
    geometricDyadicCharge (L + 1) N = geometricDyadicCharge L N +
      (1 / 2 : ℝ) ^ (L + 1) • reciprocalChargeRiesz (2 ^ (L + 1) * N) := by
  exact Finset.sum_range_succ _ _

theorem geometricDyadicCharge_next_inner_tendsto (L : ℕ) :
    Tendsto (fun N => inner ℝ (geometricDyadicCharge L N)
      (reciprocalChargeRiesz (2 ^ (L + 1) * N))) atTop
      (𝓝 ((1 / 2 : ℝ) ^ L * (-6 / Real.pi ^ 2))) := by
  have ht := tendsto_finsetSum (Finset.range (L + 1))
    (f := fun i N => (1 / 2 : ℝ) ^ i *
      inner ℝ (reciprocalChargeRiesz (2 ^ i * N))
        (reciprocalChargeRiesz (2 ^ (L + 1) * N)))
    (a := fun i => if i = L then (1 / 2 : ℝ) ^ i * (-6 / Real.pi ^ 2) else 0)
    (by
      intro i hi
      by_cases h : i = L
      · subst i
        simpa using (reciprocalChargeRiesz_dyadic_neighbor_inner_tendsto L).const_mul
          ((1 / 2 : ℝ) ^ L)
      · simp only [if_neg h]
        simpa using (reciprocalChargeRiesz_dyadic_far_inner_tendsto i (L + 1)
          (by have hi' := Finset.mem_range.mp hi; omega)).const_mul ((1 / 2 : ℝ) ^ i))
  simpa [geometricDyadicCharge, sum_inner, inner_smul_left] using ht

/-- The negative adjacent correlations are retained exactly. -/
theorem geometricDyadicCharge_norm_sq_tendsto (L : ℕ) :
    Tendsto (fun N => ‖geometricDyadicCharge L N‖ ^ 2) atTop
      (𝓝 ((12 + 3 * (1 / 4 : ℝ) ^ L) / Real.pi ^ 2)) := by
  induction L with
  | zero => simpa [geometricDyadicCharge, show (12 : ℝ) + 3 = 15 by norm_num] using reciprocalChargeRiesz_norm_sq_tendsto
  | succ L ih =>
    have hnext := (reciprocalChargeRiesz_norm_sq_tendsto.comp
      (geometric_nat_mul_tendsto (2 ^ (L + 1)) (by positivity))).const_mul
        (((1 / 2 : ℝ) ^ (L + 1)) ^ 2)
    have hcross := ((geometricDyadicCharge_next_inner_tendsto L).const_mul
      ((1 / 2 : ℝ) ^ (L + 1))).const_mul 2
    have ht := (ih.add hnext).add hcross
    have hw : ((1 / 2 : ℝ) ^ L) ^ 2 = (1 / 4 : ℝ) ^ L := by
      rw [← pow_mul, Nat.mul_comm L 2, pow_mul]
      norm_num
    have he : (12 + 3 * (1 / 4 : ℝ) ^ L) / Real.pi ^ 2 +
        ((1 / 2 : ℝ) ^ (L + 1)) ^ 2 * (15 / Real.pi ^ 2) +
        2 * ((1 / 2 : ℝ) ^ (L + 1) *
          ((1 / 2 : ℝ) ^ L * (-6 / Real.pi ^ 2))) =
        (12 + 3 * (1 / 4 : ℝ) ^ (L + 1)) / Real.pi ^ 2 := by
      rw [pow_succ (1 / 2 : ℝ) L, pow_succ (1 / 4 : ℝ) L]
      rw [← hw]
      ring
    rw [he] at ht
    simpa only [geometricDyadicCharge_succ, norm_add_sq_real, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs, inner_smul_right,
      Function.comp_def, add_right_comm] using ht

theorem geometricDyadicCharge_limit_energy_tendsto :
    Tendsto (fun L : ℕ => (12 + 3 * (1 / 4 : ℝ) ^ L) / Real.pi ^ 2)
      atTop (𝓝 (12 / Real.pi ^ 2)) := by
  have hg : Tendsto (fun L : ℕ => (1 / 4 : ℝ) ^ L) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)
  simpa using ((hg.const_mul 3).const_add 12).div_const (Real.pi ^ 2)

namespace CoefficientStabilization

private theorem geometric_cutoff_ge (i M : ℕ) : M + 1 ≤ 2 ^ i * (M + 1) := by
  have hp : 0 < 2 ^ i := by positivity
  nlinarith

theorem geometricDyadicCharge_mem_finiteSpace_orthogonal (L M : ℕ) :
    geometricDyadicCharge L (M + 1) ∈ (finiteSpace M)ᗮ := by
  unfold geometricDyadicCharge
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  exact reciprocalChargeRiesz_mem_finiteSpace_orthogonal
    (2 ^ i * (M + 1)) M (geometric_cutoff_ge i M)

theorem geometricDyadicCharge_inner_consecutive (L M : ℕ) (hM : 1 ≤ M) :
    inner ℝ (geometricDyadicCharge L (M + 1)) (consecutiveResidueHilbert M) = 1 := by
  rw [geometricDyadicCharge, sum_inner]
  have hterm (i : ℕ) :
      inner ℝ ((1 / 2 : ℝ) ^ i • reciprocalChargeRiesz (2 ^ i * (M + 1)))
        (consecutiveResidueHilbert M) = if i = 0 then 1 else 0 := by
    rw [inner_smul_left, reciprocalChargeRiesz_consecutive_biorthogonal
      (2 ^ i * (M + 1)) M (by positivity) hM]
    cases i with
    | zero => simp
    | succ i =>
      have hp : 0 < 2 ^ i := by positivity
      have hn : 2 ^ (i + 1) * (M + 1) ≠ M + 1 := by
        rw [pow_succ]
        nlinarith
      simp [hn]
  simp_rw [hterm]
  simp

/-- Exact unit-signal dual certificate for the full projection innovation. -/
theorem geometricDyadicCharge_full_innovation_product_lower
    (L M : ℕ) (hM : 1 ≤ M) :
    1 ≤ ‖geometricDyadicCharge L (M + 1)‖ ^ 2 *
      ‖consecutiveResidueHilbert M -
        (finiteSpace M).starProjection (consecutiveResidueHilbert M)‖ ^ 2 := by
  let z := consecutiveResidueHilbert M -
    (finiteSpace M).starProjection (consecutiveResidueHilbert M)
  have ho : inner ℝ (geometricDyadicCharge L (M + 1))
      ((finiteSpace M).starProjection (consecutiveResidueHilbert M)) = 0 := by
    rw [real_inner_comm]
    exact ((finiteSpace M).mem_orthogonal _).mp
      (geometricDyadicCharge_mem_finiteSpace_orthogonal L M) _
      ((finiteSpace M).starProjection_apply_mem _)
  have he : inner ℝ (geometricDyadicCharge L (M + 1)) z = 1 := by
    dsimp [z]
    rw [inner_sub_right, geometricDyadicCharge_inner_consecutive L M hM, ho, sub_zero]
  have hc := real_inner_mul_inner_self_le (geometricDyadicCharge L (M + 1)) z
  rw [he, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hc
  simpa [z] using hc

/-- A full-space lower bound; it does not estimate the capacity's screened denominator.
The auxiliary dyadic length is fixed before the physical cutoff tends to infinity. -/
theorem consecutiveResidue_full_innovation_eventually_gt
    (c : ℝ) (hc : c < Real.pi ^ 2 / 12) :
    ∀ᶠ M : ℕ in atTop, c < ‖consecutiveResidueHilbert M -
      (finiteSpace M).starProjection (consecutiveResidueHilbert M)‖ ^ 2 := by
  by_cases hc0 : c ≤ 0
  · filter_upwards [eventually_ge_atTop 1] with M hM
    have hs := consecutiveResidue_full_innovation_energy_lower M hM
    nlinarith
  have hcpos : 0 < c := lt_of_not_ge hc0
  have hp : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hd : 12 / Real.pi ^ 2 < 1 / c := by
    apply (div_lt_div_iff₀ hp hcpos).2
    have hc' := (lt_div_iff₀ (show (0 : ℝ) < 12 by norm_num)).mp hc
    nlinarith
  obtain ⟨L, hL⟩ := ((tendsto_order.1
    geometricDyadicCharge_limit_energy_tendsto).2 (1 / c) hd).exists
  have hnorm := (geometricDyadicCharge_norm_sq_tendsto L).comp
    geometric_nat_succ_tendsto
  have hsmall := (tendsto_order.1 hnorm).2 (1 / c) hL
  filter_upwards [hsmall, eventually_ge_atTop 1] with M hA hM
  have hprod := geometricDyadicCharge_full_innovation_product_lower L M hM
  have hAc : ‖geometricDyadicCharge L (M + 1)‖ ^ 2 * c < 1 :=
    (lt_div_iff₀ hcpos).mp hA
  by_contra h
  have hsc := le_of_not_gt h
  have hm := mul_le_mul_of_nonneg_left hsc (sq_nonneg ‖geometricDyadicCharge L (M + 1)‖)
  nlinarith

end CoefficientStabilization
end RiemannResearch.RH.Pareto
