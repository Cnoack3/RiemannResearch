/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.GeometricGramInnovations
import RiemannResearch.RH.ResidualDilationPartialSums
import RiemannResearch.RH.ThresholdHilbertProjection

/-!
# Actual residual geometric correlation summability

Source: direct continuation of the supplied signed-masses and argument audit,
24 September 2026. No mathematical novelty is claimed.
The integer dilation semigroup and adjoint mean identity discharge every
Gram hypothesis. Both infinite nonnegative series are explicitly summable.
The estimates do not establish ordinary sublinear primitive growth or RH.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis

theorem hilbertDilation_one_inner_one_exact (m : ℕ) (hm : 0 < m) :
    inner ℝ hilbertOne (hilbertDilation m hm hilbertOne) = 1 := by
  have h := ContinuousLinearMap.adjoint_inner_right
    (hilbertDilationContinuous m hm) hilbertOne hilbertOne
  change inner ℝ hilbertOne (hilbertDilationAdjoint m hm hilbertOne) =
    inner ℝ (hilbertDilation m hm hilbertOne) hilbertOne at h
  rw [hilbertDilationAdjoint_one, real_inner_self_eq_norm_sq,
    hilbertOne_norm_sq] at h
  rw [real_inner_comm]
  exact h.symm

def quaternaryTail (j : ℕ) : ThresholdHilbert :=
  ((1 / 2 : ℝ) ^ j) • hilbertDilation (4 ^ j) (by positivity) hilbertOne

theorem quaternaryTail_gram (i j : ℕ) (hij : i ≤ j) :
    inner ℝ (quaternaryTail i) (quaternaryTail j) = (1 / 2 : ℝ) ^ (j - i) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  have hcancel : (1 / 2 : ℝ) ^ i * (1 / 2 : ℝ) ^ i * (4 : ℝ) ^ i = 1 := by
    calc
      _ = ((1 / 2 : ℝ) * (1 / 2) * 4) ^ i := by simp only [mul_pow]
      _ = 1 := by norm_num
  unfold quaternaryTail
  rw [real_inner_smul_left, real_inner_smul_right]
  have hd : hilbertDilation (4 ^ (i + k)) (by positivity) hilbertOne =
      hilbertDilation (4 ^ i) (by positivity)
        (hilbertDilation (4 ^ k) (by positivity) hilbertOne) := by
    simpa only [pow_add] using
      (hilbertDilation_comp (4 ^ i) (4 ^ k) (by positivity) (by positivity) hilbertOne).symm
  rw [hd,
    hilbertDilation_inner, hilbertDilation_one_inner_one_exact]
  push_cast
  rw [pow_add]
  simp only [Nat.add_sub_cancel_left, mul_one]
  calc
    _ = ((1 / 2 : ℝ) ^ i * (1 / 2 : ℝ) ^ i * (4 : ℝ) ^ i) *
        (1 / 2 : ℝ) ^ k := by ring
    _ = (1 / 2 : ℝ) ^ k := by rw [hcancel, one_mul]

namespace CoefficientStabilization

def quaternaryResidualCorrelation (j : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ j * inner ℝ limitResidual
    (hilbertDilation (4 ^ j) (by positivity) limitResidual)

theorem quaternaryTail_inner_residual (j : ℕ) :
    inner ℝ (quaternaryTail j) limitResidual = quaternaryResidualCorrelation j := by
  unfold quaternaryTail quaternaryResidualCorrelation
  rw [real_inner_smul_left, real_inner_comm,
    limitResidual_inner_dilation_one]

theorem quaternaryResidualCorrelation_zero :
    quaternaryResidualCorrelation 0 = limitEnergy := by
  simp only [quaternaryResidualCorrelation, pow_zero, hilbertDilation_one,
    one_mul, real_inner_self_eq_norm_sq]
  rfl

/-- Every Gram hypothesis is discharged for actual dilation correlations. -/
theorem residual_geometric_innovation_finite_bound (N : ℕ) :
    limitEnergy ^ 2 + (4 / 3 : ℝ) *
      (∑ j ∈ Finset.range N,
        (quaternaryResidualCorrelation (j + 1) -
          (1 / 2 : ℝ) * quaternaryResidualCorrelation j) ^ 2) ≤ limitEnergy := by
  have hc : (2 / Real.sqrt 3 : ℝ) ^ 2 * (1 - (1 / 2 : ℝ) ^ 2) = 1 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have h := geometricInnovation_finite_bound quaternaryTail (1 / 2) (2 / Real.sqrt 3)
    quaternaryTail_gram hc limitResidual N
  simp only [quaternaryTail_inner_residual, quaternaryResidualCorrelation_zero,
    div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] at h
  norm_num only at h
  exact h


theorem residual_geometric_innovation_summable :
    Summable (fun j : ℕ => (4 / 3 : ℝ) *
      (quaternaryResidualCorrelation (j + 1) -
        (1 / 2 : ℝ) * quaternaryResidualCorrelation j) ^ 2) := by
  have hc : (2 / Real.sqrt 3 : ℝ) ^ 2 * (1 - (1 / 2 : ℝ) ^ 2) = 1 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have h := geometricInnovation_weighted_summable quaternaryTail (1 / 2) (2 / Real.sqrt 3)
    quaternaryTail_gram hc limitResidual
  simpa only [quaternaryTail_inner_residual, div_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), show (2 : ℝ) ^ 2 = 4 by norm_num] using h

theorem residual_geometric_innovation_infinite_bound :
    limitEnergy ^ 2 + (∑' j : ℕ, (4 / 3 : ℝ) *
      (quaternaryResidualCorrelation (j + 1) -
        (1 / 2 : ℝ) * quaternaryResidualCorrelation j) ^ 2) ≤ limitEnergy := by
  have ht := (tendsto_const_nhds (x := limitEnergy ^ 2)).add
    residual_geometric_innovation_summable.hasSum.tendsto_sum_nat
  apply le_of_tendsto' ht
  intro N
  simpa only [Finset.mul_sum] using residual_geometric_innovation_finite_bound N

/-- Exact cancellation of the normalization factors; no asymptotic notation. -/
theorem residual_geometric_innovation_eq (j : ℕ) :
    (4 / 3 : ℝ) * (quaternaryResidualCorrelation (j + 1) -
        (1 / 2 : ℝ) * quaternaryResidualCorrelation j) ^ 2 =
      (1 / 3 : ℝ) * (1 / 4 : ℝ) ^ j *
        (inner ℝ limitResidual
            (hilbertDilation (4 ^ (j + 1)) (by positivity) limitResidual) -
          inner ℝ limitResidual
            (hilbertDilation (4 ^ j) (by positivity) limitResidual)) ^ 2 := by
  have hp : ((1 / 2 : ℝ) ^ j) ^ 2 = (1 / 4 : ℝ) ^ j := by
    rw [← pow_mul, Nat.mul_comm j 2, pow_mul]
    norm_num
  unfold quaternaryResidualCorrelation
  rw [pow_succ]
  calc
    _ = (1 / 3 : ℝ) * ((1 / 2 : ℝ) ^ j) ^ 2 *
        (inner ℝ limitResidual
            (hilbertDilation (4 ^ (j + 1)) (by positivity) limitResidual) -
          inner ℝ limitResidual
            (hilbertDilation (4 ^ j) (by positivity) limitResidual)) ^ 2 := by ring
    _ = _ := by rw [hp]

theorem residual_geometric_pairing_difference_summable :
    Summable (fun j : ℕ => (1 / 3 : ℝ) * (1 / 4 : ℝ) ^ j *
      (inner ℝ limitResidual
          (hilbertDilation (4 ^ (j + 1)) (by positivity) limitResidual) -
        inner ℝ limitResidual
          (hilbertDilation (4 ^ j) (by positivity) limitResidual)) ^ 2) := by
  simpa only [residual_geometric_innovation_eq] using residual_geometric_innovation_summable

theorem residual_geometric_pairing_difference_bound :
    limitEnergy ^ 2 + (∑' j : ℕ, (1 / 3 : ℝ) * (1 / 4 : ℝ) ^ j *
      (inner ℝ limitResidual
          (hilbertDilation (4 ^ (j + 1)) (by positivity) limitResidual) -
        inner ℝ limitResidual
          (hilbertDilation (4 ^ j) (by positivity) limitResidual)) ^ 2) ≤ limitEnergy := by
  simpa only [residual_geometric_innovation_eq] using residual_geometric_innovation_infinite_bound


theorem residual_quaternary_correlation_finite_bound (N : ℕ) :
    (∑ j ∈ Finset.range (N + 1), (quaternaryResidualCorrelation j) ^ 2) ≤
      3 * limitEnergy - limitEnergy ^ 2 := by
  have hi := geometric_half_scalar_energy_identity quaternaryResidualCorrelation N
  rw [quaternaryResidualCorrelation_zero] at hi
  have hb := residual_geometric_innovation_finite_bound N
  have hd : 0 ≤ ∑ j ∈ Finset.range N,
      (quaternaryResidualCorrelation (j + 1) - quaternaryResidualCorrelation j) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  nlinarith [sq_nonneg (quaternaryResidualCorrelation N)]

theorem residual_quaternary_correlation_finset_bound (s : Finset ℕ) :
    (∑ j ∈ s, (quaternaryResidualCorrelation j) ^ 2) ≤
      3 * limitEnergy - limitEnergy ^ 2 := by
  have hsub : s ⊆ Finset.range (s.sup id + 1) := by
    intro j hj
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hj)
  calc
    _ ≤ ∑ j ∈ Finset.range (s.sup id + 1),
        (quaternaryResidualCorrelation j) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
    _ ≤ _ := residual_quaternary_correlation_finite_bound (s.sup id)

theorem residual_quaternary_correlation_summable :
    Summable (fun j : ℕ => (quaternaryResidualCorrelation j) ^ 2) :=
  summable_of_sum_le (fun _ => sq_nonneg _)
    residual_quaternary_correlation_finset_bound

theorem residual_quaternary_correlation_tsum_bound :
    (∑' j : ℕ, (quaternaryResidualCorrelation j) ^ 2) ≤
      3 * limitEnergy - limitEnergy ^ 2 := by
  exact le_of_tendsto' residual_quaternary_correlation_summable.hasSum.tendsto_sum_nat
    (fun N => residual_quaternary_correlation_finset_bound (Finset.range N))

theorem quaternaryResidualCorrelation_sq (j : ℕ) :
    (quaternaryResidualCorrelation j) ^ 2 =
      (1 / 4 : ℝ) ^ j * (inner ℝ limitResidual
        (hilbertDilation (4 ^ j) (by positivity) limitResidual)) ^ 2 := by
  have hp : ((1 / 2 : ℝ) ^ j) ^ 2 = (1 / 4 : ℝ) ^ j := by
    rw [← pow_mul, Nat.mul_comm j 2, pow_mul]
    norm_num
  unfold quaternaryResidualCorrelation
  rw [mul_pow, hp]

/-- The actual normalized dilation correlations belong to l2 on geometric scales. -/
theorem residual_geometric_pairing_square_summable :
    Summable (fun j : ℕ => (1 / 4 : ℝ) ^ j * (inner ℝ limitResidual
      (hilbertDilation (4 ^ j) (by positivity) limitResidual)) ^ 2) := by
  simpa only [quaternaryResidualCorrelation_sq] using residual_quaternary_correlation_summable

theorem residual_geometric_pairing_square_tsum_bound :
    (∑' j : ℕ, (1 / 4 : ℝ) ^ j * (inner ℝ limitResidual
      (hilbertDilation (4 ^ j) (by positivity) limitResidual)) ^ 2) ≤
        3 * limitEnergy - limitEnergy ^ 2 := by
  simpa only [quaternaryResidualCorrelation_sq] using residual_quaternary_correlation_tsum_bound

end CoefficientStabilization
end RiemannResearch.RH.Pareto
