/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QReciprocalFiniteHead
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# An actual-Q counterexample to unbounded reciprocal lifting

The target and reciprocal operator are the actual qOne and
QShiftedReciprocal.B. The closed source space is the mean-zero hyperplane,
not the arithmetic residue closure. Its explicit approximants show exactly
why boundedness cannot be omitted from the abstract compactness argument.

Physical formula: w_N(n) = Z*n^2/N for 1 <= n <= N and zero afterwards;
v_N = 1-w_N. Thus <1,w_N>=1 and ||R(v_N-1)||^2 <= Z/N.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.QReciprocalMeanZeroCounterexample
open ZetaTwoHilbert ZetaTwoProbability QShiftedReciprocal

private theorem qOne_coordinate (n : ℕ) :
    qOne n = Real.sqrt (qWeight n) := by
  change Real.sqrt (qWeight n) * qOneSequence (n + 1) = _
  simp [qOneSequence]

private theorem qOne_coordinate_pos (n : ℕ) : 0 < qOne n := by
  rw [qOne_coordinate]
  exact Real.sqrt_pos.mpr (qWeight_pos n)

private theorem qOne_coordinate_sq (n : ℕ) :
    (qOne n)^2 = 1 / (zetaTwo * ((n : ℝ) + 1)^2) := by
  rw [qOne_coordinate, Real.sq_sqrt (qWeight_pos n).le]
  simp only [qWeight, positiveQWeight, Nat.cast_add, Nat.cast_one]

/-- A finite vector with physical coordinates Z*n^2/N on 1,...,N. -/
def meanSpike (N : ℕ) : QHilbert :=
  ∑ n ∈ Finset.range N, lp.single 2 n (1 / ((N : ℝ) * qOne n))

theorem meanSpike_apply (N n : ℕ) :
    meanSpike N n = if n < N then 1 / ((N : ℝ) * qOne n) else 0 := by
  simp only [meanSpike, lp.coeFn_sum]
  simp [lp.single_apply, Finset.mem_range]

theorem inner_qOne_meanSpike (N : ℕ) (hN : 0 < N) :
    inner ℝ qOne (meanSpike N) = 1 := by
  simp only [meanSpike, inner_sum, lp.inner_single_right,
    RCLike.inner_apply, conj_trivial]
  have hterm (n : ℕ) : (1 / ((N : ℝ) * qOne n)) * qOne n = 1 / (N : ℝ) := by
    field_simp [ne_of_gt (qOne_coordinate_pos n)]
  simp_rw [hterm]
  simp [ne_of_gt (show (0 : ℝ) < N by exact_mod_cast hN)]

def meanZero : Submodule ℝ QHilbert :=
  (innerSL ℝ qOne).ker

theorem meanZero_isClosed : IsClosed (meanZero : Set QHilbert) := by
  change IsClosed {f : QHilbert | innerSL ℝ qOne f = 0}
  exact isClosed_eq (innerSL ℝ qOne).continuous continuous_const

def meanZeroApproximant (N : ℕ) : QHilbert := qOne - meanSpike N

theorem meanZeroApproximant_mem (N : ℕ) (hN : 0 < N) :
    meanZeroApproximant N ∈ meanZero := by
  change inner ℝ qOne (qOne - meanSpike N) = 0
  rw [inner_sub_right, real_inner_self_eq_norm_sq, qOne_norm_sq,
    inner_qOne_meanSpike N hN]
  ring

theorem qOne_not_mem_meanZero : qOne ∉ meanZero := by
  intro h
  change inner ℝ qOne qOne = 0 at h
  rw [real_inner_self_eq_norm_sq, qOne_norm_sq] at h
  norm_num at h

private theorem reciprocal_spike_coordinate_bound (N n : ℕ) (hN : 0 < N) :
    (B (meanSpike N) n)^2 ≤ zetaTwo / (N : ℝ)^2 := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  rw [B_apply, meanSpike_apply]
  split_ifs with hn
  · have he : (1 / ((N : ℝ) * qOne n) / ((n : ℝ) + 2))^2 =
        (zetaTwo / (N : ℝ)^2) * (((n : ℝ) + 1) / ((n : ℝ) + 2))^2 := by
      rw [div_pow, div_pow, mul_pow, qOne_coordinate_sq]
      field_simp [ne_of_gt hNR, ne_of_gt zetaTwo_pos,
        ne_of_gt (show 0 < (n : ℝ) + 1 by positivity),
        ne_of_gt (show 0 < (n : ℝ) + 2 by positivity)] <;> ring
    rw [he]
    have hr0 : 0 ≤ ((n : ℝ) + 1) / ((n : ℝ) + 2) := by positivity
    have hr1 : ((n : ℝ) + 1) / ((n : ℝ) + 2) ≤ 1 := by
      apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 2)).mpr
      linarith
    have hrsq : (((n : ℝ) + 1) / ((n : ℝ) + 2))^2 ≤ 1 := by nlinarith
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hrsq (div_nonneg zetaTwo_pos.le (sq_nonneg _))
  · simp only [zero_div, zero_pow (by norm_num : 2 ≠ 0)]
    exact div_nonneg zetaTwo_pos.le (sq_nonneg _)

theorem reciprocal_meanSpike_norm_sq_le (N : ℕ) (hN : 0 < N) :
    ‖B (meanSpike N)‖^2 ≤ zetaTwo / (N : ℝ) := by
  rw [qNorm_sq]
  have hsupport : ∀ n ∉ Finset.range N, (B (meanSpike N) n)^2 = 0 := by
    intro n hn
    have hn' : ¬ n < N := by simpa only [Finset.mem_range] using hn
    simp [B_apply, meanSpike_apply, hn']
  rw [tsum_eq_sum hsupport]
  calc
    _ ≤ ∑ _n ∈ Finset.range N, zetaTwo / (N : ℝ)^2 :=
      Finset.sum_le_sum (fun n _ => reciprocal_spike_coordinate_bound N n hN)
    _ = zetaTwo / (N : ℝ) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
      field_simp [hNR] <;> ring

theorem meanZeroApproximant_reciprocal_error_sq_le (N : ℕ) (hN : 0 < N) :
    ‖B (meanZeroApproximant N) - B qOne‖^2 ≤ zetaTwo / (N : ℝ) := by
  have he : B (meanZeroApproximant N) - B qOne = -B (meanSpike N) := by
    simp only [meanZeroApproximant, map_sub]
    abel
  rw [he, norm_neg]
  exact reciprocal_meanSpike_norm_sq_le N hN

theorem meanZeroApproximant_reciprocal_tendsto :
    Tendsto (fun j => B (meanZeroApproximant (j + 1))) atTop (𝓝 (B qOne)) := by
  have hbase : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun j : ℕ =>
      show (j : ℝ) ≤ (j : ℝ) + 1 by linarith) tendsto_natCast_atTop_atTop
  have hbound : Tendsto (fun j : ℕ => zetaTwo / ((j : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp hbase).const_mul zetaTwo
  have hsq : Tendsto (fun j => ‖B (meanZeroApproximant (j + 1)) - B qOne‖^2)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => sq_nonneg _) _ hbound
    intro j
    simpa only [Nat.cast_add, Nat.cast_one] using
      meanZeroApproximant_reciprocal_error_sq_le (j + 1) (by omega)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsqrt

/-- Same operator and target, a closed complete source space, reciprocal
convergence, but failed target membership. Arithmetic legality is not claimed. -/
theorem actual_reciprocal_lifting_counterexample :
    IsClosed (meanZero : Set QHilbert) ∧
      (∀ j, meanZeroApproximant (j + 1) ∈ meanZero) ∧
      Tendsto (fun j => B (meanZeroApproximant (j + 1))) atTop (𝓝 (B qOne)) ∧
      qOne ∉ meanZero :=
  ⟨meanZero_isClosed, fun j => meanZeroApproximant_mem (j + 1) (by omega),
    meanZeroApproximant_reciprocal_tendsto, qOne_not_mem_meanZero⟩

end RiemannResearch.RH.QReciprocalMeanZeroCounterexample
