/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.CenteredProjectionResponse
import RiemannResearch.RH.QSquarefreeShortHeadResponse
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import RiemannResearch.RH.QSquarefreeCorrectionKernel
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Exact Abel sums of the actual squarefree prefix response

Source: `SquarefreePrefixResponseResearch20261030.md`, sections 2 and 4,
for the finite and infinite Abel identities and the centered prefix variance.
This continues `SquarefreeShortHeadLean20261031.md`. All kernels and residuals
use the complete canonical squarefree stage, including composite conductors.
Physical prefixes use the full Q inner product. No arithmetic growth provider
or Riemann Hypothesis conclusion is asserted in this module.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QSquarefreePrefixAbel
open ZetaTwoHilbert ZetaTwoOptimizerStage QFiniteSupportDualCriterion
open QSquarefreeCorrectionKernel QSquarefreeShortHeadResponse
open QSquarefreeSmoothedProjection QShiftedReciprocal

def prefixResponse (N n H : ℕ) : ℝ :=
  inner ℝ (kernel N n) (finiteHead H (residual N))

theorem prefix_eq_sum (N n H : ℕ) :
    prefixResponse N n H = ∑ i ∈ Finset.range H, (residual N) i * (kernel N n) i :=
  inner_finiteHead_eq_sum _ _ _

@[simp] theorem prefix_zero (N n : ℕ) : prefixResponse N n 0 = 0 := by
  simp [prefix_eq_sum]


/-- The Hilbert prefix is exactly the original Q-weighted physical prefix. -/
theorem prefix_eq_physical_sum (N n H : ℕ) :
    prefixResponse N n H = ∑ i ∈ Finset.range H,
      positiveQWeight (i + 1) * qSequence (residual N) (i + 1) *
        qSequence (kernel N n) (i + 1) := by
  rw [prefix_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  symm
  calc
    _ = qWeight i * (((residual N) i * (kernel N n) i) /
        Real.sqrt (qWeight i) ^ 2) := by
      simp only [qSequence_succ]
      change qWeight i * (_ / _) * (_ / _) = _
      ring
    _ = _ := by
      rw [Real.sq_sqrt (qWeight_pos i).le]
      exact mul_div_cancel₀ _ (qWeight_pos i).ne'

theorem prefix_eq_neg_complete_tail (N n H : ℕ) :
    prefixResponse N n H = -inner ℝ (kernel N n)
      (residual N - finiteHead H (residual N)) :=
  residual_partial_normal_equation N H (kernel N n)
    ((stage N).starProjection_apply_mem (evaluation n))

theorem prefix_succ (N n H : ℕ) :
    prefixResponse N n (H + 1) = prefixResponse N n H + (residual N) H * (kernel N n) H := by
  simp only [prefix_eq_sum, Finset.sum_range_succ]

theorem response_eq_sum (N H n : ℕ) :
    response N H n = ∑ i ∈ Finset.range H,
      (1 / ((i : ℝ) + 2) - 1 / ((n : ℝ) + 1)) *
        ((residual N) i * (kernel N n) i) := by
  rw [response, source, inner_finiteHead_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change ((B (residual N)) i - (1 / ((n : ℝ) + 1)) * (residual N) i) *
    (kernel N n) i = _
  rw [B_apply]
  ring

/-- Abel summation with an endpoint shifted one site beyond the cutoff.
The endpoint vanishes exactly when n = H + 1. -/
theorem response_abel_exact (N H n : ℕ) :
    response N H n =
      (1 / ((H : ℝ) + 2) - 1 / ((n : ℝ) + 1)) * prefixResponse N n H +
      ∑ h ∈ Finset.range H,
        prefixResponse N n (h + 1) / (((h : ℝ) + 2) * ((h : ℝ) + 3)) := by
  induction H with
  | zero => simp [response_eq_sum]
  | succ H ih =>
    have hstep : response N (H + 1) n = response N H n +
        (1 / ((H : ℝ) + 2) - 1 / ((n : ℝ) + 1)) *
          ((residual N) H * (kernel N n) H) := by
      simp only [response_eq_sum, Finset.sum_range_succ]
    rw [hstep, ih, Finset.sum_range_succ, prefix_succ]
    push_cast
    have h2 : (H : ℝ) + 2 ≠ 0 := by positivity
    have h3 : (H : ℝ) + 3 ≠ 0 := by positivity
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

theorem lower_response_abel_exact (N H : ℕ) :
    response N H (H + 1) = ∑ h ∈ Finset.range H,
      prefixResponse N (H + 1) (h + 1) / (((h : ℝ) + 2) * ((h : ℝ) + 3)) := by
  rw [response_abel_exact]
  norm_num [Nat.cast_add, Nat.cast_one, add_assoc]

theorem prefix_tendsto_zero (N n : ℕ) :
    Tendsto (prefixResponse N n) atTop (𝓝 0) := by
  have h : Tendsto (fun H => inner ℝ (kernel N n) (finiteHead H (residual N)))
      atTop (𝓝 (inner ℝ (kernel N n) (residual N))) :=
    tendsto_const_nhds.inner (finiteHead_tendsto (residual N))
  have hz : inner ℝ (kernel N n) (residual N) = 0 :=
    ((stage N).mem_orthogonal _ |>.mp (residual_mem_orthogonal N)) _
      ((stage N).starProjection_apply_mem (evaluation n))
  change Tendsto (fun H => inner ℝ (kernel N n) (finiteHead H (residual N))) atTop (𝓝 0)
  rw [hz] at h
  exact h

theorem response_tendsto (N n : ℕ) :
    Tendsto (fun H => response N H n) atTop
      (𝓝 (qSequence (movingCorrection N) n)) := by
  have h : Tendsto (fun H => inner ℝ (residual N)
      (finiteHead H (B (kernel N n) - (1 / ((n : ℝ) + 1)) • kernel N n)))
      atTop (𝓝 (inner ℝ (residual N)
      (B (kernel N n) - (1 / ((n : ℝ) + 1)) • kernel N n))) :=
    tendsto_const_nhds.inner (finiteHead_tendsto _)
  simpa only [response_eq_head_pairing,
    ← movingCorrection_eq_centered_pairing N n (1 / ((n : ℝ) + 1))] using h


theorem prefix_abs_le (N n H : ℕ) :
    |prefixResponse N n H| ≤ ‖kernel N n‖ * ‖residual N‖ := by
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_left (finiteHead_norm_le H (residual N)) (norm_nonneg _))

theorem abel_terms_summable (N n : ℕ) :
    Summable (fun h : ℕ =>
      prefixResponse N n (h + 1) / (((h : ℝ) + 2) * ((h : ℝ) + 3))) := by
  have hs : Summable (fun h : ℕ => 1 / ((h : ℝ) + 2) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (summable_nat_add_iff 2).mpr
        (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
  apply (hs.mul_left (‖kernel N n‖ * ‖residual N‖)).of_norm_bounded
  intro h
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity :
    0 < ((h : ℝ) + 2) * ((h : ℝ) + 3))]
  calc
    _ ≤ (‖kernel N n‖ * ‖residual N‖) /
        (((h : ℝ) + 2) * ((h : ℝ) + 3)) :=
      div_le_div_of_nonneg_right (prefix_abs_le N n (h + 1)) (by positivity)
    _ ≤ (‖kernel N n‖ * ‖residual N‖) / ((h : ℝ) + 2) ^ 2 := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith [Nat.cast_nonneg (α := ℝ) h]
    _ = _ := by ring

/-- The complete centered response is an absolutely convergent signed Abel sum. -/
theorem movingCorrection_hasSum_prefix (N n : ℕ) :
    HasSum (fun h : ℕ =>
      prefixResponse N n (h + 1) / (((h : ℝ) + 2) * ((h : ℝ) + 3)))
      (qSequence (movingCorrection N) n) := by
  have hd : Tendsto (fun H : ℕ => 1 / ((H : ℝ) + 2)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hb : Tendsto (fun H : ℕ =>
      (1 / ((H : ℝ) + 2) - 1 / ((n : ℝ) + 1)) * prefixResponse N n H)
      atTop (𝓝 0) := by
    simpa using (hd.sub_const (1 / ((n : ℝ) + 1))).mul (prefix_tendsto_zero N n)
  apply (hasSum_iff_tendsto_nat_of_summable_norm (abel_terms_summable N n).norm).mpr
  have ht := (response_tendsto N n).sub hb
  simpa only [response_abel_exact, add_sub_cancel_left, sub_zero] using ht

theorem movingCorrection_eq_tsum_prefix (N n : ℕ) :
    qSequence (movingCorrection N) n = ∑' h : ℕ,
      prefixResponse N n (h + 1) / (((h : ℝ) + 2) * ((h : ℝ) + 3)) :=
  (movingCorrection_hasSum_prefix N n).tsum_eq.symm

/-- The contribution of a physical interval (u,v], including both endpoints. -/
theorem interval_response_abel_exact (N n u v : ℕ) :
    response N v n - response N u n =
      (1 / ((v : ℝ) + 2) - 1 / ((n : ℝ) + 1)) * prefixResponse N n v -
      (1 / ((u : ℝ) + 2) - 1 / ((n : ℝ) + 1)) * prefixResponse N n u +
      ((∑ h ∈ Finset.range v, prefixResponse N n (h + 1) /
        (((h : ℝ) + 2) * ((h : ℝ) + 3))) -
       ∑ h ∈ Finset.range u, prefixResponse N n (h + 1) /
        (((h : ℝ) + 2) * ((h : ℝ) + 3))) := by
  rw [response_abel_exact, response_abel_exact]
  ring

open ZetaTwoHilbert ZetaTwoOptimizerStage QFiniteSupportDualCriterion
open QSquarefreeCorrectionKernel
open RiemannResearch.Analysis.CenteredProjectionResponse

def prefixHeadEnergy (N H : ℕ) : ℝ := ‖finiteHead H (residual N)‖ ^ 2

def prefixLoss (N H : ℕ) : QHilbert :=
  sourceLoss (stage N) (residual N) (finiteHead H (residual N))

theorem prefix_inner_head (N H : ℕ) :
    inner ℝ (residual N) (finiteHead H (residual N)) = prefixHeadEnergy N H := by
  unfold prefixHeadEnergy
  rw [← real_inner_self_eq_norm_sq]
  rw [finiteHead_inner, finiteHead_idem]

/-- The exact prefix variance keeps both the complete residual energy and the
full orthogonal loss. -/
theorem prefix_projected_energy_exact (N H : ℕ) :
    ‖(stage N).starProjection (finiteHead H (residual N))‖ ^ 2 =
      prefixHeadEnergy N H * (error N - prefixHeadEnergy N H) / error N -
        ‖prefixLoss N H‖ ^ 2 := by
  have h := source_variance_exact (stage N) (residual N) (finiteHead H (residual N))
    (residual_mem_orthogonal N) (ne_of_gt (error_pos N))
  rw [prefix_inner_head] at h
  change _ = prefixHeadEnergy N H - prefixHeadEnergy N H ^ 2 / error N -
    ‖prefixLoss N H‖ ^ 2 at h
  rw [h]
  have he := ne_of_gt (error_pos N)
  field_simp

theorem prefix_sq_le_exact_variance (N n H : ℕ) :
    prefixResponse N n H ^ 2 ≤ ‖kernel N n‖ ^ 2 *
      (prefixHeadEnergy N H * (error N - prefixHeadEnergy N H) / error N -
        ‖prefixLoss N H‖ ^ 2) := by
  have h := response_sq_le_source_variance (stage N) (residual N)
    (evaluation n) (finiteHead H (residual N))
    (residual_mem_orthogonal N) (ne_of_gt (error_pos N))
  rw [prefix_inner_head] at h
  have heq : prefixHeadEnergy N H - prefixHeadEnergy N H ^ 2 / error N =
      prefixHeadEnergy N H * (error N - prefixHeadEnergy N H) / error N := by
    have he := ne_of_gt (error_pos N)
    field_simp
  change prefixResponse N n H ^ 2 ≤ ‖kernel N n‖ ^ 2 *
    (prefixHeadEnergy N H - prefixHeadEnergy N H ^ 2 / error N -
      ‖prefixLoss N H‖ ^ 2) at h
  rwa [heq] at h
theorem prefix_heads_inner (N H J : ℕ) (hHJ : H ≤ J) :
    inner ℝ (finiteHead H (residual N)) (finiteHead J (residual N)) =
      prefixHeadEnergy N H := by
  unfold prefixHeadEnergy
  rw [← real_inner_self_eq_norm_sq]
  conv_lhs => rw [real_inner_comm]
  rw [inner_finiteHead_eq_sum, inner_finiteHead_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [finiteHead_apply_of_lt J _ i (lt_of_lt_of_le (Finset.mem_range.mp hi) hHJ),
    finiteHead_apply_of_lt H _ i (Finset.mem_range.mp hi)]

theorem prefix_covariance_exact (N H J : ℕ) (hHJ : H ≤ J) :
    inner ℝ ((stage N).starProjection (finiteHead H (residual N)))
      ((stage N).starProjection (finiteHead J (residual N))) =
      prefixHeadEnergy N H -
        prefixHeadEnergy N H * prefixHeadEnergy N J / error N -
        inner ℝ (prefixLoss N H) (prefixLoss N J) := by
  have h := source_covariance_exact (stage N) (residual N)
    (finiteHead H (residual N)) (finiteHead J (residual N))
    (residual_mem_orthogonal N) (ne_of_gt (error_pos N))
  rw [prefix_heads_inner N H J hHJ, prefix_inner_head, prefix_inner_head] at h
  exact h

end RiemannResearch.RH.QSquarefreePrefixAbel
