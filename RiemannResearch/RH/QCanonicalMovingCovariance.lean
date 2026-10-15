/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CanonicalMobiusMovingCutoff
import RiemannResearch.RH.CanonicalMobiusConditionalHead
import RiemannResearch.RH.ExactHeadResidualTail
import RiemannResearch.RH.NearbyDilationGram
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoParetoTransfer
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Moving canonical covariance in the actual Q Hilbert space

Source: the user's moving-test investigation, 15 October 2026, and the
repository's complete Q/P comparison. The actual canonical physical sequence
is encoded with Q weights. Tail Cauchy--Schwarz and the checked PNT cutoff
yield unconditional moving-test and growing-column decay in Q.
The Q and P pairings remain distinct, with all comparison constants retained.
No bound on a cofinal average's own energy is asserted here.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.RH.QCanonicalMovingCovariance
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer Pareto

def canonical (N : ℕ) : QHilbert :=
  -(∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) • qResidue d) +
    (((N + 1 : ℕ) : ℝ) * mobiusReciprocalSum N) • qResidue (N + 1)

theorem canonical_sequence (N : ℕ) : qSequence (canonical N) = canonicalMobiusHead N := by
  change qSequenceLinear (canonical N) = _
  unfold canonical
  simp only [map_add, map_neg, map_sum, map_smul]
  change -(∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) •
      qSequence (qResidue d)) +
    (((N + 1 : ℕ) : ℝ) * mobiusReciprocalSum N) • qSequence (qResidue (N + 1)) = _
  simp_rw [qSequence_qResidue]
  funext n
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_apply, canonicalMobiusHead]

theorem toPareto_canonical (N : ℕ) :
    toPareto (canonical N) = canonicalMobiusHilbert N := by
  apply hilbertSequence_injective
  rw [toPareto_sequence, canonical_sequence, canonicalMobiusHilbert_sequence]

def residual (N : ℕ) : QHilbert := qOne - canonical N

theorem residual_sequence (N : ℕ) :
    qSequence (residual N) = fun n => qOneSequence n - canonicalMobiusHead N n := by
  change qSequenceLinear (qOne - canonical N) = _
  rw [map_sub]
  change qSequence qOne - qSequence (canonical N) = _
  rw [qSequence_qOne, canonical_sequence]
  rfl

theorem toPareto_residual (N : ℕ) :
    toPareto (residual N) = Pareto.MovingCovariance.residual N := by
  change toParetoLinear (qOne - canonical N) = _
  rw [map_sub]
  change toPareto qOne - toPareto (canonical N) = _
  rw [toPareto_qOne, toPareto_canonical]
  rfl

def energyRate (N : ℕ) : ℝ := ‖residual N‖ ^ 2 / ((N : ℝ) + 1)

theorem energyRate_nonneg (N : ℕ) : 0 ≤ energyRate N := by
  unfold energyRate
  positivity

theorem energyRate_le_pareto (N : ℕ) :
    energyRate N ≤ (2 / zetaTwo) * Pareto.MovingCovariance.energyRate N := by
  have hc := zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq (residual N)
  rw [toPareto_residual] at hc
  have hn : ‖residual N‖ ^ 2 ≤ (2 / zetaTwo) * ‖Pareto.MovingCovariance.residual N‖ ^ 2 := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ zetaTwo_pos).mpr
    nlinarith only [hc]
  exact (div_le_div_of_nonneg_right hn (by positivity)).trans_eq (by
    simp only [Pareto.MovingCovariance.energyRate]
    ring)

theorem tail_norm_sq_le_of_bounded (f : QHilbert) (N : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hf : ∀ n, 0 < n → |qSequence f n| ≤ A) :
    ‖hilbertTailShift f N‖ ^ 2 ≤
      (2 / zetaTwo) * A ^ 2 / ((N : ℝ) + 1) := by
  have hs : Summable (fun k : ℕ => positiveQWeight (k + N + 1) *
      qSequence f (k + N + 1) ^ 2) := by
    simpa only [Nat.add_assoc] using
      (summable_nat_add_iff (N + 1)).mpr (qSequence_square_summable f)
  have hw : Summable (fun k : ℕ => positiveWeight (k + N + 1)) := by
    simpa only [Nat.add_assoc] using
      (summable_nat_add_iff (N + 1)).mpr positiveWeight_summable
  calc
    ‖hilbertTailShift f N‖ ^ 2 =
        ∑' k : ℕ, positiveQWeight (k + N + 1) * qSequence f (k + N + 1) ^ 2 := by
      rw [hilbert_norm_sq]
      apply tsum_congr
      intro k
      exact (qSequence_weighted_square f (k + N)).symm
    _ ≤ ∑' k : ℕ, positiveWeight (k + N + 1) * ((2 / zetaTwo) * A ^ 2) := by
      apply Summable.tsum_le_tsum _ hs (hw.mul_right _)
      intro k
      have hsq : qSequence f (k + N + 1) ^ 2 ≤ A ^ 2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hA).mpr (hf _ (by omega))
      have hwc := zetaTwo_mul_QWeight_le_two_mul_paretoWeight (k + N + 1)
      have hwc' : positiveQWeight (k + N + 1) ≤
          (2 / zetaTwo) * positiveWeight (k + N + 1) := by
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ zetaTwo_pos).mpr
        nlinarith only [hwc]
      exact (mul_le_mul_of_nonneg_left hsq (positiveQWeight_nonneg _)).trans
        ((mul_le_mul_of_nonneg_right hwc' (sq_nonneg A)).trans_eq (by ring))
    _ = _ := by
      rw [tsum_mul_right]
      have ht : (∑' k : ℕ, positiveWeight (k + N + 1)) = 1 / ((N : ℝ) + 1) := by
        have h := positiveWeight_tail_tsum (N + 1) (Nat.succ_pos _)
        simpa only [Nat.add_assoc, Nat.cast_add, Nat.cast_one] using h
      rw [ht]
      ring

theorem inner_sq_le (f : QHilbert) (N : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hf : ∀ n, 0 < n → |qSequence f n| ≤ A) :
    (inner ℝ f (residual N)) ^ 2 ≤ (2 / zetaTwo) * A ^ 2 * energyRate N := by
  have he : ∀ n < N, residual N n = 0 := by
    intro n hn
    have hseq : qSequence (residual N) (n + 1) = 0 := by
      rw [residual_sequence]
      change qOneSequence (n + 1) - canonicalMobiusHead N (n + 1) = 0
      rw [canonicalMobiusHead_exact N (n + 1) (by omega) (by omega)]
      simp [qOneSequence]
    rw [qSequence_succ] at hseq
    exact (div_eq_zero_iff.mp hseq).resolve_right
      (ne_of_gt (Real.sqrt_pos.mpr (qWeight_pos n)))
  exact (hilbertTailShift_inner_sq_le f _ N he).trans
    ((mul_le_mul_of_nonneg_right (tail_norm_sq_le_of_bounded f N A hA hf)
      (sq_nonneg _)).trans_eq (by unfold energyRate; ring))

theorem moving_test_tendsto (f : ℕ → QHilbert) (A : ℕ → ℝ)
    (hA : ∀ N, 0 ≤ A N)
    (hf : ∀ N n, 0 < n → |qSequence (f N) n| ≤ A N)
    (hbudget : Tendsto (fun N => (A N) ^ 2 * energyRate N) atTop (𝓝 0)) :
    Tendsto (fun N => inner ℝ (f N) (residual N)) atTop (𝓝 0) := by
  have hs : Tendsto (fun N => (inner ℝ (f N) (residual N)) ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => sq_nonneg _) _
      (by simpa using hbudget.const_mul (2 / zetaTwo))
    intro N
    exact (inner_sq_le (f N) N (A N) (hA N) (hf N)).trans_eq (by ring)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero, Real.norm_eq_abs] using ht

theorem physical_bound (K : ℕ) (hK : 0 < K) (n : ℕ) (hn : 0 < n) :
    |qSequence (residual K) n| ≤ 1 + 2 * (K : ℝ) := by
  rw [← toPareto_sequence, toPareto_residual]
  exact Pareto.MovingCovariance.physical_bound K hK n hn

theorem covariance_sq_le_pareto (K N : ℕ) (hK : 0 < K) :
    (inner ℝ (residual K) (residual N)) ^ 2 ≤
      (2 / zetaTwo) ^ 2 * (1 + 2 * (K : ℝ)) ^ 2 * Pareto.MovingCovariance.energyRate N := by
  calc
    _ ≤ (2 / zetaTwo) * (1 + 2 * (K : ℝ)) ^ 2 * energyRate N :=
      inner_sq_le _ N _ (by positivity) (physical_bound K hK)
    _ ≤ (2 / zetaTwo) * (1 + 2 * (K : ℝ)) ^ 2 *
        ((2 / zetaTwo) * Pareto.MovingCovariance.energyRate N) :=
      mul_le_mul_of_nonneg_left (energyRate_le_pareto N) (by positivity [zetaTwo_pos])
    _ = _ := by ring

def blockEnergy (K N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range K, (inner ℝ (residual (k + 1)) (residual N)) ^ 2

theorem blockEnergy_nonneg (K N : ℕ) : 0 ≤ blockEnergy K N :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem blockEnergy_le (K N : ℕ) :
    blockEnergy K N ≤ (2 / zetaTwo) ^ 2 *
      ((K : ℝ) * (1 + 2 * (K : ℝ)) ^ 2 * Pareto.MovingCovariance.energyRate N) := by
  calc
    blockEnergy K N ≤ ∑ k ∈ Finset.range K,
        (2 / zetaTwo) ^ 2 * (1 + 2 * (K : ℝ)) ^ 2 *
          Pareto.MovingCovariance.energyRate N := by
      apply Finset.sum_le_sum
      intro k hk
      have hkK : ((k + 1 : ℕ) : ℝ) ≤ (K : ℝ) := by
        exact_mod_cast (show k + 1 ≤ K from Finset.mem_range.mp hk)
      have hs : (1 + 2 * ((k + 1 : ℕ) : ℝ)) ^ 2 ≤ (1 + 2 * (K : ℝ)) ^ 2 := by
        nlinarith [Nat.cast_nonneg (α := ℝ) (k + 1)]
      exact (covariance_sq_le_pareto (k + 1) N (Nat.succ_pos _)).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hs (sq_nonneg _))
          (Pareto.MovingCovariance.energyRate_nonneg N))
    _ = _ := by simp [Finset.sum_const]; ring

theorem explicitCutoff_blockEnergy_tendsto :
    Tendsto (fun N => blockEnergy (Pareto.MovingCovariance.explicitCutoff N) N)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun N => blockEnergy_nonneg _ _) (fun N => blockEnergy_le _ _)
  simpa only [mul_zero] using
    Pareto.MovingCovariance.explicitCutoff_budget_tendsto.const_mul ((2 / zetaTwo) ^ 2)

theorem explicitCutoff_covariance_tendsto :
    Tendsto (fun N =>
      inner ℝ (residual (Pareto.MovingCovariance.explicitCutoff N)) (residual N))
      atTop (𝓝 0) := by
  apply moving_test_tendsto _ (fun N => 1 + 2 * (Pareto.MovingCovariance.explicitCutoff N : ℝ))
    (fun _ => by positivity)
    (fun N => physical_bound _ (Pareto.MovingCovariance.explicitCutoff_pos N))
  apply squeeze_zero (fun N => mul_nonneg (sq_nonneg _) (energyRate_nonneg N)) _
    (by simpa only [mul_zero] using
      Pareto.MovingCovariance.explicitCutoff_pair_budget_tendsto.const_mul (2 / zetaTwo))
  intro N
  exact (mul_le_mul_of_nonneg_left (energyRate_le_pareto N) (sq_nonneg _)).trans_eq
    (by ring)

def blockAverage (K : ℕ) (a : ℕ → ℝ) : QHilbert :=
  ∑ k ∈ Finset.range K, a k • residual (k + 1)

theorem blockAverage_inner_sq_le (K N : ℕ) (a : ℕ → ℝ) :
    (inner ℝ (blockAverage K a) (residual N)) ^ 2 ≤
      (∑ k ∈ Finset.range K, a k ^ 2) * blockEnergy K N := by
  simp only [blockAverage, sum_inner, real_inner_smul_left]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

theorem explicitCutoff_signed_block_tendsto (a : ℕ → ℕ → ℝ)
    (B : ℝ) (hB : ∀ N,
      (∑ k ∈ Finset.range (Pareto.MovingCovariance.explicitCutoff N), a N k ^ 2) ≤ B) :
    Tendsto (fun N =>
      inner ℝ (blockAverage (Pareto.MovingCovariance.explicitCutoff N) (a N)) (residual N))
      atTop (𝓝 0) := by
  have hs : Tendsto (fun N =>
      (inner ℝ (blockAverage (Pareto.MovingCovariance.explicitCutoff N) (a N))
        (residual N)) ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => sq_nonneg _) _
      (by simpa using explicitCutoff_blockEnergy_tendsto.const_mul B)
    intro N
    exact (blockAverage_inner_sq_le _ _ _).trans
      (mul_le_mul_of_nonneg_right (hB N) (blockEnergy_nonneg _ _))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero, Real.norm_eq_abs] using ht

theorem explicitCutoff_convex_block_tendsto (a : ℕ → ℕ → ℝ)
    (ha : ∀ N k, k ∈ Finset.range (Pareto.MovingCovariance.explicitCutoff N) → 0 ≤ a N k)
    (hsum : ∀ N, ∑ k ∈ Finset.range (Pareto.MovingCovariance.explicitCutoff N), a N k = 1) :
    Tendsto (fun N =>
      inner ℝ (blockAverage (Pareto.MovingCovariance.explicitCutoff N) (a N)) (residual N))
      atTop (𝓝 0) :=
  explicitCutoff_signed_block_tendsto a 1
    (fun N => Pareto.MovingCovariance.convex_coefficients_sq_le_one _ _ (ha N) (hsum N))
end RiemannResearch.RH.QCanonicalMovingCovariance
