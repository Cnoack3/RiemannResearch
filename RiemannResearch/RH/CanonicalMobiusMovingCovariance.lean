/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CanonicalMobiusCovarianceDecay
import RiemannResearch.RH.CanonicalMobiusFullEnergy
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Moving bounded tests and canonical residual blocks

Source: the user's quantitative extension of the fixed-test covariance theorem,
15 October 2026. The proof uses the checked squared-pairing inequality separately
at each index and finite Cauchy--Schwarz. All pairings are complete Hilbert
pairings. Block column decay does not bound the block's own Gram quadratic form.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.RH.Pareto.MovingCovariance
def residual (N : ℕ) : ThresholdHilbert := hilbertOne - canonicalMobiusHilbert N
def energyRate (N : ℕ) : ℝ := ‖residual N‖ ^ 2 / ((N : ℝ) + 1)
theorem energyRate_nonneg (N : ℕ) : 0 ≤ energyRate N := by
  unfold energyRate
  positivity
theorem moving_test_tendsto (f : ℕ → ThresholdHilbert) (A : ℕ → ℝ)
    (hA : ∀ N, 0 ≤ A N)
    (hf : ∀ N n, 0 < n → |hilbertSequence (f N) n| ≤ A N)
    (hbudget : Tendsto (fun N => (A N) ^ 2 * energyRate N) atTop (𝓝 0)) :
    Tendsto (fun N => inner ℝ (f N) (residual N)) atTop (𝓝 0) := by
  have hs : Tendsto (fun N => (inner ℝ (f N) (residual N)) ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => sq_nonneg _)) _ hbudget
    exact Eventually.of_forall (fun N => by
      simpa only [energyRate, residual, div_mul_eq_mul_div, mul_div_assoc] using
        canonicalResidual_inner_sq_le (f N) N (A N) (hA N) (hf N))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero, Real.norm_eq_abs] using ht

theorem physical_bound (K : ℕ) (hK : 0 < K) (n : ℕ) (hn : 0 < n) :
    |hilbertSequence (residual K) n| ≤ 1 + 2 * (K : ℝ) := by
  have hseq : hilbertSequence (residual K) n = 1 - canonicalMobiusHead K n := by
    change hilbertSequenceLinear (hilbertOne - canonicalMobiusHilbert K) n = _
    rw [map_sub]
    change hilbertSequence hilbertOne n - hilbertSequence (canonicalMobiusHilbert K) n = _
    rw [hilbertOne_sequence, canonicalMobiusHilbert_sequence]
    simp [zeroAnchor, ne_of_gt hn]
  rw [hseq]
  have hb := abs_le.mp (canonicalMobiusHead_abs_le_two_mul K hK n)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem covariance_sq_le (K N : ℕ) (hK : 0 < K) :
    (inner ℝ (residual K) (residual N)) ^ 2 ≤
      (1 + 2 * (K : ℝ)) ^ 2 * energyRate N := by
  simpa only [residual, energyRate, div_mul_eq_mul_div, mul_div_assoc] using
    canonicalResidual_inner_sq_le (residual K) N (1 + 2 * (K : ℝ))
      (by positivity) (physical_bound K hK)

theorem moving_canonical_tendsto (K : ℕ → ℕ) (hK : ∀ N, 0 < K N)
    (hbudget : Tendsto (fun N => (1 + 2 * (K N : ℝ)) ^ 2 * energyRate N)
      atTop (𝓝 0)) :
    Tendsto (fun N => inner ℝ (residual (K N)) (residual N)) atTop (𝓝 0) :=
  moving_test_tendsto (fun N => residual (K N)) _ (fun _ => by positivity)
    (fun N => physical_bound _ (hK N)) hbudget

def blockEnergy (K N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range K, (inner ℝ (residual (k + 1)) (residual N)) ^ 2

theorem blockEnergy_nonneg (K N : ℕ) : 0 ≤ blockEnergy K N :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem blockEnergy_le (K N : ℕ) :
    blockEnergy K N ≤ (K : ℝ) * (1 + 2 * (K : ℝ)) ^ 2 * energyRate N := by
  calc
    blockEnergy K N ≤ ∑ k ∈ Finset.range K,
        (1 + 2 * (K : ℝ)) ^ 2 * energyRate N := by
      apply Finset.sum_le_sum
      intro k hk
      have hkK : ((k + 1 : ℕ) : ℝ) ≤ (K : ℝ) := by
        exact_mod_cast (show k + 1 ≤ K from Finset.mem_range.mp hk)
      have hs : (1 + 2 * ((k + 1 : ℕ) : ℝ)) ^ 2 ≤ (1 + 2 * (K : ℝ)) ^ 2 := by
        nlinarith [Nat.cast_nonneg (α := ℝ) (k + 1)]
      exact (covariance_sq_le (k + 1) N (Nat.succ_pos _)).trans
        (mul_le_mul_of_nonneg_right hs (energyRate_nonneg N))
    _ = _ := by simp [Finset.sum_const, mul_assoc]

theorem blockEnergy_tendsto (K : ℕ → ℕ)
    (hbudget : Tendsto
      (fun N => (K N : ℝ) * (1 + 2 * (K N : ℝ)) ^ 2 * energyRate N) atTop (𝓝 0)) :
    Tendsto (fun N => blockEnergy (K N) N) atTop (𝓝 0) :=
  squeeze_zero (fun _ => blockEnergy_nonneg _ _) (fun _ => blockEnergy_le _ _) hbudget


def residualAverage (s : Finset ℕ) (a : ℕ → ℝ) : ThresholdHilbert :=
  ∑ k ∈ s, a k • residual k

/-- Exact full-Hilbert Gram equality, with every signed cross term. -/
theorem residualAverage_energy (s : Finset ℕ) (a : ℕ → ℝ) :
    ‖residualAverage s a‖ ^ 2 =
      ∑ k ∈ s, ∑ l ∈ s, a k * a l * inner ℝ (residual k) (residual l) := by
  rw [residualAverage, ← real_inner_self_eq_norm_sq]
  simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  simp only [mul_assoc]

def blockAverage (K : ℕ) (a : ℕ → ℝ) : ThresholdHilbert :=
  ∑ k ∈ Finset.range K, a k • residual (k + 1)

theorem blockAverage_inner_sq_le (K N : ℕ) (a : ℕ → ℝ) :
    (inner ℝ (blockAverage K a) (residual N)) ^ 2 ≤
      (∑ k ∈ Finset.range K, a k ^ 2) * blockEnergy K N := by
  simp only [blockAverage, sum_inner, real_inner_smul_left]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

theorem blockAverage_tendsto (K : ℕ → ℕ) (a : ℕ → ℕ → ℝ)
    (B : ℝ) (hB : ∀ N, (∑ k ∈ Finset.range (K N), a N k ^ 2) ≤ B)
    (hb : Tendsto (fun N => blockEnergy (K N) N) atTop (𝓝 0)) :
    Tendsto (fun N => inner ℝ (blockAverage (K N) (a N)) (residual N))
      atTop (𝓝 0) := by
  have hs : Tendsto
      (fun N => (inner ℝ (blockAverage (K N) (a N)) (residual N)) ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => sq_nonneg _) _ (by simpa using hb.const_mul B)
    intro N
    exact (blockAverage_inner_sq_le _ _ _).trans
      (mul_le_mul_of_nonneg_right (hB N) (blockEnergy_nonneg _ _))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero, Real.norm_eq_abs] using ht

theorem convex_coefficients_sq_le_one (K : ℕ) (a : ℕ → ℝ)
    (ha : ∀ k ∈ Finset.range K, 0 ≤ a k)
    (hsum : ∑ k ∈ Finset.range K, a k = 1) :
    (∑ k ∈ Finset.range K, a k ^ 2) ≤ 1 := by
  calc
    _ ≤ ∑ k ∈ Finset.range K, a k := by
      apply Finset.sum_le_sum
      intro k hk
      have hle : a k ≤ 1 := by
        rw [← hsum]
        exact Finset.single_le_sum ha hk
      nlinarith [ha k hk]
    _ = _ := hsum

end RiemannResearch.RH.Pareto.MovingCovariance
