/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite signed period-mean certificate for the derivative product optimizer

Finite certificate for the prime-block continuation. This module certifies the finite algebra
after the arithmetic divisor sums and the mean of g_d have been provided.
It does not itself assert the divisor-sum hypotheses or global Q-energy bound.
The full mathematical derivation is in Product_Derivative_Optimizer_NoGo.md.
-/

open scoped BigOperators
namespace RiemannResearch.LinearAlgebra.DerivativeOptimizerPeriodMean

/-- The Möbius terms are retained until their exact cancellation. For a divisor
set, d is the conductor, μ is the Möbius function, M is the number of divisors,
H times their sum is the period L, and A H is the reciprocal Möbius sum. -/
theorem signed_mean_identity {ι : Type*} (s : Finset ι) (d μ : ι → ℝ)
    (q H A M L D : ℝ) (hA : A ≠ 0) (hM : M ≠ 0)
    (hd : ∀ i ∈ s, d i ≠ 0)
    (hcard : (s.card : ℝ) = M) (hsum : ∑ i ∈ s, d i = D)
    (hmu : ∑ i ∈ s, μ i = 0)
    (hmudiv : ∑ i ∈ s, μ i / d i = A * H) (hperiod : H * D = L) :
    (∑ i ∈ s, (q * (H * d i / M - μ i / A)) *
      ((d i - 1) / (2 * d i))) = q * L / (2 * M) := by
  calc
    _ = ∑ i ∈ s, ((q * H / (2 * M)) * d i - q * H / (2 * M) -
        (q / (2 * A)) * μ i + (q / (2 * A)) * (μ i / d i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      field_simp [hd i hi, hA, hM]
      ring
    _ = q * L / (2 * M) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
        hcard, hsum, hmu, hmudiv]
      rw [← hperiod]
      field_simp [hA, hM]
      ring

/-- Once weighted Cauchy--Schwarz is normalized by L³, a nonzero signed period
mean forces a complete-energy lower bound. This is a scalar consumer only. -/
theorem energy_lower_of_normalized_cauchy
    {q L M prefixEnergy totalEnergy : ℝ}
    (hq : 0 < q) (hM : 0 < M)
    (hCauchy : q ^ 2 * L ≤ 4 * M ^ 2 * prefixEnergy)
    (hprefix : q * prefixEnergy ≤ totalEnergy) :
    q ^ 3 * L / (4 * M ^ 2) ≤ totalEnergy := by
  apply (div_le_iff₀ (by positivity : 0 < 4 * M ^ 2)).mpr
  have h1 := mul_le_mul_of_nonneg_left hCauchy hq.le
  have h2 := mul_le_mul_of_nonneg_right hprefix
    (by positivity : 0 ≤ 4 * M ^ 2)
  nlinarith

/-- Weighted Cauchy--Schwarz gives the energy obstruction from the exact signed
period sum. Taking s={1,...,L}, w(n)=n² supplies the arithmetic application. -/
theorem weighted_energy_lower_from_period_mean {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (f w : ι → ℝ)
    {q L M : ℝ} (hq : 0 < q) (hL : 0 < L) (hM : 0 < M)
    (hw : ∀ i ∈ s, 0 < w i)
    (hmean : ∑ i ∈ s, f i = q * L ^ 2 / (2 * M))
    (hweight : ∑ i ∈ s, w i ≤ L ^ 3) :
    q ^ 3 * L / (4 * M ^ 2) ≤ q * ∑ i ∈ s, f i ^ 2 / w i := by
  have hW : 0 < ∑ i ∈ s, w i := Finset.sum_pos hw hs
  have hCS := Finset.sq_sum_div_le_sum_sq_div s f hw
  calc
    q ^ 3 * L / (4 * M ^ 2) = q * ((∑ i ∈ s, f i) ^ 2 / L ^ 3) := by
      rw [hmean]
      field_simp [ne_of_gt hL, ne_of_gt hM]
      ring
    _ ≤ q * ((∑ i ∈ s, f i) ^ 2 / (∑ i ∈ s, w i)) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (sq_nonneg _) hW hweight) hq.le
    _ ≤ q * ∑ i ∈ s, f i ^ 2 / w i :=
      mul_le_mul_of_nonneg_left hCS hq.le

end RiemannResearch.LinearAlgebra.DerivativeOptimizerPeriodMean
