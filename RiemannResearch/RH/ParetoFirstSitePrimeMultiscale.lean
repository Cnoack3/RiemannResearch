/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoFirstSitePrimeBlockContrast

/-!
# Complete multiscale screened prime scatter

Source: the user's October 1 audit continuation, elementary weighted
regression merge, and finite binary recursion. These support the exact
statements and proof strategy; no arithmetic growth or novelty is asserted.

Every internal binary split is retained once. Empty source children are
allowed. Initial capacity, mean mismatch, historical drift and nonprime
gains remain separate in the exact capacity formula.
-/

noncomputable section
open Filter
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.WeightedScalarEnergy

/-- A one-row weighted regression fits exactly; a nonprime zero-weight row
also has zero scatter. -/
theorem primeBlockVariance_one (N : ℕ) : primeBlockVariance N 1 = 0 := by
  rw [primeBlockVariance_eq_quotient]
  simp only [primeBlockError, primeBlockSource, primeBlockCross, square, product,
    Finset.sum_range_one, Nat.add_zero]
  by_cases hw : primeSchurWeight N = 0
  · simp [hw]
  · have hd := ne_of_gt (factorialPrimeDelta_pos N)
    field_simp [hw, hd]
    ring

/-- Sum of every internal split of the depth-h binary tree on [N,N+2^h). -/
def primeDyadicSplitBudget : ℕ → ℕ → ℝ
  | _, 0 => 0
  | N, h+1 => primeDyadicSplitBudget N h + primeDyadicSplitBudget (N+2^h) h +
      primeBlockSplitDrift N (2^h) (2^h)

/-- All child scatters are resolved recursively, including empty prime blocks. -/
theorem primeBlockVariance_eq_dyadicSplitBudget (N h : ℕ) :
    primeBlockVariance N (2^h) = primeDyadicSplitBudget N h := by
  induction h generalizing N with
  | zero => simpa [primeDyadicSplitBudget] using primeBlockVariance_one N
  | succ h ih =>
    have hp : (2:ℕ)^(h+1) = 2^h+2^h := by rw [pow_succ]; omega
    rw [hp, primeBlockVariance_split, ih, ih]
    rfl

theorem primeDyadicSplitBudget_nonneg (N h : ℕ) :
    0 ≤ primeDyadicSplitBudget N h := by
  rw [← primeBlockVariance_eq_dyadicSplitBudget]
  exact primeBlockVariance_nonneg _ _

/-- The historical head--block drift remains outside the internal tree. -/
theorem primeAngularBlock_eq_dyadicSplitBudget_drift (N h : ℕ) (hN : 0 < N) :
    primeAngularBlock N (2^h) =
      primeDyadicSplitBudget N h + primeBlockMeanDrift N (2^h) := by
  rw [primeAngularBlock_eq_variance_add_drift _ _ hN,
    primeBlockVariance_eq_dyadicSplitBudget]

/-- Exact capacity with every internal split and all remaining channels. -/
theorem capacity_eq_dyadicSplitBudget (J : ℕ) :
    tailCapacity (2^J+1) = tailCapacity 1 + primeMeanMismatchBudget (2^J) +
      (∑ j ∈ Finset.range J, primeDyadicSplitBudget (2^j) j) +
      (∑ j ∈ Finset.range J, primeBlockMeanDrift (2^j) (2^j)) +
      compositeGainBudget (2^J) := by
  simpa only [primeBlockVariance_eq_dyadicSplitBudget] using
    capacity_eq_dyadic_prime_block_budget J

/-- Full angular summability retains internal splits and historical drift. -/
theorem primeAngularInnovation_summable_iff_dyadicSplitBudget :
    Summable primeAngularInnovation ↔
      Summable (fun j => primeDyadicSplitBudget (2^j) j) ∧
      Summable (fun j => primeBlockMeanDrift (2^j) (2^j)) := by
  simpa only [primeBlockVariance_eq_dyadicSplitBudget] using
    primeAngularInnovation_summable_iff_dyadic_blocks

/-- Full first-site alternative: the tree channel alone is not asserted necessary. -/
theorem tailCapacity_tendsto_iff_dyadicSplitBudget_channels :
    Tendsto tailCapacity atTop atTop ↔
      (¬ Tendsto primeMeanMismatchBudget atTop (nhds 0)) ∨
      (¬ Summable (fun j => primeDyadicSplitBudget (2^j) j)) ∨
      (¬ Summable (fun j => primeBlockMeanDrift (2^j) (2^j))) ∨
      (¬ Summable factorialCompositeGain) := by
  simpa only [primeBlockVariance_eq_dyadicSplitBudget] using
    tailCapacity_tendsto_iff_dyadic_prime_block_channels

/-- CONDITIONAL RESEARCH REDUCTION. Divergence of the actual all-scale
signed determinant budget remains the explicit Open arithmetic provider. -/
theorem riemannHypothesis_of_dyadicSplitBudget_not_summable
    (hdiv : ¬ Summable (fun j => primeDyadicSplitBudget (2^j) j)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_dyadic_prime_block_variance
  simpa only [primeBlockVariance_eq_dyadicSplitBudget] using hdiv

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
