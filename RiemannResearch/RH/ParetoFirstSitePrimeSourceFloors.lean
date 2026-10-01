/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoFirstSitePrimeBlockContrast
import RiemannResearch.RH.ParetoAdjacentSchurBound
import RiemannResearch.Analysis.FiniteHarmonicBounds

/-!
# Unconditional reciprocal and harmonic source floors for screened split energies

Source: the user's October 1 audit continuation and the previously verified
factorialPrimeDefect_normalized_lower. The finite floors require neither PNT
nor any slope separation assumption. The stronger harmonic floor assembles
factorialPrimeSourceEnergy_ge_adjacent_harmonic from the concurrently
published eb1d817 adjacent-conductor development; this source supports the
pointwise bound, not a signed gap estimate. PNT/Dusart consequences are discussed
separately in FirstSiteMultiscaleSourceAudit20261001.md.

The harmonic reduced floor retains unequal child budgets and every actual
signed screened slope. Nonsummability of that actual energy remains Open.
-/

noncomputable section
open Filter
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.WeightedScalarEnergy
open RiemannResearch.RH.Pareto.IntegerDPP

/-- Per-row source floor, with the actual prime indicator. -/
def reciprocalPrimeSourceFloor (n : ℕ) : ℝ :=
  if Nat.Prime (n+3) then 1 / (8 * ((n+3 : ℕ) : ℝ)) else 0

/-- Complete finite reciprocal-prime mass of the block. -/
def reciprocalPrimeBlockSourceFloor (N k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, reciprocalPrimeSourceFloor (N+i)

theorem reciprocalPrimeSourceFloor_nonneg (n : ℕ) :
    0 ≤ reciprocalPrimeSourceFloor n := by
  unfold reciprocalPrimeSourceFloor
  split_ifs <;> positivity

theorem reciprocalPrimeSourceFloor_le (n : ℕ) :
    reciprocalPrimeSourceFloor n ≤
      primeSchurWeight n * (factorialPrimeDelta n)^2 := by
  by_cases hp : Nat.Prime (n+3)
  · rw [reciprocalPrimeSourceFloor, if_pos hp]
    simpa [primeSchurWeight, hp, factorialPrimeDelta, div_eq_mul_inv,
      mul_comm, Nat.add_assoc] using
      factorialPrimeDefect_normalized_lower (n+1) (by omega)
  · simp [reciprocalPrimeSourceFloor, primeSchurWeight, hp]

theorem reciprocalPrimeBlockSourceFloor_nonneg (N k : ℕ) :
    0 ≤ reciprocalPrimeBlockSourceFloor N k :=
  Finset.sum_nonneg (fun i _ => reciprocalPrimeSourceFloor_nonneg (N+i))

theorem reciprocalPrimeBlockSourceFloor_le (N k : ℕ) :
    reciprocalPrimeBlockSourceFloor N k ≤ primeBlockSource N k := by
  unfold reciprocalPrimeBlockSourceFloor primeBlockSource square
  exact Finset.sum_le_sum (fun i _ => reciprocalPrimeSourceFloor_le (N+i))

/-- A finite counting bridge: all primes are retained, and the denominator
uses the largest possible prime modulus in the block. -/
theorem reciprocalPrimeBlockSourceFloor_ge_count (N k : ℕ) :
    (∑ i ∈ Finset.range k, if Nat.Prime (N+i+3) then (1:ℝ) else 0) /
      (8 * ((N+k+2 : ℕ) : ℝ)) ≤ reciprocalPrimeBlockSourceFloor N k := by
  rw [Finset.sum_div]
  unfold reciprocalPrimeBlockSourceFloor
  apply Finset.sum_le_sum
  intro i hi
  have hi' := Finset.mem_range.mp hi
  by_cases hp : Nat.Prime (N+i+3)
  · simp only [hp, if_true, reciprocalPrimeSourceFloor]
    apply one_div_le_one_div_of_le (by positivity)
    have hidx : N+i+3 ≤ N+k+2 := by omega
    have hc : ((N+i+3 : ℕ) : ℝ) ≤ ((N+k+2 : ℕ) : ℝ) := by exact_mod_cast hidx
    exact mul_le_mul_of_nonneg_left hc (by norm_num)
  · simp [reciprocalPrimeSourceFloor, hp]

/-- A concrete common lower source witness for the original split endpoint. -/
def dyadicSplitSourceFloor (j : ℕ) : ℝ :=
  min (reciprocalPrimeBlockSourceFloor (2^(j+1)) (2^j))
    (reciprocalPrimeBlockSourceFloor (2^(j+1)+2^j) (2^j))

theorem dyadicSplitSourceFloor_nonneg (j : ℕ) : 0 ≤ dyadicSplitSourceFloor j :=
  le_min (reciprocalPrimeBlockSourceFloor_nonneg _ _)
    (reciprocalPrimeBlockSourceFloor_nonneg _ _)

theorem dyadicSplitSourceFloor_le_left (j : ℕ) :
    dyadicSplitSourceFloor j ≤ primeBlockSource (2^(j+1)) (2^j) :=
  (min_le_left _ _).trans (reciprocalPrimeBlockSourceFloor_le _ _)

theorem dyadicSplitSourceFloor_le_right (j : ℕ) :
    dyadicSplitSourceFloor j ≤ primeBlockSource (2^(j+1)+2^j) (2^j) :=
  (min_le_right _ _).trans (reciprocalPrimeBlockSourceFloor_le _ _)

/-- Reduced floor preserving unequal source mass instead of replacing it
by half the smaller child budget. Zero-source children contribute zero. -/
def reciprocalPrimeSplitWeight (N k l : ℕ) : ℝ :=
  reciprocalPrimeBlockSourceFloor N k * reciprocalPrimeBlockSourceFloor (N+k) l /
    (reciprocalPrimeBlockSourceFloor N k + reciprocalPrimeBlockSourceFloor (N+k) l)

/-- The actual complete screened slope gap, weighted by a proved source floor. -/
def reciprocalPrimeSplitEnergy (N k l : ℕ) : ℝ :=
  reciprocalPrimeSplitWeight N k l *
    (primeBlockCross (N+k) l / primeBlockSource (N+k) l -
      primeBlockCross N k / primeBlockSource N k)^2

theorem reciprocalPrimeSplitWeight_nonneg (N k l : ℕ) :
    0 ≤ reciprocalPrimeSplitWeight N k l := by
  unfold reciprocalPrimeSplitWeight
  exact div_nonneg
    (mul_nonneg (reciprocalPrimeBlockSourceFloor_nonneg _ _)
      (reciprocalPrimeBlockSourceFloor_nonneg _ _))
    (add_nonneg (reciprocalPrimeBlockSourceFloor_nonneg _ _)
      (reciprocalPrimeBlockSourceFloor_nonneg _ _))

theorem reciprocalPrimeSplitEnergy_nonneg (N k l : ℕ) :
    0 ≤ reciprocalPrimeSplitEnergy N k l :=
  mul_nonneg (reciprocalPrimeSplitWeight_nonneg _ _ _) (sq_nonneg _)

theorem reciprocalPrimeSplitEnergy_le_splitDrift (N k l : ℕ) :
    reciprocalPrimeSplitEnergy N k l ≤ primeBlockSplitDrift N k l := by
  unfold reciprocalPrimeSplitEnergy reciprocalPrimeSplitWeight primeBlockSplitDrift
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact reduced_weight_mono _ _ _ _
    (reciprocalPrimeBlockSourceFloor_nonneg _ _)
    (reciprocalPrimeBlockSourceFloor_nonneg _ _)
    (reciprocalPrimeBlockSourceFloor_le _ _)
    (reciprocalPrimeBlockSourceFloor_le _ _)

theorem reciprocalPrimeSplitEnergy_le_variance (N k l : ℕ) :
    reciprocalPrimeSplitEnergy N k l ≤ primeBlockVariance N (k+l) := by
  rw [primeBlockVariance_split]
  have h := reciprocalPrimeSplitEnergy_le_splitDrift N k l
  linarith [primeBlockVariance_nonneg N k, primeBlockVariance_nonneg (N+k) l]

/-- CONDITIONAL RESEARCH REDUCTION. Source nonnegativity and both source
comparisons are proved; actual screened-gap energy divergence remains Open. -/
theorem riemannHypothesis_of_reciprocalPrimeSplitEnergy_not_summable
    (hdiv : ¬ Summable (fun j =>
      reciprocalPrimeSplitEnergy (2^(j+1)) (2^j) (2^j))) : RiemannHypothesis := by
  apply riemannHypothesis_of_dyadic_prime_block_variance
  intro hs
  have ht : Summable (fun j => primeBlockVariance (2^(j+1)) (2^(j+1))) :=
    (summable_nat_add_iff (f := fun j : ℕ => primeBlockVariance (2^j) (2^j)) 1).mpr hs
  apply hdiv
  apply ht.of_nonneg_of_le
  · intro j
    exact reciprocalPrimeSplitEnergy_nonneg _ _ _
  · intro j
    have hh := reciprocalPrimeSplitEnergy_le_variance (2^(j+1)) (2^j) (2^j)
    have hp : (2:ℕ)^j + 2^j = 2^(j+1) := by rw [pow_succ]; omega
    simpa only [hp] using hh

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity

/-!
# Unconditional reciprocal-prime source floors for screened split energies

Source: the user's October 1 audit continuation and the previously verified
factorialPrimeDefect_normalized_lower. The finite floors require neither PNT
nor any slope separation assumption. PNT/Dusart consequences are discussed
separately in FirstSiteMultiscaleSourceAudit20261001.md.

The harmonic reduced floor retains unequal child budgets and every actual
signed screened slope. Nonsummability of that actual energy remains Open.
-/

noncomputable section
open Filter
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.WeightedScalarEnergy
open RiemannResearch.Analysis
open RiemannResearch.RH.Pareto.IntegerDPP

/-- Per-row source floor, with the actual prime indicator. -/
def harmonicPrimeSourceFloor (n : ℕ) : ℝ :=
  if Nat.Prime (n+3) then 1 / (4 * (harmonic (n+2) : ℝ)) else 0

/-- Complete finite harmonic-prime mass of the block. -/
def harmonicPrimeBlockSourceFloor (N k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, harmonicPrimeSourceFloor (N+i)

theorem harmonicPrimeSourceFloor_nonneg (n : ℕ) :
    0 ≤ harmonicPrimeSourceFloor n := by
  unfold harmonicPrimeSourceFloor
  split_ifs
  · exact div_nonneg (by norm_num) (mul_nonneg (by norm_num) (harmonic_nonnegative _))
  · exact le_rfl

theorem harmonicPrimeSourceFloor_le (n : ℕ) :
    harmonicPrimeSourceFloor n ≤
      primeSchurWeight n * (factorialPrimeDelta n)^2 := by
  by_cases hp : Nat.Prime (n+3)
  · rw [harmonicPrimeSourceFloor, if_pos hp]
    simpa [factorialPrimeSourceEnergy, primeSchurWeight, hp, factorialPrimeDelta,
      div_eq_mul_inv, mul_comm, Nat.add_assoc] using
      factorialPrimeSourceEnergy_ge_adjacent_harmonic n hp
  · simp [harmonicPrimeSourceFloor, primeSchurWeight, hp]

theorem harmonicPrimeBlockSourceFloor_nonneg (N k : ℕ) :
    0 ≤ harmonicPrimeBlockSourceFloor N k :=
  Finset.sum_nonneg (fun i _ => harmonicPrimeSourceFloor_nonneg (N+i))

theorem harmonicPrimeBlockSourceFloor_le (N k : ℕ) :
    harmonicPrimeBlockSourceFloor N k ≤ primeBlockSource N k := by
  unfold harmonicPrimeBlockSourceFloor primeBlockSource square
  exact Finset.sum_le_sum (fun i _ => harmonicPrimeSourceFloor_le (N+i))

/-- A finite counting bridge: all primes are retained, and the denominator
uses the largest possible harmonic index in the block. -/
theorem harmonicPrimeBlockSourceFloor_ge_count (N k : ℕ) :
    (∑ i ∈ Finset.range k, if Nat.Prime (N+i+3) then (1:ℝ) else 0) /
      (4 * (harmonic (N+k+1) : ℝ)) ≤ harmonicPrimeBlockSourceFloor N k := by
  rw [Finset.sum_div]
  unfold harmonicPrimeBlockSourceFloor
  apply Finset.sum_le_sum
  intro i hi
  have hi' := Finset.mem_range.mp hi
  by_cases hp : Nat.Prime (N+i+3)
  · simp only [hp, if_true, harmonicPrimeSourceFloor]
    have hh := (harmonic_interval_bounds 1 (N+i+2) (by omega)).1
    have h1 : (harmonic 1 : ℝ) = 1 := by norm_num
    rw [h1] at hh
    apply one_div_le_one_div_of_le (by linarith)
    have hm := (harmonic_interval_bounds (N+i+2) (N+k+1) (by omega)).1
    linarith
  · simp [harmonicPrimeSourceFloor, hp]

/-- A concrete common lower source witness for the original split endpoint. -/
def dyadicHarmonicSplitSourceFloor (j : ℕ) : ℝ :=
  min (harmonicPrimeBlockSourceFloor (2^(j+1)) (2^j))
    (harmonicPrimeBlockSourceFloor (2^(j+1)+2^j) (2^j))

theorem dyadicHarmonicSplitSourceFloor_nonneg (j : ℕ) : 0 ≤ dyadicHarmonicSplitSourceFloor j :=
  le_min (harmonicPrimeBlockSourceFloor_nonneg _ _)
    (harmonicPrimeBlockSourceFloor_nonneg _ _)

theorem dyadicHarmonicSplitSourceFloor_le_left (j : ℕ) :
    dyadicHarmonicSplitSourceFloor j ≤ primeBlockSource (2^(j+1)) (2^j) :=
  (min_le_left _ _).trans (harmonicPrimeBlockSourceFloor_le _ _)

theorem dyadicHarmonicSplitSourceFloor_le_right (j : ℕ) :
    dyadicHarmonicSplitSourceFloor j ≤ primeBlockSource (2^(j+1)+2^j) (2^j) :=
  (min_le_right _ _).trans (harmonicPrimeBlockSourceFloor_le _ _)

/-- Reduced floor preserving unequal source mass instead of replacing it
by half the smaller child budget. Zero-source children contribute zero. -/
def harmonicPrimeSplitWeight (N k l : ℕ) : ℝ :=
  harmonicPrimeBlockSourceFloor N k * harmonicPrimeBlockSourceFloor (N+k) l /
    (harmonicPrimeBlockSourceFloor N k + harmonicPrimeBlockSourceFloor (N+k) l)

/-- The actual complete screened slope gap, weighted by a proved source floor. -/
def harmonicPrimeSplitEnergy (N k l : ℕ) : ℝ :=
  harmonicPrimeSplitWeight N k l *
    (primeBlockCross (N+k) l / primeBlockSource (N+k) l -
      primeBlockCross N k / primeBlockSource N k)^2

theorem harmonicPrimeSplitWeight_nonneg (N k l : ℕ) :
    0 ≤ harmonicPrimeSplitWeight N k l := by
  unfold harmonicPrimeSplitWeight
  exact div_nonneg
    (mul_nonneg (harmonicPrimeBlockSourceFloor_nonneg _ _)
      (harmonicPrimeBlockSourceFloor_nonneg _ _))
    (add_nonneg (harmonicPrimeBlockSourceFloor_nonneg _ _)
      (harmonicPrimeBlockSourceFloor_nonneg _ _))

theorem harmonicPrimeSplitEnergy_nonneg (N k l : ℕ) :
    0 ≤ harmonicPrimeSplitEnergy N k l :=
  mul_nonneg (harmonicPrimeSplitWeight_nonneg _ _ _) (sq_nonneg _)

theorem harmonicPrimeSplitEnergy_le_splitDrift (N k l : ℕ) :
    harmonicPrimeSplitEnergy N k l ≤ primeBlockSplitDrift N k l := by
  unfold harmonicPrimeSplitEnergy harmonicPrimeSplitWeight primeBlockSplitDrift
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact reduced_weight_mono _ _ _ _
    (harmonicPrimeBlockSourceFloor_nonneg _ _)
    (harmonicPrimeBlockSourceFloor_nonneg _ _)
    (harmonicPrimeBlockSourceFloor_le _ _)
    (harmonicPrimeBlockSourceFloor_le _ _)

theorem harmonicPrimeSplitEnergy_le_variance (N k l : ℕ) :
    harmonicPrimeSplitEnergy N k l ≤ primeBlockVariance N (k+l) := by
  rw [primeBlockVariance_split]
  have h := harmonicPrimeSplitEnergy_le_splitDrift N k l
  linarith [primeBlockVariance_nonneg N k, primeBlockVariance_nonneg (N+k) l]

/-- The newer adjacent harmonic floor dominates the earlier reciprocal floor. -/
theorem reciprocalPrimeSourceFloor_le_harmonic (n : ℕ) :
    reciprocalPrimeSourceFloor n ≤ harmonicPrimeSourceFloor n := by
  by_cases hp : Nat.Prime (n+3)
  · simp only [reciprocalPrimeSourceFloor, harmonicPrimeSourceFloor, hp, if_true]
    have hh := (harmonic_interval_bounds 1 (n+2) (by omega)).1
    have h1 : (harmonic 1 : ℝ) = 1 := by norm_num
    rw [h1] at hh
    apply one_div_le_one_div_of_le (by linarith)
    have hi := harmonic_le_index (n+2)
    push_cast at hi ⊢
    linarith [Nat.cast_nonneg (α := ℝ) n]
  · simp [reciprocalPrimeSourceFloor, harmonicPrimeSourceFloor, hp]

theorem reciprocalPrimeBlockSourceFloor_le_harmonic (N k : ℕ) :
    reciprocalPrimeBlockSourceFloor N k ≤ harmonicPrimeBlockSourceFloor N k :=
  Finset.sum_le_sum (fun i _ => reciprocalPrimeSourceFloor_le_harmonic (N+i))

/-- The comparison uses the identical actual signed screened slope gap. -/
theorem reciprocalPrimeSplitEnergy_le_harmonic (N k l : ℕ) :
    reciprocalPrimeSplitEnergy N k l ≤ harmonicPrimeSplitEnergy N k l := by
  unfold reciprocalPrimeSplitEnergy reciprocalPrimeSplitWeight
    harmonicPrimeSplitEnergy harmonicPrimeSplitWeight
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact reduced_weight_mono _ _ _ _
    (reciprocalPrimeBlockSourceFloor_nonneg _ _)
    (reciprocalPrimeBlockSourceFloor_nonneg _ _)
    (reciprocalPrimeBlockSourceFloor_le_harmonic _ _)
    (reciprocalPrimeBlockSourceFloor_le_harmonic _ _)

/-- CONDITIONAL RESEARCH REDUCTION. Source nonnegativity and both source
comparisons are proved; actual screened-gap energy divergence remains Open. -/
theorem riemannHypothesis_of_harmonicPrimeSplitEnergy_not_summable
    (hdiv : ¬ Summable (fun j =>
      harmonicPrimeSplitEnergy (2^(j+1)) (2^j) (2^j))) : RiemannHypothesis := by
  apply riemannHypothesis_of_dyadic_prime_block_variance
  intro hs
  have ht : Summable (fun j => primeBlockVariance (2^(j+1)) (2^(j+1))) :=
    (summable_nat_add_iff (f := fun j : ℕ => primeBlockVariance (2^j) (2^j)) 1).mpr hs
  apply hdiv
  apply ht.of_nonneg_of_le
  · intro j
    exact harmonicPrimeSplitEnergy_nonneg _ _ _
  · intro j
    have hh := harmonicPrimeSplitEnergy_le_variance (2^(j+1)) (2^j) (2^j)
    have hp : (2:ℕ)^j + 2^j = 2^(j+1) := by rw [pow_succ]; omega
    simpa only [hp] using hh

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
