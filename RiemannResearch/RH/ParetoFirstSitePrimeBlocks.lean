/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoFirstSitePrimeAngular

/-!
# Exact fully weighted prime-block scatter and two-row certificates

Source: the user's 2026-09-30 continuation after the Kolmogorov three-series
bridge, developed using elementary weighted regression and finite telescoping.
These support the statements and proof strategy, not a novel arithmetic
divergence claim.

Each block retains the actual Schur pivots, factorial source, complete signed
screened CRT correction and mean mismatch square. Internal scatter can be
bounded below by two complete rows without the historical running slope.
An exact dyadic summability equivalence also keeps the mean drift channel.

No arithmetic nonsummability provider or unconditional RH is asserted.
The complete capacity formula retains its initial value and all nonprime
gains; no physical tail or Gram cross term is removed by these equalities.
-/

noncomputable section
open Filter
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.WeightedScalarEnergy
open RiemannResearch.RH.Pareto.IntegerDPP

def primeBlockSource (N k : ℕ) : ℝ :=
  square (Finset.range k) (fun i => primeSchurWeight (N+i))
    (fun i => factorialPrimeDelta (N+i))
def primeBlockError (N k : ℕ) : ℝ :=
  square (Finset.range k) (fun i => primeSchurWeight (N+i))
    (fun i => factorialPrimeError (N+i))
def primeBlockCross (N k : ℕ) : ℝ :=
  product (Finset.range k) (fun i => primeSchurWeight (N+i))
    (fun i => factorialPrimeDelta (N+i)) (fun i => factorialPrimeError (N+i))

/-- Full internal scatter at the block's own optimal slope. -/
def primeBlockVariance (N k : ℕ) : ℝ :=
  square (Finset.range k) (fun i => primeSchurWeight (N+i))
    (fun i => factorialPrimeError (N+i) -
      (primeBlockCross N k / primeBlockSource N k) * factorialPrimeDelta (N+i))

/-- The exact head--block mean mismatch, including the reduced source weight. -/
def primeBlockMeanDrift (N k : ℕ) : ℝ :=
  primeSourceBudget N * primeBlockSource N k /
    (primeSourceBudget N + primeBlockSource N k) *
      (primeBlockCross N k / primeBlockSource N k -
        primeCrossBudget N / primeSourceBudget N) ^ 2

def primeAngularBlock (N k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, primeAngularInnovation (N+i)


/-- Fully weighted separation of two complete screened rows. -/
def primeTwoRowSeparation (m n : ℕ) : ℝ :=
  primeSchurWeight m * primeSchurWeight n *
    (factorialPrimeDelta m * factorialPrimeError n -
      factorialPrimeDelta n * factorialPrimeError m)^2 /
    (primeSchurWeight m * (factorialPrimeDelta m)^2 +
      primeSchurWeight n * (factorialPrimeDelta n)^2)

theorem primeTwoRowSeparation_nonneg (m n : ℕ) : 0 ≤ primeTwoRowSeparation m n := by
  unfold primeTwoRowSeparation
  exact div_nonneg
    (mul_nonneg (mul_nonneg (primeSchurWeight_nonneg m) (primeSchurWeight_nonneg n))
      (sq_nonneg _))
    (add_nonneg (mul_nonneg (primeSchurWeight_nonneg m) (sq_nonneg _))
      (mul_nonneg (primeSchurWeight_nonneg n) (sq_nonneg _)))

theorem primeBlockSource_nonneg (N k : ℕ) : 0 ≤ primeBlockSource N k :=
  square_nonneg _ _ _ (fun i _ => primeSchurWeight_nonneg (N+i))

theorem primeBlockVariance_nonneg (N k : ℕ) : 0 ≤ primeBlockVariance N k :=
  square_nonneg _ _ _ (fun i _ => primeSchurWeight_nonneg (N+i))

theorem primeBlockMeanDrift_nonneg (N k : ℕ) : 0 ≤ primeBlockMeanDrift N k := by
  unfold primeBlockMeanDrift
  exact mul_nonneg
    (div_nonneg (mul_nonneg (primeSourceBudget_nonneg N) (primeBlockSource_nonneg N k))
      (add_nonneg (primeSourceBudget_nonneg N) (primeBlockSource_nonneg N k)))
    (sq_nonneg _)

theorem primeBlock_gram (N k : ℕ) :
    (primeBlockCross N k)^2 ≤ primeBlockSource N k * primeBlockError N k :=
  gram_nonneg _ _ _ _ (fun i _ => primeSchurWeight_nonneg (N+i))

theorem primeBlockVariance_eq_quotient (N k : ℕ) :
    primeBlockVariance N k =
      primeBlockError N k - (primeBlockCross N k)^2 / primeBlockSource N k := by
  exact centered_square_eq_sub_quotient _ _ _ _

theorem primeSourceBudget_add_block (N k : ℕ) :
    primeSourceBudget (N+k) = primeSourceBudget N + primeBlockSource N k := by
  simp only [primeSourceBudget_eq_weighted, primeBlockSource, square, Finset.sum_range_add]

theorem primeErrorBudget_add_block (N k : ℕ) :
    primeErrorBudget (N+k) = primeErrorBudget N + primeBlockError N k := by
  simp only [primeErrorBudget_eq_weighted, primeBlockError, square, Finset.sum_range_add]

theorem primeCrossBudget_add_block (N k : ℕ) :
    primeCrossBudget (N+k) = primeCrossBudget N + primeBlockCross N k := by
  simp only [primeCrossBudget_eq_weighted, primeBlockCross, product, Finset.sum_range_add]

theorem primeAngularBlock_eq_variance_step (N k : ℕ) :
    primeAngularBlock N k = primeCancellationVariance (N+k) - primeCancellationVariance N := by
  rw [primeCancellationVariance_eq_sum, primeCancellationVariance_eq_sum]
  simp [primeAngularBlock, Finset.sum_range_add]

/-- Exact block equality. No prime cross term or Schur weight is replaced. -/
theorem primeAngularBlock_eq_variance_add_drift (N k : ℕ) (hN : 0 < N) :
    primeAngularBlock N k = primeBlockVariance N k + primeBlockMeanDrift N k := by
  have hU := ne_of_gt (primeSourceBudget_pos N hN)
  rw [primeAngularBlock_eq_variance_step,
    primeCancellationVariance_eq_quotient (N+k) (by omega),
    primeCancellationVariance_eq_quotient N hN,
    primeSourceBudget_add_block, primeErrorBudget_add_block, primeCrossBudget_add_block,
    primeBlockVariance_eq_quotient]
  by_cases hu : primeBlockSource N k = 0
  · have hx : primeBlockCross N k = 0 := by
      have hg := primeBlock_gram N k
      rw [hu, zero_mul] at hg
      nlinarith [sq_nonneg (primeBlockCross N k)]
    simp [primeBlockMeanDrift, hu, hx]
  · have hSum : primeSourceBudget N + primeBlockSource N k ≠ 0 :=
      ne_of_gt (add_pos_of_pos_of_nonneg (primeSourceBudget_pos N hN)
        (primeBlockSource_nonneg N k))
    have he := centered_energy_merge (primeSourceBudget N) (primeErrorBudget N)
      (primeCrossBudget N) (primeBlockSource N k) (primeBlockError N k)
      (primeBlockCross N k) hU hu hSum
    unfold primeBlockMeanDrift
    linarith

/-- The only discarded term is the explicit nonnegative mean drift square. -/
theorem primeBlockVariance_le_angular (N k : ℕ) (hN : 0 < N) :
    primeBlockVariance N k ≤ primeAngularBlock N k := by
  rw [primeAngularBlock_eq_variance_add_drift N k hN]
  exact le_add_of_nonneg_right (primeBlockMeanDrift_nonneg N k)

/-- All ordered pairs, with the complete screened determinant. -/
theorem primeBlockVariance_eq_pair (N k : ℕ) (hu : 0 < primeBlockSource N k) :
    primeBlockVariance N k =
      (∑ i ∈ Finset.range k, ∑ j ∈ Finset.range k,
        primeSchurWeight (N+i) * primeSchurWeight (N+j) *
          (factorialPrimeDelta (N+i) * factorialPrimeError (N+j) -
            factorialPrimeDelta (N+j) * factorialPrimeError (N+i))^2) /
      (2 * primeBlockSource N k) := by
  rw [pair_identity, primeBlockVariance_eq_quotient]
  change primeBlockError N k - (primeBlockCross N k)^2 / primeBlockSource N k =
    2 * (primeBlockSource N k * primeBlockError N k - (primeBlockCross N k)^2) /
      (2 * primeBlockSource N k)
  field_simp [ne_of_gt hu]


/-- The aligned negative source cancels exactly, leaving the complete actual
Schur survivor scatter; this supplies no lower bound on that scatter. -/
theorem primeBlockVariance_eq_survivor_scatter (N k : ℕ) :
    primeBlockVariance N k =
      square (Finset.range k) (fun i => primeSchurWeight (N+i))
        (fun i => schurEta (N+i+1) -
          (1+primeBlockCross N k / primeBlockSource N k) * factorialPrimeDelta (N+i)) := by
  unfold primeBlockVariance square
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only
  by_cases hp : Nat.Prime (N+i+3)
  · have he : schurEta (N+i+1) =
        factorialPrimeDelta (N+i) + factorialPrimeError (N+i) := by
      simpa only [factorialPrimeDelta] using factorialPrimeError_decomposition (N+i) hp
    rw [he]
    ring
  · simp [primeSchurWeight, hp]

/-- Concrete fully weighted pair certificate for any two distinct block rows.
A nonprime row has zero weight, so no primality assumption is hidden. -/
theorem primeBlockVariance_ge_two_rows (N k i j : ℕ)
    (hi : i < k) (hj : j < k) (hij : i ≠ j) :
    primeTwoRowSeparation (N+i) (N+j) ≤ primeBlockVariance N k := by
  exact two_row_determinant_le_square (Finset.range k)
    (fun q => primeSchurWeight (N+q)) (fun q => factorialPrimeDelta (N+q))
    (fun q => factorialPrimeError (N+q)) (primeBlockCross N k / primeBlockSource N k)
    (fun q _ => primeSchurWeight_nonneg (N+q)) i j
    (Finset.mem_range.mpr hi) (Finset.mem_range.mpr hj) hij

theorem dyadic_primeAngularBlock_sum (J : ℕ) :
    (∑ j ∈ Finset.range J, primeAngularBlock (2^j) (2^j)) =
      primeCancellationVariance (2^J) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih, primeAngularBlock_eq_variance_step]
    have he : (2:ℕ)^(J+1) = 2^J + 2^J := by rw [pow_succ]; omega
    rw [he]
    ring


/-- Any nonsummable nonnegative block lower bound supplies the full angular
provider; the actual block comparison is retained as a hypothesis. -/
theorem primeAngularInnovation_not_summable_of_dyadic_lower (b : ℕ → ℝ)
    (hb : ∀ j, 0 ≤ b j) (hdiv : ¬ Summable b)
    (hlower : ∀ j, b j ≤ primeAngularBlock (2^j) (2^j)) :
    ¬ Summable primeAngularInnovation := by
  intro hs
  have ht := (not_summable_iff_tendsto_nat_atTop_of_nonneg hb).mp hdiv
  obtain ⟨J, hJ⟩ := eventually_atTop.mp
    ((tendsto_atTop.mp ht) ((∑' n, primeAngularInnovation n) + 1))
  have hlow := hJ J le_rfl
  have hle : (∑ j ∈ Finset.range J, b j) ≤
      ∑ j ∈ Finset.range J, primeAngularBlock (2^j) (2^j) :=
    Finset.sum_le_sum (fun j _ => hlower j)
  rw [dyadic_primeAngularBlock_sum, primeCancellationVariance_eq_sum] at hle
  have hupper := hs.sum_le_tsum (Finset.range (2^J))
    (fun n _ => primeAngularInnovation_nonneg n)
  linarith

/-- Internal block scatter can be tested without the historical running slope.
Its actual nonsummability remains an explicit Open provider. -/
theorem primeAngularInnovation_not_summable_of_dyadic_block_variance
    (h : ¬ Summable (fun j => primeBlockVariance (2^j) (2^j))) :
    ¬ Summable primeAngularInnovation :=
  primeAngularInnovation_not_summable_of_dyadic_lower _
    (fun j => primeBlockVariance_nonneg _ _) h
    (fun j => primeBlockVariance_le_angular _ _ (by positivity))

/-- Exact summability alternative. The head--block drift is retained, so
internal scatter alone is not asserted necessary for angular divergence. -/
theorem primeAngularInnovation_summable_iff_dyadic_blocks :
    Summable primeAngularInnovation ↔
      Summable (fun j => primeBlockVariance (2^j) (2^j)) ∧
        Summable (fun j => primeBlockMeanDrift (2^j) (2^j)) := by
  constructor
  · intro hs
    constructor
    · by_contra hv
      exact primeAngularInnovation_not_summable_of_dyadic_block_variance hv hs
    · by_contra hd
      apply primeAngularInnovation_not_summable_of_dyadic_lower
        (fun j => primeBlockMeanDrift (2^j) (2^j))
        (fun j => primeBlockMeanDrift_nonneg _ _) hd ?_ hs
      intro j
      rw [primeAngularBlock_eq_variance_add_drift _ _ (by positivity)]
      exact le_add_of_nonneg_left (primeBlockVariance_nonneg _ _)
  · rintro ⟨hv, hd⟩
    by_contra hs
    have ht := (not_summable_iff_tendsto_nat_atTop_of_nonneg
      primeAngularInnovation_nonneg).mp hs
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_atTop.mp ht)
      ((∑' j, primeBlockVariance (2^j) (2^j)) +
        (∑' j, primeBlockMeanDrift (2^j) (2^j)) + 1))
    have hhigh := hN N le_rfl
    rw [← primeCancellationVariance_eq_sum] at hhigh
    have hpow : ∀ n : ℕ, n < (2:ℕ)^n := by
      intro n
      induction n with
      | zero => norm_num
      | succ n ih =>
        rw [pow_succ]
        have hp : 0 < (2:ℕ)^n := by positivity
        omega
    have hmono := primeCancellationVariance_monotone (Nat.le_of_lt (hpow N))
    have he : (∑ j ∈ Finset.range N, primeAngularBlock (2^j) (2^j)) =
        (∑ j ∈ Finset.range N, primeBlockVariance (2^j) (2^j)) +
          ∑ j ∈ Finset.range N, primeBlockMeanDrift (2^j) (2^j) := by
      have hb (j : ℕ) := primeAngularBlock_eq_variance_add_drift (2^j) (2^j)
        (by positivity : 0 < (2:ℕ)^j)
      simp_rw [hb, Finset.sum_add_distrib]
    rw [← dyadic_primeAngularBlock_sum N, he] at hmono
    have hv' := hv.sum_le_tsum (Finset.range N) (fun j _ => primeBlockVariance_nonneg _ _)
    have hd' := hd.sum_le_tsum (Finset.range N) (fun j _ => primeBlockMeanDrift_nonneg _ _)
    linarith

/-- Complete first-site alternative, with both exact block channels and every
nonprime gain retained. None of the divergence conditions is supplied here. -/
theorem tailCapacity_tendsto_iff_dyadic_prime_block_channels :
    Tendsto tailCapacity atTop atTop ↔
      (¬ Tendsto primeMeanMismatchBudget atTop (nhds 0)) ∨
        (¬ Summable (fun j => primeBlockVariance (2^j) (2^j))) ∨
        (¬ Summable (fun j => primeBlockMeanDrift (2^j) (2^j))) ∨
        (¬ Summable factorialCompositeGain) := by
  rw [tailCapacity_tendsto_iff_prime_angular_channels,
    primeAngularInnovation_summable_iff_dyadic_blocks]
  simp only [not_and_or, or_assoc]

theorem riemannHypothesis_of_dyadic_prime_block_variance
    (h : ¬ Summable (fun j => primeBlockVariance (2^j) (2^j))) : RiemannHypothesis :=
  riemannHypothesis_of_primeAngularInnovation_not_summable
    (primeAngularInnovation_not_summable_of_dyadic_block_variance h)

/-- Quantitative block lower bounds may tend to zero. Their nonsummability
and their comparison with the actual weighted block scatter are Open. -/
theorem riemannHypothesis_of_dyadic_prime_block_lower_bound (b : ℕ → ℝ)
    (hb : ∀ j, 0 ≤ b j) (hdiv : ¬ Summable b)
    (hlower : ∀ j, b j ≤ primeBlockVariance (2^j) (2^j)) : RiemannHypothesis := by
  apply riemannHypothesis_of_dyadic_prime_block_variance
  intro hs
  exact hdiv (hs.of_nonneg_of_le hb hlower)


/-- Exact dyadic capacity accounting, preserving initial capacity, the mean
channel, both block channels, and every nonprime gain. -/
theorem capacity_eq_dyadic_prime_block_budget (J : ℕ) :
    tailCapacity (2^J+1) = tailCapacity 1 + primeMeanMismatchBudget (2^J) +
      (∑ j ∈ Finset.range J, primeBlockVariance (2^j) (2^j)) +
      (∑ j ∈ Finset.range J, primeBlockMeanDrift (2^j) (2^j)) +
      compositeGainBudget (2^J) := by
  rw [capacity_eq_prime_alignment_budget _ (by positivity),
    ← dyadic_primeAngularBlock_sum J]
  have hb (j : ℕ) := primeAngularBlock_eq_variance_add_drift (2^j) (2^j)
    (by positivity : 0 < (2:ℕ)^j)
  simp_rw [hb, Finset.sum_add_distrib]
  ring

/-- Conditional arithmetic endpoint using only fully weighted two-row
separations. The first one-row dyadic block is omitted; its energy is finite.
Nonsummability of these actual determinants is the sole Open growth provider. -/
theorem riemannHypothesis_of_dyadic_prime_pair_separation (i j : ℕ → ℕ)
    (hi : ∀ r, i r < 2^(r+1)) (hj : ∀ r, j r < 2^(r+1))
    (hij : ∀ r, i r ≠ j r)
    (hdiv : ¬ Summable (fun r =>
      primeTwoRowSeparation (2^(r+1)+i r) (2^(r+1)+j r))) : RiemannHypothesis := by
  apply riemannHypothesis_of_dyadic_prime_block_variance
  intro hs
  have hshift : Summable (fun r => primeBlockVariance (2^(r+1)) (2^(r+1))) :=
    (summable_nat_add_iff
      (f := fun r : ℕ => primeBlockVariance (2^r) (2^r)) 1).mpr hs
  exact hdiv (hshift.of_nonneg_of_le
    (fun r => primeTwoRowSeparation_nonneg _ _)
    (fun r => primeBlockVariance_ge_two_rows _ _ _ _ (hi r) (hj r) (hij r)))

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
