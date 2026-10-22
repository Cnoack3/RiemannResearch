import RiemannResearch.RH.ParetoFirstSitePrimeBudget
import RiemannResearch.RH.ParetoPrimeCrossStageCancellation
import RiemannResearch.Analysis.WeightedScalarEnergy

/-!
# Exact prime alignment and fluctuation-scale first-site providers

Source: the user continuation from 2e18190a98441778f47d5fdf7542e73bc5d68868
(2026-09-30), combined with finite weighted Lagrange square completion and
finite-head/tail Cauchy--Schwarz. These support the statement and proof strategy.

The actual factorial/CRT source and signed screened correction are retained.
The exact capacity split consists of mean mismatch, centered error variance,
and every nonprime Schur gain, with the initial capacity present. The variance
is also the full ordered-pair determinant square.

Bounded capacity forces both the mean mismatch and error/source mismatch to
vanish on the source-fluctuation scale. Consequently a cofinal fixed positive
mean mismatch, or an error saving c*sqrt(U), suffices for the first-site
provider. The displayed arithmetic lower bounds remain explicitly OPEN.
This module establishes no unconditional capacity divergence or RH.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.RH.Pareto.IntegerDPP
open RiemannResearch.Analysis.WeightedScalarEnergy

/-- The complete prime Schur weight; the actual pivot is never replaced. -/
def primeSchurWeight (n : ℕ) : ℝ :=
  if Nat.Prime (n+3) then (schurSigma (n+1))⁻¹ else 0

theorem primeSchurWeight_nonneg (n : ℕ) : 0 ≤ primeSchurWeight n := by
  unfold primeSchurWeight
  split_ifs
  · exact inv_nonneg.mpr (schurSigma_pos _).le
  · exact le_rfl

theorem primeSourceBudget_eq_weighted (N : ℕ) :
    primeSourceBudget N = square (Finset.range N) primeSchurWeight factorialPrimeDelta := by
  unfold primeSourceBudget square
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : Nat.Prime (n+3) <;>
    simp [factorialPrimeSourceEnergy, primeSchurWeight, factorialPrimeDelta,
      hp, div_eq_mul_inv, mul_comm]

theorem primeErrorBudget_eq_weighted (N : ℕ) :
    primeErrorBudget N = square (Finset.range N) primeSchurWeight factorialPrimeError := by
  unfold primeErrorBudget square
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : Nat.Prime (n+3) <;>
    simp [factorialPrimeErrorEnergy, primeSchurWeight, hp, div_eq_mul_inv, mul_comm]

theorem primeCrossBudget_eq_weighted (N : ℕ) :
    primeCrossBudget N = product (Finset.range N) primeSchurWeight
      factorialPrimeDelta factorialPrimeError := by
  unfold primeCrossBudget product
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : Nat.Prime (n+3) <;>
    simp [factorialPrimeCrossEnergy, primeSchurWeight, hp, div_eq_mul_inv, mul_comm, mul_assoc]

theorem primeGainBudget_eq_weighted (N : ℕ) :
    primeGainBudget N = square (Finset.range N) primeSchurWeight
      (fun n => schurEta (n+1)) := by
  unfold primeGainBudget square
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : Nat.Prime (n+3) <;>
    simp [factorialPrimeGain, primeSchurWeight, hp, div_eq_mul_inv, mul_comm]

theorem primeSourceBudget_monotone : Monotone primeSourceBudget := by
  apply monotone_nat_of_le_succ
  intro N
  unfold primeSourceBudget
  rw [Finset.sum_range_succ]
  exact le_add_of_nonneg_right (factorialPrimeSourceEnergy_nonneg N)

theorem primeSourceBudget_nonneg (N : ℕ) : 0 ≤ primeSourceBudget N :=
  Finset.sum_nonneg (fun n _ => factorialPrimeSourceEnergy_nonneg n)

theorem primeSourceBudget_pos (N : ℕ) (hN : 0 < N) : 0 < primeSourceBudget N := by
  have h1 : 0 < primeSourceBudget 1 := by
    simpa [primeSourceBudget, factorialPrimeSourceEnergy, factorialPrimeDelta,
      (by decide : Nat.Prime 3)] using
      div_pos (sq_pos_of_pos (factorialPrimeDelta_pos 0)) (schurSigma_pos 1)
  exact h1.trans_le (primeSourceBudget_monotone (by omega : 1 ≤ N))

theorem primeGainBudget_nonneg (N : ℕ) : 0 ≤ primeGainBudget N :=
  Finset.sum_nonneg (fun n _ => factorialPrimeGain_nonneg n)

theorem compositeGainBudget_nonneg (N : ℕ) : 0 ≤ compositeGainBudget N :=
  Finset.sum_nonneg (fun n _ => factorialCompositeGain_nonneg n)

/-- Squared accumulated source--survivor pairing, on the source energy scale. -/
def primeMeanMismatchBudget (N : ℕ) : ℝ :=
  (primeSourceBudget N + primeCrossBudget N)^2 / primeSourceBudget N

/-- The complete centered error square, including every prime row. -/
def primeCancellationVariance (N : ℕ) : ℝ :=
  square (Finset.range N) primeSchurWeight
    (fun n => factorialPrimeError n -
      (primeCrossBudget N / primeSourceBudget N)*factorialPrimeDelta n)

/-- Every ordered pair is retained in this weighted Lagrange determinant. -/
def primePairCancellationBudget (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
    primeSchurWeight i*primeSchurWeight j*
      (factorialPrimeDelta i*factorialPrimeError j -
        factorialPrimeDelta j*factorialPrimeError i)^2

theorem primeMeanMismatchBudget_nonneg (N : ℕ) : 0 ≤ primeMeanMismatchBudget N :=
  div_nonneg (sq_nonneg _) (primeSourceBudget_nonneg N)

theorem primeCancellationVariance_nonneg (N : ℕ) : 0 ≤ primeCancellationVariance N :=
  square_nonneg _ _ _ (fun n _ => primeSchurWeight_nonneg n)

theorem primePairCancellationBudget_eq (N : ℕ) :
    primePairCancellationBudget N =
      2*(primeSourceBudget N*primeErrorBudget N-(primeCrossBudget N)^2) := by
  unfold primePairCancellationBudget
  rw [pair_identity, ← primeSourceBudget_eq_weighted, ← primeErrorBudget_eq_weighted,
    ← primeCrossBudget_eq_weighted]


theorem primeCrossBudget_sq_le (N : ℕ) :
    (primeCrossBudget N)^2 ≤ primeSourceBudget N*primeErrorBudget N := by
  rw [primeCrossBudget_eq_weighted, primeSourceBudget_eq_weighted,
    primeErrorBudget_eq_weighted]
  exact gram_nonneg _ _ _ _ (fun n _ => primeSchurWeight_nonneg n)

theorem primeCancellationVariance_eq_pair_budget (N : ℕ) (hN : 0 < N) :
    primeCancellationVariance N = primePairCancellationBudget N / (2*primeSourceBudget N) := by
  have hu : square (Finset.range N) primeSchurWeight factorialPrimeDelta ≠ 0 := by
    rw [← primeSourceBudget_eq_weighted]
    exact ne_of_gt (primeSourceBudget_pos N hN)
  unfold primeCancellationVariance
  rw [primeSourceBudget_eq_weighted, primeCrossBudget_eq_weighted,
    centered_square_eq _ _ _ _ hu, ← primeSourceBudget_eq_weighted,
    ← primeErrorBudget_eq_weighted, ← primeCrossBudget_eq_weighted,
    primePairCancellationBudget_eq]
  ring

/-- Exact mean/variance split of the complete signed capacity budget.
No cross term, nonprime gain, physical tail or initial capacity is dropped. -/
theorem capacity_eq_prime_alignment_budget (N : ℕ) (hN : 0 < N) :
    tailCapacity (N+1) = tailCapacity 1 + primeMeanMismatchBudget N +
      primeCancellationVariance N + compositeGainBudget N := by
  have hu : square (Finset.range N) primeSchurWeight factorialPrimeDelta ≠ 0 := by
    rw [← primeSourceBudget_eq_weighted]
    exact ne_of_gt (primeSourceBudget_pos N hN)
  have he := completed_square (Finset.range N) primeSchurWeight
    factorialPrimeDelta factorialPrimeError hu
  rw [← primeSourceBudget_eq_weighted, ← primeErrorBudget_eq_weighted,
    ← primeCrossBudget_eq_weighted] at he
  change primeSourceBudget N + primeErrorBudget N + 2*primeCrossBudget N =
    primeMeanMismatchBudget N + primeCancellationVariance N at he
  rw [capacity_eq_prime_composite_budget, primeGainBudget_eq_signed, he]
  ring

/-- The remaining exact provider, now expressed as three nonnegative channels. -/
theorem tailCapacity_tendsto_iff_prime_alignment_unbounded :
    Tendsto tailCapacity atTop atTop ↔
      ∀ B : ℝ, ∃ N : ℕ, 0 < N ∧
        B < primeMeanMismatchBudget N + primeCancellationVariance N + compositeGainBudget N := by
  constructor
  · intro ht B
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      ((tendsto_atTop.mp ht) (B+tailCapacity 1+1))
    have hh := hN (N+2) (by omega)
    rw [show N+2 = (N+1)+1 by omega, capacity_eq_prime_alignment_budget (N+1) (by omega)] at hh
    exact ⟨N+1, by omega, by linarith⟩
  · intro h
    apply tendsto_atTop.mpr
    intro B
    obtain ⟨N, hN, hh⟩ := h (B-tailCapacity 1)
    have hC : B ≤ tailCapacity (N+1) := by
      rw [capacity_eq_prime_alignment_budget N hN]
      linarith
    exact eventually_atTop.mpr ⟨N+1, fun n hn =>
      hC.trans (tailCapacity_monotone hn)⟩

/-- Exact accumulated mixed pairing with the actual survivor. -/
theorem prime_source_add_cross_eq_survivor (N : ℕ) :
    primeSourceBudget N + primeCrossBudget N =
      product (Finset.range N) primeSchurWeight factorialPrimeDelta
        (fun n => schurEta (n+1)) := by
  unfold primeSourceBudget primeCrossBudget product
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : Nat.Prime (n+3)
  · simp only [factorialPrimeSourceEnergy, factorialPrimeCrossEnergy,
      primeSchurWeight, if_pos hp]
    rw [factorialPrimeError_decomposition n hp]
    unfold factorialPrimeDelta
    ring
  · simp [factorialPrimeSourceEnergy, factorialPrimeCrossEnergy, primeSchurWeight, hp]

/-- The full signed CRT row pairing. These are screened innovations, so the
negative-entry formula for raw tail atoms cannot replace this expression. -/
theorem prime_source_add_cross_eq_screened_rows (N : ℕ) :
    primeSourceBudget N + primeCrossBudget N =
      ∑ n ∈ Finset.range N, primeSchurWeight n*factorialPrimeDelta n*
        (factorialPrimeDelta n +
          inner ℝ (tailInnovation (n+1)) (infiniteCoprimeCertificate (Nat.factorial 2)) +
          ∑ j ∈ Finset.range n, factorialPrimeCrossGram n j) := by
  rw [primeSourceBudget_eq_weighted, primeCrossBudget_eq_weighted]
  unfold square product
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [factorialPrimeError_eq_base_add_crossGram]
  ring

/-- The full prime survivor energy is summable under bounded capacity. -/
theorem factorialPrimeGain_summable_of_capacity_bounded
    (h : ∃ B : ℝ, ∀ n : ℕ, tailCapacity n ≤ B) :
    Summable factorialPrimeGain := by
  by_contra hs
  have ht := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    factorialPrimeGain_nonneg).mp hs
  obtain ⟨B, hB⟩ := h
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_atTop.mp ht) (B+1))
  have hh : B+1 ≤ primeGainBudget N := hN N le_rfl
  linarith [primeGainBudget_le_capacity N, hB (N+1)]

/-- Summable prime survivor energy forces the mean mismatch to vanish on
the source-fluctuation scale; a global Cauchy bound alone would give only O(1). -/
theorem primeMeanMismatchBudget_tendsto_of_gain_summable
    (hg : Summable factorialPrimeGain) :
    Tendsto primeMeanMismatchBudget atTop (𝓝 0) := by
  have hb : Summable (fun n => primeSchurWeight n*(schurEta (n+1))^2) := by
    apply hg.congr
    intro n
    by_cases hp : Nat.Prime (n+3) <;>
      simp [factorialPrimeGain, primeSchurWeight, hp, div_eq_mul_inv, mul_comm]
  have ha : Tendsto (fun N => square (Finset.range N) primeSchurWeight factorialPrimeDelta)
      atTop atTop := by
    simpa only [← primeSourceBudget_eq_weighted] using primeSourceBudget_tendsto
  have he := normalized_product_tendsto_zero primeSchurWeight factorialPrimeDelta
    (fun n => schurEta (n+1)) primeSchurWeight_nonneg hb ha
  change Tendsto (fun N => (primeSourceBudget N+primeCrossBudget N)^2/primeSourceBudget N)
    atTop (𝓝 0)
  simpa only [← prime_source_add_cross_eq_survivor, ← primeSourceBudget_eq_weighted] using he

theorem primeMeanMismatchBudget_tendsto_of_capacity_bounded
    (h : ∃ B : ℝ, ∀ n : ℕ, tailCapacity n ≤ B) :
    Tendsto primeMeanMismatchBudget atTop (𝓝 0) :=
  primeMeanMismatchBudget_tendsto_of_gain_summable
    (factorialPrimeGain_summable_of_capacity_bounded h)

theorem primeMeanMismatchBudget_tendsto_of_not_RH
    (hRH : ¬ RiemannHypothesis) :
    Tendsto primeMeanMismatchBudget atTop (𝓝 0) := by
  have hg := (summable_nat_add_iff 1).mpr (schurGain_summable_of_not_RH hRH)
  have hp : Summable factorialPrimeGain :=
    Summable.of_nonneg_of_le factorialPrimeGain_nonneg
      (fun n => by
        unfold factorialPrimeGain
        split_ifs
        · exact le_rfl
        · exact div_nonneg (sq_nonneg _) (schurSigma_pos _).le) hg
  exact primeMeanMismatchBudget_tendsto_of_gain_summable hp

/-- CONDITIONAL RESEARCH REDUCTION. The nonvanishing arithmetic provider
is weaker than a fixed fraction of U and remains OPEN. -/
theorem riemannHypothesis_of_prime_mean_mismatch_not_tendsto
    (h : ¬ Tendsto primeMeanMismatchBudget atTop (𝓝 0)) :
    RiemannHypothesis := by
  by_contra hRH
  exact h (primeMeanMismatchBudget_tendsto_of_not_RH hRH)

/-- CONDITIONAL RESEARCH REDUCTION: a fixed positive mismatch at cofinally
many stages suffices. No such lower bound is proved here. -/
theorem riemannHypothesis_of_prime_mean_mismatch_cofinal
    (ε : ℝ) (hε : 0 < ε)
    (h : ∀ N₀ : ℕ, ∃ N ≥ N₀, ε ≤ primeMeanMismatchBudget N) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_prime_mean_mismatch_not_tendsto
  intro ht
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((tendsto_order.mp ht).2 ε hε)
  obtain ⟨N, hN, hh⟩ := h N₀
  linarith [hN₀ N hN]

/-- Direct first-site provider from incompatibility with every bounded capacity. -/
theorem tailCapacity_tendsto_of_prime_mean_mismatch_not_tendsto
    (h : ¬ Tendsto primeMeanMismatchBudget atTop (𝓝 0)) :
    Tendsto tailCapacity atTop atTop := by
  apply tailCapacity_tendsto_iff_prime_budget_unbounded.mpr
  intro B
  by_contra hb
  have hB : ∀ N : ℕ, primeSourceBudget N + primeSignedBudget N ≤ B := by
    intro N
    exact le_of_not_gt (fun hn => hb ⟨N, hn⟩)
  have hc : ∀ n : ℕ, tailCapacity n ≤ tailCapacity 1+B := by
    intro n
    have hh : tailCapacity (n+1) ≤ tailCapacity 1+B := by
      rw [capacity_eq_prime_signed_budget]
      linarith [hB n]
    exact (tailCapacity_monotone (Nat.le_succ n)).trans hh
  exact h (primeMeanMismatchBudget_tendsto_of_capacity_bounded ⟨_, hc⟩)

/-- A fluctuation-scale arithmetic lower bound supplies the first-site provider;
the hypothesis is explicitly OPEN. -/
theorem tailCapacity_tendsto_of_prime_mean_mismatch_cofinal
    (ε : ℝ) (hε : 0 < ε)
    (h : ∀ N₀ : ℕ, ∃ N ≥ N₀, ε ≤ primeMeanMismatchBudget N) :
    Tendsto tailCapacity atTop atTop := by
  apply tailCapacity_tendsto_of_prime_mean_mismatch_not_tendsto
  intro ht
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((tendsto_order.mp ht).2 ε hε)
  obtain ⟨N, hN, hh⟩ := h N₀
  linarith [hN₀ N hN]

/-- Error/source norm mismatch on the source-fluctuation scale. -/
def primeErrorMismatchBudget (N : ℕ) : ℝ :=
  (primeErrorBudget N-primeSourceBudget N)^2 / primeSourceBudget N

theorem primeErrorMismatchBudget_nonneg (N : ℕ) : 0 ≤ primeErrorMismatchBudget N :=
  div_nonneg (sq_nonneg _) (primeSourceBudget_nonneg N)

/-- Exact square completion behind the fluctuation-scale error bound. -/
theorem primeErrorMismatchBudget_completion (N : ℕ) :
    primeErrorMismatchBudget N +
      (primeGainBudget N+2*(primeSourceBudget N+primeCrossBudget N))^2/primeSourceBudget N =
        2*(primeGainBudget N)^2/primeSourceBudget N + 8*primeMeanMismatchBudget N := by
  unfold primeErrorMismatchBudget primeMeanMismatchBudget
  rw [primeGainBudget_eq_signed]
  ring

/-- Only the explicit nonnegative completion square from the previous
equality is discarded in this upper bound. -/
theorem primeErrorMismatchBudget_le (N : ℕ) :
    primeErrorMismatchBudget N ≤
      2*(primeGainBudget N)^2 / primeSourceBudget N + 8*primeMeanMismatchBudget N := by
  have hs : 0 ≤
      (primeGainBudget N+2*(primeSourceBudget N+primeCrossBudget N))^2/primeSourceBudget N :=
    div_nonneg (sq_nonneg _) (primeSourceBudget_nonneg N)
  linarith [primeErrorMismatchBudget_completion N]

/-- Bounded survivor energy forces V-U=o(sqrt U), not merely V/U→1. -/
theorem primeErrorMismatchBudget_tendsto_of_gain_summable
    (hg : Summable factorialPrimeGain) :
    Tendsto primeErrorMismatchBudget atTop (𝓝 0) := by
  have hG : Tendsto primeGainBudget atTop (𝓝 (∑' n, factorialPrimeGain n)) :=
    hg.hasSum.tendsto_sum_nat
  have hU := tendsto_inv_atTop_zero.comp primeSourceBudget_tendsto
  have hhead : Tendsto (fun N => 2*(primeGainBudget N)^2/primeSourceBudget N)
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using ((hG.pow 2).const_mul 2).mul hU
  have hm := primeMeanMismatchBudget_tendsto_of_gain_summable hg
  have hu : Tendsto
      (fun N => 2*(primeGainBudget N)^2/primeSourceBudget N+8*primeMeanMismatchBudget N)
      atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add] using hhead.add (hm.const_mul 8)
  exact squeeze_zero primeErrorMismatchBudget_nonneg primeErrorMismatchBudget_le hu

theorem primeErrorMismatchBudget_tendsto_of_capacity_bounded
    (h : ∃ B : ℝ, ∀ n : ℕ, tailCapacity n ≤ B) :
    Tendsto primeErrorMismatchBudget atTop (𝓝 0) :=
  primeErrorMismatchBudget_tendsto_of_gain_summable
    (factorialPrimeGain_summable_of_capacity_bounded h)

/-- CONDITIONAL RESEARCH REDUCTION: a nonvanishing error/source mismatch
on the square-root source scale is an OPEN arithmetic hypothesis. -/
theorem tailCapacity_tendsto_of_prime_error_mismatch_cofinal
    (ε : ℝ) (hε : 0 < ε)
    (h : ∀ N₀ : ℕ, ∃ N ≥ N₀, ε ≤ primeErrorMismatchBudget N) :
    Tendsto tailCapacity atTop atTop := by
  apply tailCapacity_tendsto_iff_prime_budget_unbounded.mpr
  intro B
  by_contra hb
  have hB : ∀ N : ℕ, primeSourceBudget N+primeSignedBudget N ≤ B := by
    intro N
    exact le_of_not_gt (fun hn => hb ⟨N, hn⟩)
  have hc : ∀ n : ℕ, tailCapacity n ≤ tailCapacity 1+B := by
    intro n
    have hh : tailCapacity (n+1) ≤ tailCapacity 1+B := by
      rw [capacity_eq_prime_signed_budget]
      linarith [hB n]
    exact (tailCapacity_monotone (Nat.le_succ n)).trans hh
  have ht := primeErrorMismatchBudget_tendsto_of_capacity_bounded ⟨_, hc⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp ((tendsto_order.mp ht).2 ε hε)
  obtain ⟨N, hN, hh⟩ := h N₀
  linarith [hN₀ N hN]

/-- RH endpoint for the explicit fluctuation-scale error/source provider. -/
theorem riemannHypothesis_of_prime_error_mismatch_cofinal
    (ε : ℝ) (hε : 0 < ε)
    (h : ∀ N₀ : ℕ, ∃ N ≥ N₀, ε ≤ primeErrorMismatchBudget N) :
    RiemannHypothesis :=
  riemannHypothesis_of_tailCapacity_tendsto
    (tailCapacity_tendsto_of_prime_error_mismatch_cofinal ε hε h)

/-- CONDITIONAL RESEARCH REDUCTION. A cofinal error saving of c*sqrt U
suffices, even though its relative fraction tends to zero. The arithmetic
saving is not proved by the exact CRT identities. -/
theorem tailCapacity_tendsto_of_prime_error_sqrt_gap
    (c : ℝ) (hc : 0 < c)
    (h : ∀ N₀ : ℕ, ∃ N ≥ N₀,
      primeErrorBudget N ≤ primeSourceBudget N-c*Real.sqrt (primeSourceBudget N)) :
    Tendsto tailCapacity atTop atTop := by
  apply tailCapacity_tendsto_of_prime_error_mismatch_cofinal (c^2) (sq_pos_of_pos hc)
  intro N₀
  obtain ⟨N, hN, hh⟩ := h (max N₀ 1)
  refine ⟨N, (le_max_left _ _).trans hN, ?_⟩
  have hNp : 0 < N := by omega
  have hu := primeSourceBudget_pos N hNp
  have hsave : c*Real.sqrt (primeSourceBudget N) ≤
      primeSourceBudget N-primeErrorBudget N := by linarith
  have hs := pow_le_pow_left₀
    (mul_nonneg hc.le (Real.sqrt_nonneg _)) hsave 2
  rw [mul_pow, Real.sq_sqrt (primeSourceBudget_nonneg N)] at hs
  unfold primeErrorMismatchBudget
  apply (le_div_iff₀ hu).mpr
  nlinarith

/-- RH endpoint; the cofinal square-root saving remains an explicit hypothesis. -/
theorem riemannHypothesis_of_prime_error_sqrt_gap
    (c : ℝ) (hc : 0 < c)
    (h : ∀ N₀ : ℕ, ∃ N ≥ N₀,
      primeErrorBudget N ≤ primeSourceBudget N-c*Real.sqrt (primeSourceBudget N)) :
    RiemannHypothesis :=
  riemannHypothesis_of_tailCapacity_tendsto
    (tailCapacity_tendsto_of_prime_error_sqrt_gap c hc h)


/-- A fixed additive constant can also be retained in the square-root saving.
The cofinal arithmetic hypothesis is OPEN. -/
theorem tailCapacity_tendsto_of_prime_error_sqrt_gap_additive
    (c K : ℝ) (hc : 0 < c)
    (h : ∀ N₀ : ℕ, ∃ N ≥ N₀,
      primeErrorBudget N ≤ primeSourceBudget N-c*Real.sqrt (primeSourceBudget N)+K) :
    Tendsto tailCapacity atTop atTop := by
  have hr : Tendsto (fun N => Real.sqrt (primeSourceBudget N)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp primeSourceBudget_tendsto
  obtain ⟨M, hM⟩ := eventually_atTop.mp ((tendsto_atTop.mp hr) (2*K/c))
  apply tailCapacity_tendsto_of_prime_error_sqrt_gap (c/2) (by linarith)
  intro N₀
  obtain ⟨N, hN, hh⟩ := h (max N₀ M)
  refine ⟨N, (le_max_left _ _).trans hN, ?_⟩
  have hMN : M ≤ N := (le_max_right _ _).trans hN
  have hs := (div_le_iff₀ hc).mp (hM N hMN)
  nlinarith

/-- RH endpoint with the fixed additive constant retained. -/
theorem riemannHypothesis_of_prime_error_sqrt_gap_additive
    (c K : ℝ) (hc : 0 < c)
    (h : ∀ N₀ : ℕ, ∃ N ≥ N₀,
      primeErrorBudget N ≤ primeSourceBudget N-c*Real.sqrt (primeSourceBudget N)+K) :
    RiemannHypothesis :=
  riemannHypothesis_of_tailCapacity_tendsto
    (tailCapacity_tendsto_of_prime_error_sqrt_gap_additive c K hc h)

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
