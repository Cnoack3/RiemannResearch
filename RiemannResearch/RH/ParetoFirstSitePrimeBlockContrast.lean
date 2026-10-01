/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoFirstSitePrimeBlocks

/-!
# Source-balanced prime-block tests and pooled mean separation

Source: the user's 2026-09-30 angular-increment continuation, developed by
finite weighted orthogonal projection and exact regression square completion.
This supports the statements and proof strategy; no arithmetic novelty or
unconditional divergence is asserted.

Tests use every complete signed screened factorial/CRT row. Source projection
removes the fitted source component algebraically. The full block equality
retains its contrast remainder and historical running-slope drift. Pooled
two-subblock separation gives a finite many-row determinant lower bound.
The dyadic capacity equality also retains initial capacity, mean mismatch and
every nonprime gain. All growth hypotheses remain explicit and Open.
No Burnol, PNT, asymptotic rate, independence, or RH-strength provider is imported.
-/

noncomputable section
open Filter
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.WeightedScalarEnergy
open RiemannResearch.RH.Pareto.IntegerDPP

/-- Source projection of an arbitrary local test; every Schur weight is retained. -/
def primeBlockBalancedTest (N k : ℕ) (f : ℕ → ℝ) (i : ℕ) : ℝ :=
  f i - (product (Finset.range k) (fun q => primeSchurWeight (N+q))
    (fun q => factorialPrimeDelta (N+q)) f / primeBlockSource N k) *
      factorialPrimeDelta (N+i)
/-- Squared norm of the source-balanced test. -/
def primeBlockContrastEnergy (N k : ℕ) (f : ℕ → ℝ) : ℝ :=
  square (Finset.range k) (fun i => primeSchurWeight (N+i))
    (primeBlockBalancedTest N k f)
/-- Signed pairing with the complete screened factorial error. -/
def primeBlockContrastPairing (N k : ℕ) (f : ℕ → ℝ) : ℝ :=
  product (Finset.range k) (fun i => primeSchurWeight (N+i))
    (primeBlockBalancedTest N k f) (fun i => factorialPrimeError (N+i))
/-- All-row finite lower certificate; it is zero when the test norm is zero. -/
def primeBlockContrastCertificate (N k : ℕ) (f : ℕ → ℝ) : ℝ :=
  (primeBlockContrastPairing N k f)^2 / primeBlockContrastEnergy N k f
/-- Complete regression remainder after testing the block's centered error. -/
def primeBlockContrastRemainder (N k : ℕ) (f : ℕ → ℝ) : ℝ :=
  square (Finset.range k) (fun i => primeSchurWeight (N+i))
    (fun i => factorialPrimeError (N+i) -
      (primeBlockCross N k / primeBlockSource N k) * factorialPrimeDelta (N+i) -
      (primeBlockContrastPairing N k f / primeBlockContrastEnergy N k f) *
        primeBlockBalancedTest N k f i)

theorem primeBlockBalancedTest_source_zero (N k : ℕ) (f : ℕ → ℝ) :
    product (Finset.range k) (fun i => primeSchurWeight (N+i))
      (fun i => factorialPrimeDelta (N+i)) (primeBlockBalancedTest N k f) = 0 :=
  centered_product_zero _ _ _ _ (fun i _ => primeSchurWeight_nonneg (N+i))

theorem primeBlockVariance_eq_contrast_add_remainder (N k : ℕ) (f : ℕ → ℝ) :
    primeBlockVariance N k =
      primeBlockContrastCertificate N k f + primeBlockContrastRemainder N k f := by
  exact balanced_contrast_completion _ _ _ _ _
    (primeBlockCross N k / primeBlockSource N k)
    (primeBlockBalancedTest_source_zero N k f)

theorem primeBlockContrastCertificate_nonneg (N k : ℕ) (f : ℕ → ℝ) :
    0 ≤ primeBlockContrastCertificate N k f :=
  div_nonneg (sq_nonneg _) (square_nonneg _ _ _
    (fun i _ => primeSchurWeight_nonneg (N+i)))

theorem primeBlockContrastRemainder_nonneg (N k : ℕ) (f : ℕ → ℝ) :
    0 ≤ primeBlockContrastRemainder N k f :=
  square_nonneg _ _ _ (fun i _ => primeSchurWeight_nonneg (N+i))

theorem primeBlockContrastCertificate_le_variance (N k : ℕ) (f : ℕ → ℝ) :
    primeBlockContrastCertificate N k f ≤ primeBlockVariance N k := by
  rw [primeBlockVariance_eq_contrast_add_remainder N k f]
  exact le_add_of_nonneg_right (primeBlockContrastRemainder_nonneg N k f)

/-- Exact full angular accounting, preserving the historical head--block
slope drift as well as the contrast remainder. -/
theorem primeAngularBlock_eq_contrast_remainder_drift (N k : ℕ)
    (hN : 0 < N) (f : ℕ → ℝ) :
    primeAngularBlock N k = primeBlockContrastCertificate N k f +
      primeBlockContrastRemainder N k f + primeBlockMeanDrift N k := by
  rw [primeAngularBlock_eq_variance_add_drift N k hN,
    primeBlockVariance_eq_contrast_add_remainder N k f]

theorem primeBlockContrastCertificate_le_angular (N k : ℕ)
    (hN : 0 < N) (f : ℕ → ℝ) :
    primeBlockContrastCertificate N k f ≤ primeAngularBlock N k :=
  (primeBlockContrastCertificate_le_variance N k f).trans
    (primeBlockVariance_le_angular N k hN)

theorem primeBlockContrastPairing_eq_screened_rows (N k : ℕ) (f : ℕ → ℝ) :
    primeBlockContrastPairing N k f =
      ∑ i ∈ Finset.range k,
        primeSchurWeight (N+i) * primeBlockBalancedTest N k f i *
          (inner ℝ (tailInnovation (N+i+1))
            (infiniteCoprimeCertificate (Nat.factorial 2)) +
            ∑ j ∈ Finset.range (N+i), factorialPrimeCrossGram (N+i) j) := by
  unfold primeBlockContrastPairing product
  simp_rw [factorialPrimeError_eq_base_add_crossGram]

theorem primeBlockContrastPairing_eq_survivor (N k : ℕ) (f : ℕ → ℝ) :
    primeBlockContrastPairing N k f =
      product (Finset.range k) (fun i => primeSchurWeight (N+i))
        (primeBlockBalancedTest N k f) (fun i => schurEta (N+i+1)) := by
  have hca : product (Finset.range k) (fun i => primeSchurWeight (N+i))
      (primeBlockBalancedTest N k f) (fun i => factorialPrimeDelta (N+i)) = 0 := by
    simpa only [product, mul_comm, mul_left_comm, mul_assoc] using
      primeBlockBalancedTest_source_zero N k f
  have he : primeBlockContrastPairing N k f =
      product (Finset.range k) (fun i => primeSchurWeight (N+i))
        (primeBlockBalancedTest N k f)
        (fun i => schurEta (N+i+1) - factorialPrimeDelta (N+i)) := by
    unfold primeBlockContrastPairing product
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only
    by_cases hp : Nat.Prime (N+i+3)
    · have hh : schurEta (N+i+1) =
          factorialPrimeDelta (N+i) + factorialPrimeError (N+i) := by
        simpa only [factorialPrimeDelta] using factorialPrimeError_decomposition (N+i) hp
      rw [hh]
      ring
    · simp [primeSchurWeight, hp]
  rw [he]
  have hp := product_sub_right (Finset.range k) (fun i => primeSchurWeight (N+i))
    (primeBlockBalancedTest N k f) (fun i => schurEta (N+i+1))
    (fun i => factorialPrimeDelta (N+i)) 1
  simpa only [one_mul, hca, sub_zero] using hp

/-- Exact capacity accounting for arbitrary dyadic tests, retaining initial
capacity, the running mean mismatch, every contrast square and nonprime gain. -/
theorem capacity_eq_dyadic_prime_contrast_budget (J : ℕ) (f : ℕ → ℕ → ℝ) :
    tailCapacity (2^J+1) = tailCapacity 1 + primeMeanMismatchBudget (2^J) +
      (∑ j ∈ Finset.range J, primeBlockContrastCertificate (2^j) (2^j) (f j)) +
      (∑ j ∈ Finset.range J, primeBlockContrastRemainder (2^j) (2^j) (f j)) +
      (∑ j ∈ Finset.range J, primeBlockMeanDrift (2^j) (2^j)) +
      compositeGainBudget (2^J) := by
  rw [capacity_eq_dyadic_prime_block_budget]
  have he : (∑ j ∈ Finset.range J, primeBlockVariance (2^j) (2^j)) =
      (∑ j ∈ Finset.range J, primeBlockContrastCertificate (2^j) (2^j) (f j)) +
      ∑ j ∈ Finset.range J, primeBlockContrastRemainder (2^j) (2^j) (f j) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ =>
      primeBlockVariance_eq_contrast_add_remainder (2^j) (2^j) (f j))
  rw [he]
  ring


/-- The contrast bound is attained by the actual centered error, including
empty-source and zero-variance blocks. This does not supply any growth. -/
theorem primeBlockContrastCertificate_eq_variance_at_error (N k : ℕ) :
    primeBlockContrastCertificate N k (fun i => factorialPrimeError (N+i)) =
      primeBlockVariance N k := by
  let f := fun i => factorialPrimeError (N+i)
  let c := primeBlockBalancedTest N k f
  have hca : product (Finset.range k) (fun i => primeSchurWeight (N+i))
      c (fun i => factorialPrimeDelta (N+i)) = 0 := by
    simpa only [product, mul_comm, mul_left_comm, mul_assoc] using
      primeBlockBalancedTest_source_zero N k f
  have he : primeBlockContrastEnergy N k f = primeBlockVariance N k := rfl
  have hl : primeBlockContrastPairing N k f = primeBlockContrastEnergy N k f := by
    have hp := product_sub_right (Finset.range k) (fun i => primeSchurWeight (N+i))
      c f (fun i => factorialPrimeDelta (N+i)) (primeBlockCross N k / primeBlockSource N k)
    rw [hca, mul_zero, sub_zero] at hp
    have hcc : product (Finset.range k) (fun i => primeSchurWeight (N+i)) c c =
        square (Finset.range k) (fun i => primeSchurWeight (N+i)) c := by
      unfold product square
      apply Finset.sum_congr rfl
      intro i hi
      ring
    change product (Finset.range k) (fun i => primeSchurWeight (N+i)) c f =
      square (Finset.range k) (fun i => primeSchurWeight (N+i)) c
    rw [← hcc]
    exact hp.symm
  change (primeBlockContrastPairing N k f)^2 / primeBlockContrastEnergy N k f = _
  rw [hl, he]
  by_cases h : primeBlockVariance N k = 0
  · simp [h]
  · field_simp [h]

/-- CONDITIONAL RESEARCH REDUCTION: growth of the actual contrast energies is
the explicit Open arithmetic provider. No analytic rate is imported. -/
theorem riemannHypothesis_of_dyadic_prime_contrast (f : ℕ → ℕ → ℝ)
    (hdiv : ¬ Summable (fun j =>
      primeBlockContrastCertificate (2^j) (2^j) (f j))) : RiemannHypothesis :=
  riemannHypothesis_of_dyadic_prime_block_lower_bound _
    (fun j => primeBlockContrastCertificate_nonneg (2^j) (2^j) (f j)) hdiv
    (fun j => primeBlockContrastCertificate_le_variance (2^j) (2^j) (f j))


/-- Fully weighted mean separation of two consecutive subblocks. -/
def primeBlockSplitDrift (N k l : ℕ) : ℝ :=
  primeBlockSource N k * primeBlockSource (N+k) l /
    (primeBlockSource N k + primeBlockSource (N+k) l) *
    (primeBlockCross (N+k) l / primeBlockSource (N+k) l -
      primeBlockCross N k / primeBlockSource N k)^2

theorem primeBlockSplitDrift_nonneg (N k l : ℕ) :
    0 ≤ primeBlockSplitDrift N k l := by
  unfold primeBlockSplitDrift
  exact mul_nonneg
    (div_nonneg (mul_nonneg (primeBlockSource_nonneg _ _) (primeBlockSource_nonneg _ _))
      (add_nonneg (primeBlockSource_nonneg _ _) (primeBlockSource_nonneg _ _)))
    (sq_nonneg _)

/-- Exact two-subblock scatter decomposition; both child squares are retained. -/
theorem primeBlockVariance_split (N k l : ℕ)
    (hk : 0 < primeBlockSource N k) (hl : 0 < primeBlockSource (N+k) l) :
    primeBlockVariance N (k+l) = primeBlockVariance N k +
      primeBlockVariance (N+k) l + primeBlockSplitDrift N k l := by
  have hs : primeBlockSource N (k+l) =
      primeBlockSource N k + primeBlockSource (N+k) l := by
    simp only [primeBlockSource, square, Finset.sum_range_add, Nat.add_assoc]
  have hv : primeBlockError N (k+l) =
      primeBlockError N k + primeBlockError (N+k) l := by
    simp only [primeBlockError, square, Finset.sum_range_add, Nat.add_assoc]
  have hx : primeBlockCross N (k+l) =
      primeBlockCross N k + primeBlockCross (N+k) l := by
    simp only [primeBlockCross, product, Finset.sum_range_add, Nat.add_assoc]
  rw [primeBlockVariance_eq_quotient, primeBlockVariance_eq_quotient,
    primeBlockVariance_eq_quotient, hs, hv, hx]
  exact centered_energy_merge _ _ _ _ _ _ (ne_of_gt hk) (ne_of_gt hl)
    (ne_of_gt (add_pos hk hl))

theorem primeAngularBlock_eq_split_scatter_drift (N k l : ℕ)
    (hN : 0 < N) (hk : 0 < primeBlockSource N k)
    (hl : 0 < primeBlockSource (N+k) l) :
    primeAngularBlock N (k+l) = primeBlockVariance N k +
      primeBlockVariance (N+k) l + primeBlockSplitDrift N k l +
      primeBlockMeanDrift N (k+l) := by
  rw [primeAngularBlock_eq_variance_add_drift _ _ hN,
    primeBlockVariance_split _ _ _ hk hl]

theorem primeBlockSplitDrift_le_angular (N k l : ℕ)
    (hN : 0 < N) (hk : 0 < primeBlockSource N k)
    (hl : 0 < primeBlockSource (N+k) l) :
    primeBlockSplitDrift N k l ≤ primeAngularBlock N (k+l) := by
  rw [primeAngularBlock_eq_split_scatter_drift _ _ _ hN hk hl]
  linarith [primeBlockVariance_nonneg N k, primeBlockVariance_nonneg (N+k) l,
    primeBlockMeanDrift_nonneg N (k+l)]

/-- All rates are finite explicit hypotheses; no PNT or signed gap is supplied. -/
theorem primeAngularBlock_ge_split_gap (N k l : ℕ) (hN : 0 < N)
    (v : ℝ) (hv : 0 ≤ v)
    (hk : v ≤ primeBlockSource N k) (hl : v ≤ primeBlockSource (N+k) l) :
    (v/2) *
      (primeBlockCross (N+k) l / primeBlockSource (N+k) l -
        primeBlockCross N k / primeBlockSource N k)^2 ≤ primeAngularBlock N (k+l) := by
  by_cases hz : v = 0
  · simp only [hz, zero_div, zero_mul]
    unfold primeAngularBlock
    exact Finset.sum_nonneg (fun i _ => primeAngularInnovation_nonneg (N+i))
  have hvpos : 0 < v := lt_of_le_of_ne hv (Ne.symm hz)
  have hred := reduced_weight_lower (primeBlockSource (N+k) l)
    (primeBlockSource N k) v (hvpos.trans_le hk) (primeBlockSource_nonneg _ _) hk hl
  have hm := mul_le_mul_of_nonneg_right hred
    (sq_nonneg (primeBlockCross (N+k) l / primeBlockSource (N+k) l -
      primeBlockCross N k / primeBlockSource N k))
  have hle := primeBlockSplitDrift_le_angular N k l hN (hvpos.trans_le hk) (hvpos.trans_le hl)
  unfold primeBlockSplitDrift at hle
  rw [mul_comm (primeBlockSource (N+k) l) (primeBlockSource N k)] at hm
  exact hm.trans hle

/-- CONDITIONAL RESEARCH REDUCTION: lower source rates and the signed pooled
mean separation must be established for the actual screened arithmetic. -/
theorem riemannHypothesis_of_dyadic_split_gap (v d : ℕ → ℝ)
    (hv : ∀ j, 0 ≤ v j)
    (hleft : ∀ j, v j ≤ primeBlockSource (2^(j+1)) (2^j))
    (hright : ∀ j, v j ≤ primeBlockSource (2^(j+1)+2^j) (2^j))
    (hgap : ∀ j, (d j)^2 ≤
      (primeBlockCross (2^(j+1)+2^j) (2^j) /
          primeBlockSource (2^(j+1)+2^j) (2^j) -
        primeBlockCross (2^(j+1)) (2^j) / primeBlockSource (2^(j+1)) (2^j))^2)
    (hdiv : ¬ Summable (fun j => (v j/2)*(d j)^2)) : RiemannHypothesis := by
  apply riemannHypothesis_of_primeAngularInnovation_not_summable
  intro hs
  have hsum : Summable (fun j => primeAngularBlock (2^(j+1)) (2^(j+1))) := by
    have hb : Summable (fun j => primeAngularBlock (2^j) (2^j)) := by
      obtain ⟨hS, hH⟩ := primeAngularInnovation_summable_iff_dyadic_blocks.mp hs
      have hh := hS.add hH
      apply hh.congr
      intro j
      exact (primeAngularBlock_eq_variance_add_drift _ _ (by positivity)).symm
    exact (summable_nat_add_iff (f := fun j : ℕ => primeAngularBlock (2^j) (2^j)) 1).mpr hb
  apply hdiv
  apply hsum.of_nonneg_of_le
  · intro j
    exact mul_nonneg (div_nonneg (hv j) (by norm_num)) (sq_nonneg _)
  · intro j
    have h := primeAngularBlock_ge_split_gap (2^(j+1)) (2^j) (2^j)
      (by positivity) (v j) (hv j) (hleft j) (hright j)
    have hp : (2:ℕ)^j + 2^j = 2^(j+1) := by rw [pow_succ]; omega
    rw [hp] at h
    exact (mul_le_mul_of_nonneg_left (hgap j)
      (div_nonneg (hv j) (by norm_num))).trans h







end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
