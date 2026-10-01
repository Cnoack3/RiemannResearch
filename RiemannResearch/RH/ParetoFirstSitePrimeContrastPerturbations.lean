/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoFirstSitePrimeBlockContrast
import RiemannResearch.RH.ParetoCrossGramRowEnergy
import RiemannResearch.Analysis.DyadicWeightedContrast

/-!
# Finite-energy perturbations of actual screened prime contrasts

Source: the user's October 1 audit continuation, the project's checked
fixed-vector Bessel bounds, and exact finite signed square expansion.
These support the statements and proof strategy; no novelty is claimed.

The fixed base and any fixed finite signed column packet preserve contrast
summability for arbitrary cutoff-dependent tests. The exact square equality
retains the signed base cross term. A general signed row transfer requires
its weighted square-summability hypothesis explicitly. Growth of the actual
moving screened CRT contrast remains Open.
-/

noncomputable section
open Filter
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.WeightedScalarEnergy
open RiemannResearch.Analysis.DyadicWeightedContrast
open RiemannResearch.Analysis.OrthogonalPairingEnergy
open RiemannResearch.RH.Pareto.IntegerDPP

/-- Signed contribution of one fixed Hilbert vector to the actual block test. -/
def primeBlockFixedPairing (N k : ℕ) (f : ℕ → ℝ) (z : ThresholdHilbert) : ℝ :=
  product (Finset.range k) (fun i => primeSchurWeight (N+i))
    (primeBlockBalancedTest N k f)
    (fun i => inner ℝ (tailInnovation (N+i+1)) z)

def primeBlockFixedPairingCertificate (N k : ℕ) (f : ℕ → ℝ)
    (z : ThresholdHilbert) : ℝ :=
  (primeBlockFixedPairing N k f z)^2 / primeBlockContrastEnergy N k f

theorem primeBlockFixedPairingCertificate_nonneg (N k : ℕ)
    (f : ℕ → ℝ) (z : ThresholdHilbert) :
    0 ≤ primeBlockFixedPairingCertificate N k f z :=
  div_nonneg (sq_nonneg _) (square_nonneg _ _ _
    (fun i _ => primeSchurWeight_nonneg (N+i)))

/-- Only a finite weighted Gram inequality is used, also at zero test norm. -/
theorem primeBlockFixedPairingCertificate_le_square (N k : ℕ)
    (f : ℕ → ℝ) (z : ThresholdHilbert) :
    primeBlockFixedPairingCertificate N k f z ≤
      square (Finset.range k) (fun i => primeSchurWeight (N+i))
        (fun i => inner ℝ (tailInnovation (N+i+1)) z) := by
  let w := fun i => primeSchurWeight (N+i)
  let c := primeBlockBalancedTest N k f
  let e := fun i => inner ℝ (tailInnovation (N+i+1)) z
  have hw : ∀ i ∈ Finset.range k, 0 ≤ w i :=
    fun i _ => primeSchurWeight_nonneg (N+i)
  change (product (Finset.range k) w c e)^2 /
    square (Finset.range k) w c ≤ square (Finset.range k) w e
  by_cases hE : square (Finset.range k) w c = 0
  · simpa [hE] using square_nonneg (Finset.range k) w e hw
  · have hpos : 0 < square (Finset.range k) w c :=
      lt_of_le_of_ne (square_nonneg _ _ _ hw) (Ne.symm hE)
    apply (div_le_iff₀ hpos).mpr
    simpa only [mul_comm] using gram_nonneg (Finset.range k) w c e hw

theorem primeBlockFixedPairingCertificate_le_rows (N k : ℕ)
    (f : ℕ → ℝ) (z : ThresholdHilbert) :
    primeBlockFixedPairingCertificate N k f z ≤
      ∑ i ∈ Finset.range k,
        (inner ℝ (tailInnovation (N+i+1)) z)^2 / schurSigma (N+i+1) := by
  apply (primeBlockFixedPairingCertificate_le_square N k f z).trans
  unfold square
  apply Finset.sum_le_sum
  intro i hi
  by_cases hp : Nat.Prime (N+i+3)
  · simp [primeSchurWeight, hp, div_eq_mul_inv, mul_comm]
  · simp only [primeSchurWeight, if_neg hp, zero_mul]
    exact div_nonneg (sq_nonneg _) (schurSigma_pos _).le

/-- Tests may vary arbitrarily with the dyadic block. The vector z is fixed. -/
theorem primeBlockFixedPairingCertificate_dyadic_summable
    (f : ℕ → ℕ → ℝ) (z : ThresholdHilbert) :
    Summable (fun j => primeBlockFixedPairingCertificate (2^j) (2^j) (f j) z) := by
  have hs : Summable (fun n =>
      (inner ℝ (tailInnovation (n+1)) z)^2 / schurSigma (n+1)) :=
    (summable_nat_add_iff 1).mpr (tailInnovation_fixed_pairing_energy_summable z)
  have hb := dyadic_block_summable_of_nonneg _
    (fun n => div_nonneg (sq_nonneg _) (schurSigma_pos _).le) hs
  exact Summable.of_nonneg_of_le
    (fun j => primeBlockFixedPairingCertificate_nonneg _ _ _ _)
    (fun j => primeBlockFixedPairingCertificate_le_rows _ _ _ _) hb

/-- Exact certificate after subtracting a fixed-vector signed contribution. -/
def primeBlockAdjustedContrastCertificate (N k : ℕ) (f : ℕ → ℝ)
    (z : ThresholdHilbert) : ℝ :=
  (primeBlockContrastPairing N k f - primeBlockFixedPairing N k f z)^2 /
    primeBlockContrastEnergy N k f

/-- Fixed-vector corrections preserve summability. No growing column packet
or block-dependent vector is covered by this statement. -/
theorem primeBlockAdjustedContrastCertificate_dyadic_summable_iff
    (f : ℕ → ℕ → ℝ) (z : ThresholdHilbert) :
    Summable (fun j => primeBlockAdjustedContrastCertificate (2^j) (2^j) (f j) z) ↔
      Summable (fun j => primeBlockContrastCertificate (2^j) (2^j) (f j)) := by
  have hb : Summable (fun j =>
      (-(primeBlockFixedPairing (2^j) (2^j) (f j) z))^2 /
        primeBlockContrastEnergy (2^j) (2^j) (f j)) := by
    simpa only [neg_sq, primeBlockFixedPairingCertificate] using primeBlockFixedPairingCertificate_dyadic_summable f z
  exact weighted_square_add_summable_iff
    (fun j => primeBlockContrastPairing (2^j) (2^j) (f j))
    (fun j => -(primeBlockFixedPairing (2^j) (2^j) (f j) z))
    (fun j => primeBlockContrastEnergy (2^j) (2^j) (f j))
    (fun j => square_nonneg _ _ _ (fun i _ => primeSchurWeight_nonneg (2^j+i))) hb

/-- All changing earlier screened CRT columns, with the fixed base separated. -/
def primeBlockMovingCRTContrastPairing (N k : ℕ) (f : ℕ → ℝ) : ℝ :=
  product (Finset.range k) (fun i => primeSchurWeight (N+i))
    (primeBlockBalancedTest N k f)
    (fun i => ∑ m ∈ Finset.range (N+i), factorialPrimeCrossGram (N+i) m)

/-- Complete signed equality precedes the summability comparison. -/
theorem primeBlockMovingCRTContrastPairing_eq_sub_base (N k : ℕ) (f : ℕ → ℝ) :
    primeBlockMovingCRTContrastPairing N k f =
      primeBlockContrastPairing N k f -
        primeBlockFixedPairing N k f (infiniteCoprimeCertificate (Nat.factorial 2)) := by
  unfold primeBlockMovingCRTContrastPairing primeBlockContrastPairing primeBlockFixedPairing product
  simp_rw [factorialPrimeError_eq_base_add_crossGram]
  simp only [mul_add, Finset.sum_add_distrib]
  ring

def primeBlockMovingCRTContrastCertificate (N k : ℕ) (f : ℕ → ℝ) : ℝ :=
  (primeBlockMovingCRTContrastPairing N k f)^2 / primeBlockContrastEnergy N k f

/-- The fixed base can be removed at the summability level for arbitrary tests. -/
theorem primeBlockMovingCRTContrastCertificate_dyadic_summable_iff
    (f : ℕ → ℕ → ℝ) :
    Summable (fun j => primeBlockMovingCRTContrastCertificate (2^j) (2^j) (f j)) ↔
      Summable (fun j => primeBlockContrastCertificate (2^j) (2^j) (f j)) := by
  have he (N k : ℕ) (g : ℕ → ℝ) :
      primeBlockMovingCRTContrastCertificate N k g =
        primeBlockAdjustedContrastCertificate N k g
          (infiniteCoprimeCertificate (Nat.factorial 2)) := by
    unfold primeBlockMovingCRTContrastCertificate primeBlockAdjustedContrastCertificate
    rw [primeBlockMovingCRTContrastPairing_eq_sub_base]
  simp_rw [he]
  exact primeBlockAdjustedContrastCertificate_dyadic_summable_iff f
    (infiniteCoprimeCertificate (Nat.factorial 2))

/-- Exact square accounting: the signed base cross term remains present. -/
theorem primeBlockContrastCertificate_eq_movingCRT_split (N k : ℕ) (f : ℕ → ℝ) :
    primeBlockContrastCertificate N k f =
      primeBlockMovingCRTContrastCertificate N k f +
      2 * primeBlockMovingCRTContrastPairing N k f *
        primeBlockFixedPairing N k f (infiniteCoprimeCertificate (Nat.factorial 2)) /
        primeBlockContrastEnergy N k f +
      primeBlockFixedPairingCertificate N k f
        (infiniteCoprimeCertificate (Nat.factorial 2)) := by
  have he := primeBlockMovingCRTContrastPairing_eq_sub_base N k f
  have hp : primeBlockContrastPairing N k f =
      primeBlockMovingCRTContrastPairing N k f +
        primeBlockFixedPairing N k f (infiniteCoprimeCertificate (Nat.factorial 2)) := by
    linarith
  unfold primeBlockContrastCertificate primeBlockMovingCRTContrastCertificate
    primeBlockFixedPairingCertificate
  rw [hp]
  ring

/-- A fixed finite signed column packet is one fixed Hilbert vector. -/
theorem primeBlockFixedPairing_eq_finite_columns (N k : ℕ) (f : ℕ → ℝ)
    (s : Finset ℕ) (a : ℕ → ℝ) :
    primeBlockFixedPairing N k f (∑ m ∈ s, a m • factorialPrimeRefinement m) =
      product (Finset.range k) (fun i => primeSchurWeight (N+i))
        (primeBlockBalancedTest N k f)
        (fun i => ∑ m ∈ s, a m * factorialPrimeCrossGram (N+i) m) := by
  unfold primeBlockFixedPairing
  simp only [inner_sum, inner_smul_right, factorialPrimeCrossGram]

/-- Removing any fixed finite signed column packet preserves actual dyadic
contrast summability, even when the tests depend on the cutoff. -/
theorem primeBlockContrast_finite_columns_dyadic_summable_iff
    (f : ℕ → ℕ → ℝ) (s : Finset ℕ) (a : ℕ → ℝ) :
    Summable (fun j =>
      (primeBlockContrastPairing (2^j) (2^j) (f j) -
        product (Finset.range (2^j)) (fun i => primeSchurWeight (2^j+i))
          (primeBlockBalancedTest (2^j) (2^j) (f j))
          (fun i => ∑ m ∈ s, a m * factorialPrimeCrossGram (2^j+i) m))^2 /
          primeBlockContrastEnergy (2^j) (2^j) (f j)) ↔
      Summable (fun j => primeBlockContrastCertificate (2^j) (2^j) (f j)) := by
  simpa only [primeBlockAdjustedContrastCertificate, primeBlockFixedPairing_eq_finite_columns] using
    primeBlockAdjustedContrastCertificate_dyadic_summable_iff f
      (∑ m ∈ s, a m • factorialPrimeRefinement m)

/-- Signed square-summable row corrections preserve the actual contrast
summability target. Arithmetic providers of he must be proved separately. -/
theorem primeBlockContrast_row_perturbation_dyadic_summable_iff
    (f : ℕ → ℕ → ℝ) (e : ℕ → ℝ)
    (he : Summable (fun n => primeSchurWeight n * (e n)^2)) :
    Summable (fun j =>
      (primeBlockContrastPairing (2^j) (2^j) (f j) -
        product (Finset.range (2^j)) (fun i => primeSchurWeight (2^j+i))
          (primeBlockBalancedTest (2^j) (2^j) (f j))
          (fun i => e (2^j+i)))^2 /
          primeBlockContrastEnergy (2^j) (2^j) (f j)) ↔
      Summable (fun j => primeBlockContrastCertificate (2^j) (2^j) (f j)) := by
  have hb := dyadic_pairing_energy_summable primeSchurWeight e
    (fun j => primeBlockBalancedTest (2^j) (2^j) (f j))
    primeSchurWeight_nonneg he
  have hh := weighted_square_add_summable_iff
    (fun j => primeBlockContrastPairing (2^j) (2^j) (f j) -
      product (Finset.range (2^j)) (fun i => primeSchurWeight (2^j+i))
        (primeBlockBalancedTest (2^j) (2^j) (f j)) (fun i => e (2^j+i)))
    (fun j => product (Finset.range (2^j)) (fun i => primeSchurWeight (2^j+i))
      (primeBlockBalancedTest (2^j) (2^j) (f j)) (fun i => e (2^j+i)))
    (fun j => primeBlockContrastEnergy (2^j) (2^j) (f j))
    (fun j => square_nonneg _ _ _ (fun i _ => primeSchurWeight_nonneg (2^j+i))) hb
  simpa only [sub_add_cancel, primeBlockContrastCertificate] using hh.symm

/-- CONDITIONAL RESEARCH REDUCTION. Nonsummability of the actual moving
screened CRT contribution is still Open; the fixed base is no longer a provider. -/
theorem riemannHypothesis_of_movingCRTContrast_not_summable
    (f : ℕ → ℕ → ℝ)
    (hdiv : ¬ Summable (fun j =>
      primeBlockMovingCRTContrastCertificate (2^j) (2^j) (f j))) : RiemannHypothesis := by
  apply riemannHypothesis_of_dyadic_prime_contrast f
  intro hs
  exact hdiv ((primeBlockMovingCRTContrastCertificate_dyadic_summable_iff f).mpr hs)

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
