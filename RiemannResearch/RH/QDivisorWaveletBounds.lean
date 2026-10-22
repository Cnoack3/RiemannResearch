/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.RH.QPrimeWaveletOverlap
import RiemannResearch.RH.QDivisorWaveletFactorization
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Pointwise Jordan bounds for the Q divisor kernel

Source: user-provided moving-window analysis, Section 5. The exact wavelet
factorization is retained before estimating its arithmetic energy.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.ZetaTwoHilbert
open ZetaTwoProbability
theorem qDivisorWavelet_abs_le_jordan (r : ℕ) (hr : r ≠ 0) (n : ℕ+) :
    |qDivisorWavelet r (n : ℕ)| ≤ qJordanTwo r := by
  rw [qDivisorWavelet_eq_prime_product r hr n, qJordanTwo, if_neg hr, Finset.abs_prod]
  exact Finset.prod_le_prod (fun _ _ => abs_nonneg _)
    (fun p hp => abs_geometricWavelet_le_weight p (r.factorization p)
      (primeValuation p n) (Nat.prime_of_mem_primeFactors hp))
theorem qJordanTwo_le_sq (r : ℕ) (hr : r ≠ 0) : qJordanTwo r ≤ (r : ℝ) ^ 2 := by
  rw [qJordanTwo, if_neg hr]
  calc
    _ ≤ ∏ p ∈ r.primeFactors, ((p : ℝ) ^ (r.factorization p)) ^ 2 :=
      Finset.prod_le_prod (fun p hp =>
        (qValuationWaveletWeight_pos p _ (Nat.prime_of_mem_primeFactors hp)).le)
        (fun p _ => valuationWaveletWeight_le_pow p _)
    _ = (r : ℝ) ^ 2 := by
      rw [Finset.prod_pow]
      congr 1
      exact_mod_cast (Nat.prod_primeFactors_pow_factorization hr).symm
theorem qDivisorWavelet_energy_le_sq (r : ℕ) (hr : r ≠ 0) (n : ℕ+) :
    qDivisorWavelet r (n : ℕ) ^ 2 / qJordanTwo r ≤ (r : ℝ) ^ 2 := by
  have hJ := qJordanTwo_pos r (Nat.pos_of_ne_zero hr)
  have hA := qDivisorWavelet_abs_le_jordan r hr n
  have hsq : qDivisorWavelet r (n : ℕ) ^ 2 ≤ qJordanTwo r ^ 2 := by
    nlinarith [sq_abs (qDivisorWavelet r (n : ℕ)),
      mul_nonneg (sub_nonneg.mpr hA) (add_nonneg hJ.le (abs_nonneg (qDivisorWavelet r (n : ℕ))))]
  calc
    _ ≤ qJordanTwo r := (div_le_iff₀ hJ).mpr (by nlinarith)
    _ ≤ _ := qJordanTwo_le_sq r hr
end RiemannResearch.RH.ZetaTwoHilbert
