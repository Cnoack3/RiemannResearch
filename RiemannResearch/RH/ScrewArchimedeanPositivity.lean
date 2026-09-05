/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.Analysis.ExponentialKernelGram
import RiemannResearch.RH.ScrewArchimedeanSeries

/-!
# Conditional positivity of the negative archimedean contribution

For every finite set of real points and real coefficients with zero sum,
the negative archimedean screw series has a nonnegative quadratic expression.
The same holds for every infinite tail, by a proved summability interchange
and the exponential Gram integral. The zero-sum hypothesis cancels the constant
part; no arithmetic positivity hypothesis is used.

Source: user-provided RH_Local_to_Global_Trace_Attack_Plan_2026-09-05,
archimedean decomposition and Gram-factorization sections. These finite-node
results do not yet prove the analogous integrated step/L2 statements, and do
not give positivity of the complete signed arithmetic kernel.
-/

namespace RiemannResearch.RH
open scoped BigOperators
open RiemannResearch.Analysis
noncomputable section

theorem neg_archimedeanScrewTerm_finite_nonneg {ι : Type*} [Fintype ι]
    (k : ℕ) (x c : ι → ℝ) (hc : ∑ i, c i = 0) :
    0 ≤ ∑ i, ∑ j, c i * (-archimedeanScrewTerm k (x i-x j)) * c j := by
  have he : (∑ i, ∑ j, c i * (-archimedeanScrewTerm k (x i-x j)) * c j) =
      4*archimedeanWeight k *
        (∑ i, ∑ j, c i * Real.exp (-archimedeanRate k*|x i-x j|) * c j) := by
    have hterm (i j : ι) :
        c i * (-archimedeanScrewTerm k (x i-x j)) * c j =
          4*archimedeanWeight k *
            (c i * Real.exp (-archimedeanRate k*|x i-x j|)*c j - c i*c j) := by
      unfold archimedeanScrewTerm
      ring
    simp_rw [hterm, ← Finset.mul_sum, Finset.sum_sub_distrib]
    simp [← Finset.mul_sum, hc]
  rw [he]
  exact mul_nonneg (mul_nonneg (by norm_num) (archimedeanWeight_nonneg k))
    (exponentialKernel_finite_nonneg (archimedeanRate_pos k) x c)

theorem neg_archimedeanScrewTail_finite_nonneg {ι : Type*} [Fintype ι]
    (J : ℕ) (x c : ι → ℝ) (hc : ∑ i, c i = 0) :
    0 ≤ ∑ i, ∑ j, c i * (-(∑' k : ℕ,
      archimedeanScrewTerm (k+J) (x i-x j))) * c j := by
  have hs (i j : ι) : Summable (fun k : ℕ =>
      c i * (-archimedeanScrewTerm (k+J) (x i-x j)) * c j) :=
    ((((summable_nat_add_iff J).mpr (summable_archimedeanScrewTerm (x i-x j))).neg).mul_left (c i)).mul_right (c j)
  have he : (∑' k : ℕ, ∑ i, ∑ j,
      c i * (-archimedeanScrewTerm (k+J) (x i-x j)) * c j) =
      ∑ i, ∑ j, c i * (-(∑' k : ℕ,
        archimedeanScrewTerm (k+J) (x i-x j))) * c j := by
    rw [Summable.tsum_finsetSum (fun i _ => summable_sum (fun j _ => hs i j))]
    simp_rw [Summable.tsum_finsetSum (fun j _ => hs _ j),
      tsum_mul_right, tsum_mul_left, tsum_neg]
  rw [← he]
  exact tsum_nonneg (fun k => neg_archimedeanScrewTerm_finite_nonneg (k+J) x c hc)

theorem neg_archimedeanScrewSeries_finite_nonneg {ι : Type*} [Fintype ι]
    (x c : ι → ℝ) (hc : ∑ i, c i = 0) :
    0 ≤ ∑ i, ∑ j, c i * (-archimedeanScrewSeries (x i-x j)) * c j := by
  simpa only [archimedeanScrewSeries, Nat.add_zero] using
    neg_archimedeanScrewTail_finite_nonneg 0 x c hc

end
end RiemannResearch.RH
