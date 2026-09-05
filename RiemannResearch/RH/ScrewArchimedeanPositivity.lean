/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.Analysis.ExponentialKernelGram
import RiemannResearch.RH.FiniteDyadicCellKernel
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
The individual-term dyadic theorem below is a later integrated extension;
interchange of the full series or an infinite tail with the double integral
remains open.
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
    ((((summable_nat_add_iff J).mpr
      (summable_archimedeanScrewTerm (x i-x j))).neg).mul_left (c i)).mul_right (c j)
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

open RiemannResearch.RH.PrimeGapCurvature
open MeasureTheory

/-- The actual integrated quadratic form of each negative archimedean
summand is nonnegative on every dyadic Haar step. The mean-zero identity removes
the constant part before the exponential Gram theorem supplies the sign. -/
theorem neg_archimedeanScrewTerm_dyadic_integral_nonneg
    {R : ℝ} (hR : 0 ≤ R) (m k : ℕ)
    (c : FiniteDyadicHaarIndex m → ℝ) :
    0 ≤ ∫ x, dyadicHaarStep R m c x *
      (∫ y, (-archimedeanScrewTerm k (x - y)) *
        dyadicHaarStep R m c y) := by
  let u := dyadicHaarStep R m c
  let A : ℝ := 4 * archimedeanWeight k
  let e : ℝ → ℝ → ℝ :=
    fun x y => Real.exp (-archimedeanRate k * |x - y|)
  have hecont : Continuous (Function.uncurry e) := by
    unfold e
    fun_prop
  have hgauge := finiteCellKernel_gauge_invariant
    (dyadicCellLeft R m) (dyadicCellRight R m)
    ((finiteDyadicHaarMatrix m).mulVec c) (dyadicCell_ordered hR m)
    (fun x y => A * e x y) (continuous_const.mul hecont)
    (fun _ => -A) (fun _ => 0) continuous_const
    (dyadicHaarStep_integral_zero hR m c)
  have hkernel (x y : ℝ) :
      A * e x y + -A + 0 = -archimedeanScrewTerm k (x - y) := by
    unfold A e archimedeanScrewTerm
    ring
  have heq :
      (∫ x, u x * (∫ y, (-archimedeanScrewTerm k (x - y)) * u y)) =
        A * (∫ x, u x * (∫ y, e x y * u y)) := by
    have hg : (∫ x, u x *
        (∫ y, (A * e x y + -A + 0) * u y)) =
        ∫ x, u x * (∫ y, A * e x y * u y) := by
      simpa only [u, dyadicHaarStep] using hgauge
    simp_rw [hkernel] at hg
    rw [hg]
    have hinner (x : ℝ) :
        (∫ y, A * e x y * u y) = A * (∫ y, e x y * u y) := by
      have h := integral_const_mul (μ := volume) A (fun y => e x y * u y)
      simpa only [mul_assoc] using h
    simp_rw [hinner]
    have hout := integral_const_mul (μ := volume) A
      (fun x => u x * (∫ y, e x y * u y))
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hout
  rw [heq]
  apply mul_nonneg
  · exact mul_nonneg (by norm_num) (archimedeanWeight_nonneg k)
  · unfold e u
    exact dyadicHaarStep_exponentialKernel_integral_nonneg
      (archimedeanRate_pos k) R m c

end
end RiemannResearch.RH
