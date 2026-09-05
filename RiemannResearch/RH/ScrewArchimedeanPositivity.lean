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
archimedean decomposition and Gram-factorization sections. The integrated
theorems below prove the actual infinite-tail interchange, dyadic positivity,
and an explicit L1 remainder bound. The support-based L2 refinement and
positivity of the complete signed arithmetic kernel remain separate
obligations.
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

/-- Exact removal of the constant part of one negative archimedean summand
on a dyadic mean-zero step. This identity is kept separate from the subsequent
positivity argument. -/
theorem neg_archimedeanScrewTerm_dyadic_integral_eq
    {R : ℝ} (hR : 0 ≤ R) (m k : ℕ)
    (c : FiniteDyadicHaarIndex m → ℝ) :
    (∫ x, dyadicHaarStep R m c x *
      (∫ y, (-archimedeanScrewTerm k (x - y)) *
        dyadicHaarStep R m c y)) =
      4 * archimedeanWeight k *
        (∫ x, dyadicHaarStep R m c x *
          (∫ y, Real.exp (-archimedeanRate k * |x - y|) *
            dyadicHaarStep R m c y)) := by
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
  simpa only [A, e, u, mul_assoc, mul_left_comm, mul_comm] using hout

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

/-- Absolute convergence justifies exchanging an arbitrary archimedean tail
with the actual double integral of every integrable real test. The proof is on
the product space and records the summable L1 majorant needed by Fubini. -/
theorem neg_archimedeanScrewTail_integral_eq_tsum
    (J : ℕ) (u : ℝ → ℝ) (hu : Integrable u) :
    (∫ x, u x * (∫ y, (-archimedeanScrewTail J (x - y)) * u y)) =
      ∑' k : ℕ, ∫ x, u x *
        (∫ y, (-archimedeanScrewTerm (k + J) (x - y)) * u y) := by
  let F : ℕ → ℝ × ℝ → ℝ := fun k p =>
    u p.1 * (-archimedeanScrewTerm (k + J) (p.1 - p.2)) * u p.2
  let T : ℝ × ℝ → ℝ := fun p =>
    u p.1 * (-archimedeanScrewTail J (p.1 - p.2)) * u p.2
  let L : ℝ := (∫ x, ‖u x‖) ^ 2
  have hbase : Integrable (fun p : ℝ × ℝ => u p.1 * u p.2)
      (volume.prod volume) := hu.mul_prod hu
  have hnormbase : Integrable (fun p : ℝ × ℝ => ‖u p.1‖ * ‖u p.2‖)
      (volume.prod volume) := hu.norm.mul_prod hu.norm
  have hF (k : ℕ) : Integrable (F k) (volume.prod volume) := by
    have hm : AEStronglyMeasurable
        (fun p : ℝ × ℝ => -archimedeanScrewTerm (k + J) (p.1 - p.2))
        (volume.prod volume) := by
      exact ((continuous_archimedeanScrewTerm (k + J)).neg.comp
        (continuous_fst.sub continuous_snd)).measurable.aestronglyMeasurable
    have hb : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume),
        ‖-archimedeanScrewTerm (k + J) (p.1 - p.2)‖ ≤
          4 * archimedeanWeight (k + J) := by
      filter_upwards with p
      simpa only [norm_neg] using
        norm_archimedeanScrewTerm_le (k + J) (p.1 - p.2)
    have h := hbase.mul_bdd hm hb
    simpa only [F, mul_assoc, mul_left_comm, mul_comm] using h
  have hnorm_le (k : ℕ) :
      (∫ p : ℝ × ℝ, ‖F k p‖ ∂(volume.prod volume)) ≤
        4 * archimedeanWeight (k + J) * L := by
    have hmajor : Integrable (fun p : ℝ × ℝ =>
        (4 * archimedeanWeight (k + J)) * (‖u p.1‖ * ‖u p.2‖))
        (volume.prod volume) :=
      hnormbase.const_mul (4 * archimedeanWeight (k + J))
    calc
      (∫ p : ℝ × ℝ, ‖F k p‖ ∂(volume.prod volume)) ≤
          ∫ p : ℝ × ℝ,
            (4 * archimedeanWeight (k + J)) * (‖u p.1‖ * ‖u p.2‖)
              ∂(volume.prod volume) := by
        apply integral_mono (hF k).norm hmajor
        intro p
        simp only [F, Real.norm_eq_abs, abs_mul, abs_neg]
        have ht := norm_archimedeanScrewTerm_le (k + J) (p.1 - p.2)
        rw [Real.norm_eq_abs] at ht
        convert mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left ht (abs_nonneg (u p.1)))
          (abs_nonneg (u p.2)) using 1
        all_goals ring
      _ = 4 * archimedeanWeight (k + J) * L := by
        rw [integral_const_mul]
        have hp := integral_prod_mul (μ := volume) (ν := volume)
          (fun x : ℝ => ‖u x‖) (fun y : ℝ => ‖u y‖)
        rw [hp]
        simp only [L]
        ring
  have hnormsum : Summable (fun k : ℕ =>
      ∫ p : ℝ × ℝ, ‖F k p‖ ∂(volume.prod volume)) := by
    apply Summable.of_nonneg_of_le
    · intro k
      exact integral_nonneg (fun _ => norm_nonneg _)
    · exact hnorm_le
    · have hw := ((summable_nat_add_iff J).mpr summable_archimedeanWeight)
          |>.mul_left (4 * L)
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hw
  have hT : Integrable T (volume.prod volume) := by
    have hm : AEStronglyMeasurable
        (fun p : ℝ × ℝ => -archimedeanScrewTail J (p.1 - p.2))
        (volume.prod volume) := by
      exact ((continuous_archimedeanScrewTail J).neg.comp
        (continuous_fst.sub continuous_snd)).measurable.aestronglyMeasurable
    have hb : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume),
        ‖-archimedeanScrewTail J (p.1 - p.2)‖ ≤
          4 * archimedeanTailMajorant J := by
      filter_upwards with p
      rw [norm_neg, Real.norm_eq_abs,
        abs_of_nonneg (archimedeanScrewTail_bounds J (p.1 - p.2)).1]
      exact (archimedeanScrewTail_bounds J (p.1 - p.2)).2
    have h := hbase.mul_bdd hm hb
    simpa only [T, mul_assoc, mul_left_comm, mul_comm] using h
  have hpoint (p : ℝ × ℝ) : (∑' k : ℕ, F k p) = T p := by
    simp only [F, T, archimedeanScrewTail]
    rw [tsum_mul_right, tsum_mul_left, tsum_neg]
  have hsumprod :
      (∫ p : ℝ × ℝ, ∑' k : ℕ, F k p ∂(volume.prod volume)) =
        ∑' k : ℕ, ∫ p : ℝ × ℝ, F k p ∂(volume.prod volume) := by
    exact (integral_tsum_of_summable_integral_norm hF hnormsum).symm
  have htailprod :
      (∫ x, u x * (∫ y, (-archimedeanScrewTail J (x - y)) * u y)) =
        ∫ p : ℝ × ℝ, T p ∂(volume.prod volume) := by
    have hinner (x : ℝ) :
        (∫ y, u x * (-archimedeanScrewTail J (x - y)) * u y) =
          u x * (∫ y, (-archimedeanScrewTail J (x - y)) * u y) := by
      have h := integral_const_mul (μ := volume) (u x)
        (fun y => (-archimedeanScrewTail J (x - y)) * u y)
      simpa only [mul_assoc] using h
    rw [integral_prod T hT]
    change (∫ x, u x * (∫ y, (-archimedeanScrewTail J (x-y))*u y)) =
      ∫ x, ∫ y, u x * (-archimedeanScrewTail J (x-y))*u y
    congr 1
    funext x
    exact (hinner x).symm
  have htermprod (k : ℕ) :
      (∫ p : ℝ × ℝ, F k p ∂(volume.prod volume)) =
        ∫ x, u x *
          (∫ y, (-archimedeanScrewTerm (k + J) (x - y)) * u y) := by
    have hinner (x : ℝ) :
        (∫ y, u x * (-archimedeanScrewTerm (k + J) (x - y)) * u y) =
          u x * (∫ y, (-archimedeanScrewTerm (k + J) (x - y)) * u y) := by
      have h := integral_const_mul (μ := volume) (u x)
        (fun y => (-archimedeanScrewTerm (k + J) (x - y)) * u y)
      simpa only [mul_assoc] using h
    rw [integral_prod (F k) (hF k)]
    change (∫ x, ∫ y, u x * (-archimedeanScrewTerm (k+J) (x-y))*u y) =
      ∫ x, u x * (∫ y, (-archimedeanScrewTerm (k+J) (x-y))*u y)
    congr 1
    funext x
    exact hinner x
  calc
    (∫ x, u x * (∫ y, (-archimedeanScrewTail J (x - y)) * u y)) =
        ∫ p : ℝ × ℝ, T p ∂(volume.prod volume) := htailprod
    _ = ∫ p : ℝ × ℝ, ∑' k : ℕ, F k p ∂(volume.prod volume) := by
      congr 1
      funext p
      exact (hpoint p).symm
    _ = ∑' k : ℕ, ∫ p : ℝ × ℝ, F k p ∂(volume.prod volume) := hsumprod
    _ = ∑' k : ℕ, ∫ x, u x *
        (∫ y, (-archimedeanScrewTerm (k + J) (x - y)) * u y) := by
      congr 1
      funext k
      exact htermprod k

/-- The absolute size of an integrated archimedean tail is controlled by its
explicit tail majorant and the square of the test's L1 norm. -/
theorem norm_neg_archimedeanScrewTail_integral_le_l1_sq
    (J : ℕ) (u : ℝ → ℝ) (hu : Integrable u) :
    ‖∫ x, u x * (∫ y, (-archimedeanScrewTail J (x - y)) * u y)‖ ≤
      4 * archimedeanTailMajorant J * (∫ x, ‖u x‖) ^ 2 := by
  let C : ℝ := 4 * archimedeanTailMajorant J
  let I : ℝ := ∫ x, ‖u x‖
  have hinner (x : ℝ) :
      ‖∫ y, (-archimedeanScrewTail J (x - y)) * u y‖ ≤ C * I := by
    have hmajor : Integrable (fun y => C * ‖u y‖) := hu.norm.const_mul C
    calc
      ‖∫ y, (-archimedeanScrewTail J (x - y)) * u y‖ ≤
          ∫ y, C * ‖u y‖ := by
        apply norm_integral_le_of_norm_le hmajor
        filter_upwards with y
        rw [norm_mul, norm_neg]
        have ht := archimedeanScrewTail_bounds J (x - y)
        rw [Real.norm_eq_abs, abs_of_nonneg ht.1]
        exact mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
      _ = C * I := by rw [integral_const_mul]
  have hmajor : Integrable (fun x => (C * I) * ‖u x‖) :=
    hu.norm.const_mul (C * I)
  calc
    ‖∫ x, u x * (∫ y, (-archimedeanScrewTail J (x - y)) * u y)‖ ≤
        ∫ x, (C * I) * ‖u x‖ := by
      apply norm_integral_le_of_norm_le hmajor
      filter_upwards with x
      rw [norm_mul]
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left (hinner x) (norm_nonneg (u x))
    _ = C * I ^ 2 := by
      rw [integral_const_mul]
      unfold I
      ring
    _ = _ := rfl

/-- The integrated negative archimedean tail is nonnegative on every dyadic
Haar step, and its size has an explicit L1 remainder bound. This controls only
the archimedean exponential tail, not the complete signed Weil form. -/
theorem neg_archimedeanScrewTail_dyadic_integral_bounds_l1
    {R : ℝ} (hR : 0 ≤ R) (m J : ℕ)
    (c : FiniteDyadicHaarIndex m → ℝ) :
    0 ≤ ∫ x, dyadicHaarStep R m c x *
        (∫ y, (-archimedeanScrewTail J (x - y)) *
          dyadicHaarStep R m c y) ∧
      (∫ x, dyadicHaarStep R m c x *
        (∫ y, (-archimedeanScrewTail J (x - y)) *
          dyadicHaarStep R m c y)) ≤
        4 * archimedeanTailMajorant J *
          (∫ x, ‖dyadicHaarStep R m c x‖) ^ 2 := by
  let u := dyadicHaarStep R m c
  have hu : Integrable u := by
    simpa only [u, mul_one] using
      integrable_dyadicHaarStep_mul_continuous
        R m c (fun _ => (1 : ℝ)) continuous_const
  have hnonneg :
      0 ≤ ∫ x, u x * (∫ y, (-archimedeanScrewTail J (x - y)) * u y) := by
    rw [neg_archimedeanScrewTail_integral_eq_tsum J u hu]
    exact tsum_nonneg (fun k =>
      neg_archimedeanScrewTerm_dyadic_integral_nonneg hR m (k + J) c)
  constructor
  · exact hnonneg
  · have hbound :=
      norm_neg_archimedeanScrewTail_integral_le_l1_sq J u hu
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg] at hbound
    exact hbound

end
end RiemannResearch.RH
