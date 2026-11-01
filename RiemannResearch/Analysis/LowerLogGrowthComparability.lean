/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.LowerLogGrowth
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

/-!
# Invariance of zero lower logarithmic growth under comparable energies

Source: the user's 1 November 2026 P/Q change-of-measure question.
These statements are general order and logarithm facts; actual arithmetic
energy comparability is supplied by the consuming application.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.Analysis.SubpolynomialWindow

/-- A fixed multiplicative upper bound transfers zero lower logarithmic growth.
The comparison is only required eventually. -/
theorem lowerLogGrowth_eq_zero_of_eventually_le_mul
    (E F H : ℕ → ℝ) (C : ℝ)
    (hH : Tendsto H atTop atTop)
    (hE : ∀ n, 0 ≤ E n) (hF : ∀ n, 0 ≤ F n)
    (hEF : ∀ᶠ n in atTop, E n ≤ C * F n)
    (hzero : lowerLogGrowth F H = 0) :
    lowerLogGrowth E H = 0 := by
  let K : ℝ := max 1 C
  have hK1 : 1 ≤ K := le_max_left _ _
  have hCK : C ≤ K := le_max_right _ _
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  have hlog : Tendsto (fun n => Real.log (H n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hH
  have hconst : Tendsto (fun n => Real.log K / Real.log (H n))
      atTop (𝓝 0) := hlog.const_div_atTop _
  apply (lowerLogGrowth_eq_zero_iff E H).mpr
  intro ε hε
  have hsmall := (lowerLogGrowth_eq_zero_iff F H).mp hzero (ε / 2) (half_pos hε)
  have hH1 : ∀ᶠ n in atTop, 1 < H n := hH.eventually (eventually_gt_atTop 1)
  have hconstsmall := hconst.eventually (Iio_mem_nhds (half_pos hε))
  apply (hsmall.and_eventually (hH1.and (hconstsmall.and hEF))).mono
  rintro n ⟨hsn, hHn, hcn, hEn⟩
  have hbound : 1 + E n ≤ K * (1 + F n) := by
    have hmul := mul_le_mul_of_nonneg_right hCK (hF n)
    nlinarith
  have hlogbound := Real.log_le_log (by linarith [hE n] : 0 < 1 + E n) hbound
  rw [Real.log_mul (ne_of_gt hK)
    (ne_of_gt (by linarith [hF n] : 0 < 1 + F n))] at hlogbound
  have hdiv := div_le_div_of_nonneg_right hlogbound (Real.log_pos hHn).le
  rw [add_div] at hdiv
  linarith

/-- Equivalent complete weighted energies have the same zero lower logarithmic
growth criterion. This does not compare unsmoothed and smoothed energies. -/
theorem lowerLogGrowth_eq_zero_iff_of_comparable
    (E F H : ℕ → ℝ) (C D : ℝ)
    (hH : Tendsto H atTop atTop)
    (hE : ∀ n, 0 ≤ E n) (hF : ∀ n, 0 ≤ F n)
    (hEF : ∀ᶠ n in atTop, E n ≤ C * F n)
    (hFE : ∀ᶠ n in atTop, F n ≤ D * E n) :
    lowerLogGrowth E H = 0 ↔ lowerLogGrowth F H = 0 := by
  constructor
  · exact lowerLogGrowth_eq_zero_of_eventually_le_mul F E H D hH hF hE hFE
  · exact lowerLogGrowth_eq_zero_of_eventually_le_mul E F H C hH hE hF hEF


/-- A fixed affine upper bound transfers zero lower logarithmic growth.
The additive constant accounts for the exact head of an energy. -/
theorem lowerLogGrowth_eq_zero_of_eventually_le_add_mul
    (E F H : ℕ → ℝ) (C D : ℝ)
    (hH : Tendsto H atTop atTop)
    (hE : ∀ n, 0 ≤ E n) (hF : ∀ n, 0 ≤ F n)
    (hEF : ∀ᶠ n in atTop, E n ≤ C + D * F n)
    (hzero : lowerLogGrowth F H = 0) :
    lowerLogGrowth E H = 0 := by
  let K : ℝ := max 1 (max (1 + C) D)
  have hK1 : 1 ≤ K := le_max_left _ _
  have hCK : 1 + C ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hDK : D ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  have hlog : Tendsto (fun n => Real.log (H n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hH
  have hconst : Tendsto (fun n => Real.log K / Real.log (H n))
      atTop (𝓝 0) := hlog.const_div_atTop _
  apply (lowerLogGrowth_eq_zero_iff E H).mpr
  intro ε hε
  have hsmall := (lowerLogGrowth_eq_zero_iff F H).mp hzero (ε / 2) (half_pos hε)
  have hH1 : ∀ᶠ n in atTop, 1 < H n := hH.eventually (eventually_gt_atTop 1)
  have hconstsmall := hconst.eventually (Iio_mem_nhds (half_pos hε))
  apply (hsmall.and_eventually (hH1.and (hconstsmall.and hEF))).mono
  rintro n ⟨hsn, hHn, hcn, hEn⟩
  have hbound : 1 + E n ≤ K * (1 + F n) := by
    have hmul := mul_le_mul_of_nonneg_right hDK (hF n)
    nlinarith
  have hlogbound := Real.log_le_log (by linarith [hE n] : 0 < 1 + E n) hbound
  rw [Real.log_mul (ne_of_gt hK)
    (ne_of_gt (by linarith [hF n] : 0 < 1 + F n))] at hlogbound
  have hdiv := div_le_div_of_nonneg_right hlogbound (Real.log_pos hHn).le
  rw [add_div] at hdiv
  linarith
end RiemannResearch.Analysis.SubpolynomialWindow
