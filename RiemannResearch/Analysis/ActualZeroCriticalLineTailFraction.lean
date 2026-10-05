/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroBadTailDensity
import RiemannResearch.Analysis.ActualZeroTailReflection
import RiemannResearch.RH.WeilExplicitFormula.Final
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
This transfers the already
vendored unconditional two-thirds critical-line result to the actual strict
horizontal tails. It supplies a uniform constant fraction, not exponential
zero-density decay. Source: Alpöge--Furman, arXiv:2608.13637v2, and the imported
Zeta23.thmA₀_cumulative. All multiplicities and the full original normalizer
remain present.
-/

noncomputable section
open Zeta23 Filter
open scoped BigOperators

namespace RiemannResearch.Analysis.ActualZeroOrdinate

theorem onLineCount_eq_realSum (T : ℝ) :
    (N0 0 T : ℝ) =
      realSum T (fun ρ => if ρ.re = 1 / 2 then 1 else 0) := by
  classical
  have hfin : (zerosIn 0 T ∩ {ρ : ℂ | ρ.re = 1 / 2}).Finite :=
    (zerosIn_finite 0 T).subset Set.inter_subset_left
  have hfilter : (cutoff T).filter (fun ρ => ρ.re = 1 / 2) = hfin.toFinset := by
    ext ρ
    simp [cutoff]
  rw [N0, finsum_mem_eq_finite_toFinset_sum _ hfin, Nat.cast_sum]
  unfold realSum
  rw [← hfilter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ρ hρ
  norm_num only [one_div] at *
  split_ifs <;> simp_all

/-- Exact complete-copy partition into on-line and off-line zeros. -/
theorem strictTail_zero_add_onLineCount (T : ℝ) :
    strictTail T 0 + (N0 0 T : ℝ) = (Ncount 0 T : ℝ) := by
  rw [strictTail_eq_realSum, onLineCount_eq_realSum, ← realSum_add]
  have heq : (fun ρ : ℂ =>
      (if 0 < |ρ.re - 1 / 2| then (1 : ℝ) else 0) +
        (if ρ.re = 1 / 2 then 1 else 0)) = (fun _ => 1) := by
    funext ρ
    by_cases h : ρ.re = 1 / 2
    · simp [h]
    · have hp : 0 < |ρ.re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr h)
      simp only [if_pos hp, if_neg h, add_zero]
  rw [heq, realSum_one]

theorem strictTail_le_zero (T δ : ℝ) (hδ : 0 ≤ δ) :
    strictTail T δ ≤ strictTail T 0 := by
  rw [strictTail_eq_realSum, strictTail_eq_realSum]
  apply realSum_mono
  intro ρ hρ
  by_cases h : δ < |ρ.re - 1 / 2|
  · have hp : 0 < |ρ.re - 1 / 2| := lt_of_le_of_lt hδ h
    simp only [if_pos h, if_pos hp, le_refl]
  · simp only [if_neg h]
    split_ifs <;> norm_num

/-- Genuine unconditional uniform bad fraction from the existing critical-line
provider; it does not assert the stronger Ingham exponential density decay. -/
theorem eventually_strictTail_le_third (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ δ : ℝ, 0 ≤ δ →
      strictTail T δ ≤ (1 / 3 + ε) * (Ncount 0 T : ℝ) := by
  obtain ⟨T₀, hT₀⟩ := thmA₀_cumulative ε hε
  filter_upwards [eventually_ge_atTop T₀] with T hT
  intro δ hδ
  have hs : (N0star 0 T : ℝ) ≤ (N0 0 T : ℝ) := by
    exact_mod_cast (trivial_chain₀ 0 T).2.1
  have hline := (hT₀ T hT).trans hs
  have hpartition := strictTail_zero_add_onLineCount T
  have htail := strictTail_le_zero T δ hδ
  nlinarith

theorem eventually_normalized_strictTail_le_third (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ δ : ℝ, 0 ≤ δ →
      strictTail T δ / (Ncount 0 T : ℝ) ≤ 1 / 3 + ε := by
  filter_upwards [eventually_strictTail_le_third ε hε] with T hT
  intro δ hδ
  by_cases hN : (Ncount 0 T : ℝ) = 0
  · rw [hN, div_zero]
    positivity
  · have hN0 : 0 < (Ncount 0 T : ℝ) :=
      lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hN)
    apply (div_le_iff₀ hN0).mpr
    simpa only [mul_comm] using hT δ hδ

theorem eventually_rightStrictTail_le_sixth (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ δ : ℝ, 0 ≤ δ →
      rightStrictTail T δ ≤ (1 / 6 + ε / 2) * (Ncount 0 T : ℝ) := by
  filter_upwards [eventually_strictTail_le_third ε hε] with T hT
  intro δ hδ
  have h := hT δ hδ
  rw [strictTail_eq_twice_right T δ hδ] at h
  linarith

/-- Preserve the strict mask before applying the strip endpoint bound. -/
theorem badCoshSum_le_strictTail (T δ ell : ℝ) (hell : 0 ≤ ell) :
    badWeightedSum T δ (fun t => Real.cosh (ell * t) - 1) ≤
      (Real.cosh (ell / 2) - 1) * strictTail T δ := by
  classical
  unfold badWeightedSum strictTail FiniteStrictTail.badSum FiniteStrictTail.tail
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c hc
  by_cases hbad : δ < copyDisplacement T c
  · rw [if_pos hbad, if_pos hbad, mul_one]
    apply sub_le_sub_right
    apply Real.cosh_le_cosh.mpr
    have hx0 : 0 ≤ copyDisplacement T c := abs_nonneg _
    have hx : copyDisplacement T c ≤ 1 / 2 :=
      (displacement_lt_half c.1.2).le
    rw [abs_of_nonneg (mul_nonneg hell hx0),
      abs_of_nonneg (div_nonneg hell (by norm_num))]
    nlinarith [mul_le_mul_of_nonneg_left hx hell]
  · rw [if_neg hbad, if_neg hbad, mul_zero]

end RiemannResearch.Analysis.ActualZeroOrdinate

namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open ActualZeroOrdinate

/-- Unconditional eventual factor 1/3 in the actual bad-operator strip bound.
The event is independent of the integer support size and of the good cutoff.
This does not close the growing-support Ingham density provider. -/
theorem eventually_badCorrection_norm_le_third (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ d : ℕ, 1 ≤ d → ∀ δ : ℝ, 0 ≤ δ →
      ‖badCorrection T d δ‖ ≤
        ((d : ℝ) / 2) * (Real.cosh (Real.log (d : ℝ) / 2) - 1) * (1 / 3 + ε) := by
  filter_upwards [eventually_normalized_strictTail_le_third ε hε] with T hT
  intro d hd δ hδ
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hlog : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hdR
  have hC : 0 ≤ Real.cosh (Real.log (d : ℝ) / 2) - 1 :=
    sub_nonneg.mpr (Real.one_le_cosh _)
  calc
    _ ≤ (d : ℝ) / (2 * (Ncount 0 T : ℝ)) *
        badWeightedSum T δ (fun t => Real.cosh (Real.log (d : ℝ) * t) - 1) :=
      badCorrection_norm_le_badWeightedSum T d hd δ
    _ ≤ (d : ℝ) / (2 * (Ncount 0 T : ℝ)) *
        ((Real.cosh (Real.log (d : ℝ) / 2) - 1) * strictTail T δ) :=
      mul_le_mul_of_nonneg_left
        (badCoshSum_le_strictTail T δ (Real.log (d : ℝ)) hlog) (by positivity)
    _ = ((d : ℝ) / 2) * (Real.cosh (Real.log (d : ℝ) / 2) - 1) *
        (strictTail T δ / (Ncount 0 T : ℝ)) := by
      simp only [div_eq_mul_inv, mul_inv]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hT δ hδ) (by positivity)

end RiemannResearch.Analysis.ActualZeroPhaseMoments
